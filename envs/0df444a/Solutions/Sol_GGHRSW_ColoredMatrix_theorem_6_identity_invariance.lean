-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.theorem_6_identity_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T04:57:01.432293+00:00
-- url     : https://prove2.me/submissions/42a39b86-c419-4625-9459-5eb5118dabfc

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model
import Definitions.Def_GGHRSW_ColoredMatrix_Simulator
import Theorems.Thm_GGHRSW_ColoredMatrix_consistent_display

open GGHRSW.ColoredMatrix Matrix

namespace GGHRSW.ColoredMatrix.Collision

variable {p : ℕ}

/-! ### Padding records into square matrices -/

/-- Top-left padding of an `a × b` matrix into an `M × M` matrix. -/
def padMat (M : ℕ) {a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod p)) :
    Matrix (Fin M) (Fin M) (ZMod p) :=
  fun i j => if hi : i.val < a then if hj : j.val < b then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

lemma padMat_add {M a b : ℕ} (A B : Matrix (Fin a) (Fin b) (ZMod p)) :
    padMat M (A + B) = padMat M A + padMat M B := by
  ext i j
  simp only [padMat, Matrix.add_apply]
  split_ifs <;> simp

lemma padMat_smul {M a b : ℕ} (c : ZMod p) (A : Matrix (Fin a) (Fin b) (ZMod p)) :
    padMat M (c • A) = c • padMat M A := by
  ext i j
  simp only [padMat, Matrix.smul_apply]
  split_ifs <;> simp

lemma padMat_mul {M a b c : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod p))
    (B : Matrix (Fin b) (Fin c) (ZMod p)) (hb : b ≤ M) :
    padMat M (A * B) = padMat M A * padMat M B := by
  ext i j
  simp only [padMat, Matrix.mul_apply]
  by_cases hi : i.val < a
  · by_cases hj : j.val < c
    · simp only [hi, hj, dite_true]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ
        ((Finset.univ : Finset (Fin b)).map (Fin.castLEEmb hb)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [k.isLt]
      · intro k _ hk
        have : ¬ k.val < b := by
          intro hkb
          apply hk
          simp only [Finset.mem_map, Finset.mem_univ, true_and]
          exact ⟨⟨k.val, hkb⟩, by ext; simp⟩
        simp [this]
    · simp [hi, hj]
  · simp [hi]

lemma padMat_square {M : ℕ} (A : Matrix (Fin M) (Fin M) (ZMod p)) : padMat M A = A := by
  ext i j
  simp [padMat]

/-- Padding of a record. -/
def pad (M : ℕ) (r : Record p) : Matrix (Fin M) (Fin M) (ZMod p) := padMat M r.mat

/-- A default record (never consulted for well-formed expressions). -/
def dflt : Record p := ⟨0, 0, .src, .src, 0⟩

lemma pad_add {M : ℕ} {r r' r'' : Record p} (h : addRec r r' = some r'') :
    pad M r'' = pad M r + pad M r' := by
  unfold addRec at h
  rcases r with ⟨a, b, lc, rc, m⟩
  rcases r' with ⟨a', b', lc', rc', m'⟩
  by_cases hc : a = a' ∧ b = b' ∧ lc = lc' ∧ rc = rc'
  · rw [dif_pos hc] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    cases h
    simp [pad, padMat_add]
  · rw [dif_neg hc] at h
    cases h

lemma pad_constMul {M : ℕ} (r : Record p) (a : ZMod p) :
    pad M (constMulRec r a) = a • pad M r := padMat_smul a r.mat

lemma pad_mul {M : ℕ} {r r' r'' : Record p} (h : multRec r r' = some r'')
    (hc : r.cols ≤ M) :
    pad M r'' = pad M r * pad M r' := by
  unfold multRec at h
  rcases r with ⟨a, b, lc, rc, m⟩
  rcases r' with ⟨a', b', lc', rc', m'⟩
  by_cases hcond : b = a' ∧ rc = lc'
  · rw [dif_pos hcond] at h
    obtain ⟨rfl, rfl⟩ := hcond
    cases h
    simpa [pad] using padMat_mul m m' hc
  · rw [dif_neg hcond] at h
    cases h

/-! ### Formal words: expressions as non-commutative polynomials in the handles -/

/-- The non-commutative formal polynomial of an expression, in the handle variables. -/
noncomputable def word : QExpr p → MonoidAlgebra (ZMod p) (FreeMonoid ℕ)
  | .init k => MonoidAlgebra.single (FreeMonoid.of k) 1
  | .add e e' => word e + word e'
  | .constMul e a => a • word e
  | .mult e e' => word e * word e'

/-- Evaluation of formal words at the (padded) records of a database. -/
noncomputable def liftDB (M : ℕ) (db : List (Record p)) :
    MonoidAlgebra (ZMod p) (FreeMonoid ℕ) →ₐ[ZMod p] Matrix (Fin M) (Fin M) (ZMod p) :=
  MonoidAlgebra.lift (ZMod p) (Matrix (Fin M) (Fin M) (ZMod p)) (FreeMonoid ℕ)
    (FreeMonoid.lift fun k => pad M ((db[k]?).getD dflt))

/-- The value of a well-formed expression is the evaluation of its formal word. -/
theorem pad_eval_eq_lift {M : ℕ} {db : List (Record p)}
    (hdb : ∀ r ∈ db, r.rows ≤ M ∧ r.cols ≤ M) :
    ∀ (e : QExpr p) (r : Record p), e.eval db = some r →
      r.rows ≤ M ∧ r.cols ≤ M ∧ pad M r = liftDB M db (word e)
  | .init k, r, h => by
    simp only [QExpr.eval] at h
    have hr := hdb r (List.mem_of_getElem? h)
    refine ⟨hr.1, hr.2, ?_⟩
    simp [liftDB, word, h, MonoidAlgebra.lift_single]
  | .add e e', r, h => by
    simp only [QExpr.eval, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, r2, h2, h⟩ := h
    obtain ⟨a1, b1, ih1⟩ := pad_eval_eq_lift hdb e r1 h1
    obtain ⟨-, -, ih2⟩ := pad_eval_eq_lift hdb e' r2 h2
    have hs : r.rows = r1.rows ∧ r.cols = r1.cols := by
      unfold addRec at h
      split_ifs at h
      cases h
      exact ⟨rfl, rfl⟩
    refine ⟨hs.1 ▸ a1, hs.2 ▸ b1, ?_⟩
    rw [pad_add h, ih1, ih2, word, map_add]
  | .constMul e a, r, h => by
    simp only [QExpr.eval, Option.map_eq_some_iff] at h
    obtain ⟨r1, h1, rfl⟩ := h
    obtain ⟨a1, b1, ih1⟩ := pad_eval_eq_lift hdb e r1 h1
    refine ⟨a1, b1, ?_⟩
    rw [pad_constMul, ih1, word, map_smul]
  | .mult e e', r, h => by
    simp only [QExpr.eval, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, r2, h2, h⟩ := h
    obtain ⟨a1, b1, ih1⟩ := pad_eval_eq_lift hdb e r1 h1
    obtain ⟨a2, b2, ih2⟩ := pad_eval_eq_lift hdb e' r2 h2
    have hs : r.rows = r1.rows ∧ r.cols = r2.cols := by
      unfold multRec at h
      split_ifs at h
      cases h
      exact ⟨rfl, rfl⟩
    refine ⟨hs.1 ▸ a1, hs.2 ▸ b2, ?_⟩
    rw [pad_mul h b1, ih1, ih2, word, map_mul]

/-- Padding is injective on records of a fixed shape whose dimensions fit. -/
lemma eq_of_pad_eq {M : ℕ} {r r' : Record p} (hs : r.shape = r'.shape) (hr : r.rows ≤ M)
    (hc : r.cols ≤ M) (h : pad M r = pad M r') : r = r' := by
  rcases r with ⟨a, b, lc, rc, m⟩
  rcases r' with ⟨a', b', lc', rc', m'⟩
  simp only [Record.shape, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
  simp only at hr hc
  congr
  ext i j
  have := congrFun (congrFun h ⟨i.val, by omega⟩) ⟨j.val, by omega⟩
  simpa [pad, padMat, i.isLt, j.isLt] using this

/-! ### Removing the Kilian randomization -/

section Randomization

variable {bp : BP}

/-- The sample with every randomizing matrix replaced by the identity. -/
def unrand (ω : Sample p bp) : Sample p bp := (fun _ => 1, fun _ => 1, ω.2.2)

/-- The left randomizer `R_{a-1}` of a colour (the identity for `src`, `snk`). -/
noncomputable def leftR (ω : Sample p bp) :
    Color → Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p)
  | .prim a => if h : a - 1 < bp.n + 1 then ((ω.R ⟨a - 1, h⟩ : GL _ _) : Matrix _ _ _) else 1
  | .dum a => if h : a - 1 < bp.n + 1 then ((ω.R' ⟨a - 1, h⟩ : GL _ _) : Matrix _ _ _) else 1
  | _ => 1

/-- The right randomizer `R_{a-1}⁻¹` of a colour (the identity for `src`, `snk`). -/
noncomputable def rightR (ω : Sample p bp) :
    Color → Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p)
  | .prim a => if h : a - 1 < bp.n + 1 then (((ω.R ⟨a - 1, h⟩)⁻¹ : GL _ _) : Matrix _ _ _) else 1
  | .dum a => if h : a - 1 < bp.n + 1 then (((ω.R' ⟨a - 1, h⟩)⁻¹ : GL _ _) : Matrix _ _ _)
      else 1
  | _ => 1

lemma rightR_mul_leftR (ω : Sample p bp) (c : Color) :
    rightR ω c * leftR ω c = 1 := by
  cases c <;> simp only [rightR, leftR] <;> (try split_ifs) <;> simp

lemma isUnit_leftR (ω : Sample p bp) (c : Color) : IsUnit (leftR ω c) := by
  cases c <;> simp only [leftR] <;> (try split_ifs) <;>
    first | exact Units.isUnit _ | exact isUnit_one

lemma isUnit_rightR (ω : Sample p bp) (c : Color) : IsUnit (rightR ω c) := by
  cases c <;> simp only [rightR] <;> (try split_ifs) <;>
    first | exact Units.isUnit _ | exact isUnit_one

lemma leftR_prim_succ (ω : Sample p bp) (i : Fin bp.n) :
    leftR ω (.prim (i.val + 1)) = ((ω.R i.castSucc : GL _ _) : Matrix _ _ _) := by
  simp only [leftR]
  rw [dif_pos (by omega)]
  all_goals congr 3

lemma leftR_dum_succ (ω : Sample p bp) (i : Fin bp.n) :
    leftR ω (.dum (i.val + 1)) = ((ω.R' i.castSucc : GL _ _) : Matrix _ _ _) := by
  simp only [leftR]
  rw [dif_pos (by omega)]
  all_goals congr 3

lemma rightR_prim_succ_succ (ω : Sample p bp) (i : Fin bp.n) :
    rightR ω (.prim (i.val + 2)) = (((ω.R i.succ)⁻¹ : GL _ _) : Matrix _ _ _) := by
  simp only [rightR]
  rw [dif_pos (by omega)]
  all_goals congr 4

lemma rightR_dum_succ_succ (ω : Sample p bp) (i : Fin bp.n) :
    rightR ω (.dum (i.val + 2)) = (((ω.R' i.succ)⁻¹ : GL _ _) : Matrix _ _ _) := by
  simp only [rightR]
  rw [dif_pos (by omega)]
  all_goals congr 4

/-- Each record is the randomization of the corresponding record of the unrandomized sample. -/
def RandRel (ω : Sample p bp) (r r₁ : Record p) : Prop :=
  r.shape = r₁.shape ∧ pad (NDim bp.n) r = leftR ω r.lc * pad (NDim bp.n) r₁ * rightR ω r.rc

lemma stepRec_randRel (ω : Sample p bp) (primal : Bool) (i : Fin bp.n) (b : Bool) :
    RandRel ω (stepRec ω primal i b) (stepRec (unrand ω) primal i b) := by
  cases primal
  · refine ⟨rfl, ?_⟩
    simp only [stepRec, pad, padMat_square, Bool.false_eq_true, if_false]
    rw [leftR_dum_succ, rightR_dum_succ_succ]
    simp [D'Til, unrand, Sample.R', D'mat, Sample.d', Sample.γ]
  · refine ⟨rfl, ?_⟩
    simp only [stepRec, pad, padMat_square, if_true]
    rw [leftR_prim_succ, rightR_prim_succ_succ]
    simp [DTil, unrand, Sample.R, Dmat, Sample.d, Sample.γ]

lemma forall₂_map_same {α β : Type} {R : β → β → Prop} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, R (f a) (g a)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma forall₂_flatMap_same {α β : Type} {R : β → β → Prop} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma programRecs_randRel (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp)
    (primal : Bool) :
    List.Forall₂ (RandRel ω) (programRecs bp J σ ω primal) (programRecs bp J σ (unrand ω) primal) := by
  unfold programRecs
  refine List.rel_append (forall₂_map_same _ _ _ fun i _ => stepRec_randRel ω primal i _)
    (forall₂_flatMap_same _ _ _ fun i _ => ?_)
  exact List.Forall₂.cons (stepRec_randRel ω primal i false)
    (List.Forall₂.cons (stepRec_randRel ω primal i true) List.Forall₂.nil)

lemma initDB_randRel (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp) :
    List.Forall₂ (RandRel ω) (initDB bp J σ ω) (initDB bp J σ (unrand ω)) := by
  unfold initDB
  refine List.rel_append (List.rel_append ?_ (programRecs_randRel J σ ω true))
    (programRecs_randRel J σ ω false)
  have hl1 : leftR ω (.prim (bp.n + 1)) = ((ω.R (Fin.last bp.n) : GL _ _) : Matrix _ _ _) := by
    simp only [leftR]
    rw [dif_pos (by omega)]
    all_goals congr 3
  have hl2 : leftR ω (.dum (bp.n + 1)) = ((ω.R' (Fin.last bp.n) : GL _ _) : Matrix _ _ _) := by
    simp only [leftR]
    rw [dif_pos (by omega)]
    all_goals congr 3
  have hr1 : rightR ω (.prim 1) = (((ω.R 0)⁻¹ : GL _ _) : Matrix _ _ _) := by
    simp only [rightR]
    rw [dif_pos (by omega)]
    rfl
  have hr2 : rightR ω (.dum 1) = (((ω.R' 0)⁻¹ : GL _ _) : Matrix _ _ _) := by
    simp only [rightR]
    rw [dif_pos (by omega)]
    rfl
  refine List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩
    (List.Forall₂.cons ⟨rfl, ?_⟩ (List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil)))
  · simp only [pad, hr1, leftR, one_mul, sTil, unrand, Sample.R, Sample.sMid, Sample.sStar]
    rw [padMat_mul _ _ le_rfl, padMat_square]
    simp
  · simp only [pad, hr2, leftR, one_mul, s'Til, unrand, Sample.R', Sample.s'Mid, Sample.s'Star]
    rw [padMat_mul _ _ le_rfl, padMat_square]
    simp
  · simp only [pad, hl1, rightR, mul_one, tTil, unrand, Sample.R, Sample.tLow, Sample.tStar]
    rw [padMat_mul _ _ le_rfl, padMat_square]
    simp
  · simp only [pad, hl2, rightR, mul_one, t'Til, unrand, Sample.R', Sample.t'Low, Sample.t'Star]
    rw [padMat_mul _ _ le_rfl, padMat_square]
    simp

end Randomization

/-! ### Shapes (as in the simulation proof) -/

section Shapes

lemma stepRec_shape {bp : BP} (ω : Sample p bp) (primal : Bool) (i : Fin bp.n) (b : Bool) :
    (stepRec ω primal i b).shape = stepShape bp.n primal i.val := by
  cases primal <;> rfl

lemma programRecs_shapes (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (ω : Sample p bp) (primal : Bool) :
    (programRecs bp J σ ω primal).map Record.shape = programShapes bp J primal := by
  unfold programRecs programShapes
  simp [List.map_flatMap, stepRec_shape]

lemma initDB_shapes (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp) :
    (initDB bp J σ ω).map Record.shape = initShapes bp J := by
  unfold initDB initShapes
  simp only [List.map_append, programRecs_shapes]
  rfl

lemma addRec_map_shape (r r' : Record p) :
    (addRec r r').map Record.shape = if r.shape = r'.shape then some r.shape else none := by
  unfold addRec
  by_cases h : r.rows = r'.rows ∧ r.cols = r'.cols ∧ r.lc = r'.lc ∧ r.rc = r'.rc
  · rw [dif_pos h, if_pos (by simp [Record.shape, h.1, h.2.1, h.2.2.1, h.2.2.2])]
    rfl
  · rw [dif_neg h, if_neg (by simpa [Record.shape] using h)]
    rfl

lemma multRec_map_shape (r r' : Record p) :
    (multRec r r').map Record.shape =
      if r.shape.2.1 = r'.shape.1 ∧ r.shape.2.2.2 = r'.shape.2.2.1 then
        some (r.shape.1, r'.shape.2.1, r.shape.2.2.1, r'.shape.2.2.2) else none := by
  unfold multRec
  by_cases h : r.cols = r'.rows ∧ r.rc = r'.lc
  · rw [dif_pos h, if_pos (by simpa [Record.shape] using h)]
    rfl
  · rw [dif_neg h, if_neg (by simpa [Record.shape] using h)]
    rfl

theorem eval_map_shape {bp : BP} {J : Finset (Fin bp.ℓ)} {db : List (Record p)}
    (hdb : db.map Record.shape = initShapes bp J) (e : QExpr p) :
    (e.eval db).map Record.shape = e.shape bp J := by
  induction e with
  | init k => simp [QExpr.eval, QExpr.shape, ← hdb]
  | add e e' ih ih' =>
    simp only [QExpr.eval, QExpr.shape, ← ih, ← ih']
    cases e.eval db <;> cases e'.eval db <;> simp [addRec_map_shape]
  | constMul e a ih =>
    simp only [QExpr.eval, QExpr.shape, ← ih]
    cases e.eval db <;> rfl
  | mult e e' ih ih' =>
    simp only [QExpr.eval, QExpr.shape, ← ih, ← ih']
    cases e.eval db <;> cases e'.eval db <;> simp [multRec_map_shape]

lemma exists_eval_of_shape {bp : BP} {J : Finset (Fin bp.ℓ)} {db : List (Record p)}
    (hdb : db.map Record.shape = initShapes bp J) {e : QExpr p} {s : Shape}
    (hs : e.shape bp J = some s) : ∃ r, e.eval db = some r ∧ r.shape = s := by
  have h := eval_map_shape hdb e
  rw [hs] at h
  rcases he : e.eval db with _ | r
  · rw [he] at h
    simp at h
  · rw [he] at h
    exact ⟨r, rfl, Option.some_injective _ h⟩

lemma initShapes_dims (bp : BP) (J : Finset (Fin bp.ℓ)) :
    ∀ s ∈ initShapes bp J, s.1 ≤ NDim bp.n ∧ s.2.1 ≤ NDim bp.n := by
  intro s hs
  simp only [initShapes, programShapes, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_flatMap, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl | rfl) | ⟨i, -, rfl⟩ | ⟨i, -, rfl | rfl⟩) |
    ⟨i, -, rfl⟩ | ⟨i, -, rfl | rfl⟩) <;> simp [stepShape] <;> omega

lemma initDB_dims (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp) :
    ∀ r ∈ initDB bp J σ ω, r.rows ≤ NDim bp.n ∧ r.cols ≤ NDim bp.n := by
  intro r hr
  have : r.shape ∈ initShapes bp J := by
    rw [← initDB_shapes bp J σ ω]
    exact List.mem_map_of_mem hr
  exact initShapes_dims bp J _ this

end Shapes

/-! ### Colour paths -/

/-- `u` is a colour path from `a` to `b` through records with the shapes `sh`. -/
def IsPath (sh : List Shape) : Color → Color → List ℕ → Prop
  | _, _, [] => False
  | a, b, k :: u => ∃ s, sh[k]? = some s ∧ s.2.2.1 = a ∧
      ((u = [] ∧ s.2.2.2 = b) ∨ IsPath sh s.2.2.2 b u)

lemma IsPath.append {sh : List Shape} :
    ∀ {a c b : Color} {u v : List ℕ}, IsPath sh a c u → IsPath sh c b v → IsPath sh a b (u ++ v)
  | _, _, _, [], _, hu, _ => hu.elim
  | _, _, _, _ :: _, _, ⟨s, hs, hl, h⟩, hv => by
    refine ⟨s, hs, hl, Or.inr ?_⟩
    rcases h with ⟨rfl, hc⟩ | h
    · rw [hc]
      exact hv
    · exact IsPath.append h hv

noncomputable instance instDecEqFreeMonoidNat : DecidableEq (FreeMonoid ℕ) := Classical.decEq _

lemma word_support {bp : BP} {J : Finset (Fin bp.ℓ)} :
    ∀ (e : QExpr p) (s : Shape), e.shape bp J = some s →
      ∀ u ∈ (word e).coeff.support, IsPath (initShapes bp J) s.2.2.1 s.2.2.2 (FreeMonoid.toList u)
  | .init k, s, hs, u, hu => by
    simp only [word, MonoidAlgebra.coeff_single] at hu
    have := Finsupp.support_single_subset hu
    rw [Finset.mem_singleton] at this
    subst this
    exact ⟨s, hs, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | .add e e', s, hs, u, hu => by
    simp only [QExpr.shape, Option.bind_eq_some_iff] at hs
    obtain ⟨s1, h1, s2, h2, hs⟩ := hs
    by_cases h12 : s1 = s2
    · rw [if_pos h12] at hs
      cases hs
      subst h12
      simp only [word, MonoidAlgebra.coeff_add] at hu
      rcases Finset.mem_union.1 (Finsupp.support_add hu) with hu | hu
      · exact word_support e _ h1 u hu
      · exact word_support e' _ h2 u hu
    · rw [if_neg h12] at hs
      cases hs
  | .constMul e a, s, hs, u, hu => by
    simp only [word, MonoidAlgebra.coeff_smul] at hu
    exact word_support e s hs u (Finsupp.support_smul hu)
  | .mult e e', s, hs, u, hu => by
    simp only [QExpr.shape, Option.bind_eq_some_iff] at hs
    obtain ⟨s1, h1, s2, h2, hs⟩ := hs
    by_cases h12 : s1.2.1 = s2.1 ∧ s1.2.2.2 = s2.2.2.1
    · rw [if_pos h12] at hs
      cases hs
      simp only [word] at hu
      obtain ⟨u1, hu1, u2, hu2, rfl⟩ :=
        Finset.mem_mul.1 (MonoidAlgebra.support_coeff_mul_subset _ _ hu)
      rw [FreeMonoid.toList_mul]
      have := word_support e' _ h2 u2 hu2
      rw [← h12.2] at this
      exact (word_support e _ h1 u1 hu1).append this
    · rw [if_neg h12] at hs
      cases hs

/-! ### The randomization cancels along colour paths -/

section PathRand

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- The padded matrix of handle `k`. -/
noncomputable def hmat (M : ℕ) (db : List (Record p)) (k : ℕ) : Matrix (Fin M) (Fin M) (ZMod p) :=
  pad M ((db[k]?).getD dflt)

lemma forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {k : ℕ} {x : α}, l₁[k]? = some x →
      ∃ y, l₂[k]? = some y ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hab⟩
  | _, _, .cons _ hl, k + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hl h

lemma path_prod_rand (ω : Sample p bp) :
    ∀ (a b : Color) (u : List ℕ), IsPath (initShapes bp J) a b u →
      (u.map (hmat (NDim bp.n) (initDB bp J σ ω))).prod =
        leftR ω a * (u.map (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod * rightR ω b
  | _, _, [], h => h.elim
  | a, b, k :: u, ⟨s, hs, hl, h⟩ => by
    have hk : (initDB bp J σ ω)[k]?.map Record.shape = some s := by
      rw [← List.getElem?_map, initDB_shapes, hs]
    rcases hr : (initDB bp J σ ω)[k]? with _ | r
    · rw [hr] at hk
      simp at hk
    rw [hr] at hk
    have hrs : r.shape = s := Option.some_injective _ hk
    obtain ⟨r₁, hr₁, hrel⟩ := forall₂_getElem? (initDB_randRel J σ ω) hr
    have hlc : r.lc = a := by
      rw [← hl, ← hrs]
      rfl
    have h1 : hmat (NDim bp.n) (initDB bp J σ ω) k = pad (NDim bp.n) r := by simp [hmat, hr]
    have h2 : hmat (NDim bp.n) (initDB bp J σ (unrand ω)) k = pad (NDim bp.n) r₁ := by
      simp [hmat, hr₁]
    simp only [List.map_cons, List.prod_cons, h1, h2]
    rw [hrel.2, hlc]
    rcases h with ⟨rfl, hb⟩ | h
    · have hrc : r.rc = b := by
        rw [← hb, ← hrs]
        rfl
      simp [hrc]
    · have hrc : r.rc = s.2.2.2 := by
        rw [← hrs]
        rfl
      rw [path_prod_rand ω s.2.2.2 b u h, hrc]
      rw [show ∀ X : Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p),
          leftR ω a * pad (NDim bp.n) r₁ * rightR ω s.2.2.2 * (leftR ω s.2.2.2 * X * rightR ω b) =
            leftR ω a * pad (NDim bp.n) r₁ * (rightR ω s.2.2.2 * leftR ω s.2.2.2) * X *
              rightR ω b from fun X => by simp only [Matrix.mul_assoc], rightR_mul_leftR,
        Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- On combinations of colour paths from `a` to `b`, the randomization factors out. -/
lemma lift_rand (ω : Sample p bp) (a b : Color) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, IsPath (initShapes bp J) a b (FreeMonoid.toList u)) :
    liftDB (NDim bp.n) (initDB bp J σ ω) w =
      leftR ω a * liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w * rightR ω b := by
  simp only [liftDB, MonoidAlgebra.lift_apply, Finsupp.sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [FreeMonoid.lift_apply, FreeMonoid.lift_apply]
  have := path_prod_rand (J := J) (σ := σ) ω a b _ (hw u hu)
  unfold hmat at this
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

/-- Two well-formed expressions of the same shape have equal values iff the unrandomized
evaluation of the difference of their words vanishes. -/
theorem eval_eq_iff (ω : Sample p bp) {e e' : QExpr p} {s : Shape}
    (hs : e.shape bp J = some s) (hs' : e'.shape bp J = some s) :
    e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) ↔
      liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) (word e - word e') = 0 := by
  have hdb := initDB_shapes bp J σ ω
  obtain ⟨r, hr, hrs⟩ := exists_eval_of_shape hdb hs
  obtain ⟨r', hr', hrs'⟩ := exists_eval_of_shape hdb hs'
  obtain ⟨hrow, hcol, hpad⟩ := pad_eval_eq_lift (initDB_dims bp J σ ω) e r hr
  obtain ⟨-, -, hpad'⟩ := pad_eval_eq_lift (initDB_dims bp J σ ω) e' r' hr'
  have hw : ∀ u ∈ (word e - word e').coeff.support,
      IsPath (initShapes bp J) s.2.2.1 s.2.2.2 (FreeMonoid.toList u) := by
    intro u hu
    rw [MonoidAlgebra.coeff_sub] at hu
    rcases Finset.mem_union.1 (Finsupp.support_sub hu) with hu | hu
    · exact word_support e s hs u hu
    · exact word_support e' s hs' u hu
  rw [hr, hr', ← (isUnit_leftR ω s.2.2.1).mul_right_eq_zero,
    ← (isUnit_rightR ω s.2.2.2).mul_left_eq_zero, ← lift_rand ω _ _ _ hw, map_sub, sub_eq_zero,
    ← hpad, ← hpad']
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [eq_of_pad_eq (hrs.trans hrs'.symm) hrow hcol h]

end PathRand

/-! ### Handles of the initial database -/

section Handles

variable {bp : BP}

/-- The colour `i` (primal) or `i′` (dummy). -/
def pc (primal : Bool) (a : ℕ) : Color := if primal then .prim a else .dum a

lemma pc_inj {pr pr' : Bool} {a a' : ℕ} (h : pc pr a = pc pr' a') : pr = pr' ∧ a = a' := by
  cases pr <;> cases pr' <;> simp_all [pc]

lemma pc_ne_src (pr : Bool) (a : ℕ) : pc pr a ≠ .src := by cases pr <;> simp [pc]

lemma pc_ne_snk (pr : Bool) (a : ℕ) : pc pr a ≠ .snk := by cases pr <;> simp [pc]

lemma stepShape_eq (n : ℕ) (pr : Bool) (i : ℕ) :
    stepShape n pr i = (NDim n, NDim n, pc pr (i + 1), pc pr (i + 2)) := by
  cases pr <;> rfl

/-- The step slots of one program, in database order: `(i, false)` for a fixed step,
`(i, false), (i, true)` for a free step. -/
def programSlots (bp : BP) (J : Finset (Fin bp.ℓ)) : List (Fin bp.n × Bool) :=
  ((List.finRange bp.n).filter fun i => bp.inp i ∈ J).map (fun i => (i, false)) ++
    ((List.finRange bp.n).filter fun i => bp.inp i ∉ J).flatMap
      (fun i => [(i, false), (i, true)])

/-- The bit actually used by a slot under the assignment `σ`. -/
def act (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (x : Fin bp.n × Bool) : Bool :=
  if bp.inp x.1 ∈ J then σ (bp.inp x.1) else x.2

lemma programRecs_eq_slots (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp)
    (primal : Bool) :
    programRecs bp J σ ω primal =
      (programSlots bp J).map fun x => stepRec ω primal x.1 (act bp J σ x) := by
  unfold programRecs programSlots
  rw [List.map_append, List.map_map, List.map_flatMap]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := (List.mem_filter.1 hi).2
    simp only [decide_eq_true_eq] at this
    simp [act, this]
  · refine List.flatMap_congr fun i hi => ?_
    have := (List.mem_filter.1 hi).2
    simp only [decide_eq_true_eq] at this
    simp [act, this]

lemma programShapes_eq_slots (J : Finset (Fin bp.ℓ)) (primal : Bool) :
    programShapes bp J primal =
      (programSlots bp J).map fun x => stepShape bp.n primal x.1.val := by
  unfold programShapes programSlots
  rw [List.map_append, List.map_map, List.map_flatMap]
  rfl

lemma programSlots_nodup (J : Finset (Fin bp.ℓ)) : (programSlots bp J).Nodup := by
  unfold programSlots
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact ((List.nodup_finRange _).filter _).map (fun a b h => by simpa using h)
  · rw [List.nodup_flatMap]
    refine ⟨fun i _ => by simp, ?_⟩
    refine ((List.nodup_finRange _).filter _).pairwise_of_forall_ne fun i _ j _ hij => ?_
    simp [List.Disjoint, hij, Ne.symm hij]
  · intro x hx y hy hxy
    subst hxy
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hx
    simp only [List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, h⟩ := hy
    rcases h with h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h <;>
      exact hj hi

/-- Slots of a fixed step use the bit `false`. -/
lemma slot_fixed {J : Finset (Fin bp.ℓ)} {x : Fin bp.n × Bool} (hx : x ∈ programSlots bp J)
    (hJ : bp.inp x.1 ∈ J) : x.2 = false := by
  simp only [programSlots, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with ⟨i, -, rfl⟩ | ⟨i, hi, rfl | rfl⟩
  · rfl
  · rfl
  · exact absurd hJ hi

/-- `(step, actual bit)` determines the slot. -/
lemma slot_eq_of_act {J : Finset (Fin bp.ℓ)} (σ : Fin bp.ℓ → Bool) {x y : Fin bp.n × Bool}
    (hx : x ∈ programSlots bp J) (hy : y ∈ programSlots bp J) (h1 : x.1 = y.1)
    (h2 : act bp J σ x = act bp J σ y) : x = y := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  simp only at h1
  subst h1
  by_cases hJ : bp.inp i ∈ J
  · have ha := slot_fixed hx hJ
    have hb := slot_fixed hy hJ
    simp only at ha hb
    rw [ha, hb]
  · simp only [act, hJ, if_false] at h2
    rw [h2]

/-- The handle of a slot of the primal or the dummy program. -/
def hdl (bp : BP) (J : Finset (Fin bp.ℓ)) (primal : Bool) (x : Fin bp.n × Bool) : ℕ :=
  4 + (if primal then 0 else (programSlots bp J).length) + (programSlots bp J).idxOf x

/-- The handle of `s̃` (primal) or `s̃′` (dummy). -/
def sH (primal : Bool) : ℕ := if primal then 0 else 1

/-- The handle of `t̃` (primal) or `t̃′` (dummy). -/
def tH (primal : Bool) : ℕ := if primal then 2 else 3

/-- The four bookend shapes. -/
def bookendShapes (n : ℕ) : List Shape :=
  [(1, NDim n, .src, pc true 1), (1, NDim n, .src, pc false 1),
   (NDim n, 1, pc true (n + 1), .snk), (NDim n, 1, pc false (n + 1), .snk)]

lemma initShapes_eq (J : Finset (Fin bp.ℓ)) :
    initShapes bp J = bookendShapes bp.n ++
      (programSlots bp J).map (fun x => stepShape bp.n true x.1.val) ++
      (programSlots bp J).map (fun x => stepShape bp.n false x.1.val) := by
  unfold initShapes
  rw [programShapes_eq_slots, programShapes_eq_slots]
  rfl

/-- Classification of handles by their shape. -/
lemma handle_cases (J : Finset (Fin bp.ℓ)) {k : ℕ} {s : Shape}
    (hs : (initShapes bp J)[k]? = some s) :
    (∃ pr : Bool, k = sH pr ∧ s = (1, NDim bp.n, .src, pc pr 1)) ∨
    (∃ pr : Bool, k = tH pr ∧ s = (NDim bp.n, 1, pc pr (bp.n + 1), .snk)) ∨
    (∃ (pr : Bool) (x : Fin bp.n × Bool), x ∈ programSlots bp J ∧ k = hdl bp J pr x ∧
      s = stepShape bp.n pr x.1.val) := by
  rw [initShapes_eq] at hs
  have hnd := programSlots_nodup (bp := bp) J
  by_cases h4 : k < 4
  · rw [List.getElem?_append_left (by simp [bookendShapes]; omega),
      List.getElem?_append_left (by simp [bookendShapes]; omega)] at hs
    interval_cases k <;> simp [bookendShapes] at hs <;> subst hs
    · exact Or.inl ⟨true, rfl, rfl⟩
    · exact Or.inl ⟨false, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨true, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨false, rfl, rfl⟩)
  · right; right
    by_cases hL : k - 4 < (programSlots bp J).length
    · rw [List.getElem?_append_left (by simp [bookendShapes]; omega),
        List.getElem?_append_right (by simp [bookendShapes]; omega), List.getElem?_map] at hs
      simp only [bookendShapes, List.length_cons, List.length_nil] at hs
      rw [List.getElem?_eq_getElem hL] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      refine ⟨true, _, List.getElem_mem hL, ?_, hs.symm⟩
      simp only [hdl, if_true, add_zero]
      rw [hnd.idxOf_getElem]
      omega
    · have hL2 : k - 4 - (programSlots bp J).length < (programSlots bp J).length := by
        have := List.getElem?_eq_none_iff.not.1 (fun h => by
          rw [List.getElem?_append_right (by simp [bookendShapes]; omega), List.getElem?_map,
            h] at hs
          simp at hs)
        simp [bookendShapes] at this
        omega
      rw [List.getElem?_append_right (by simp [bookendShapes]; omega), List.getElem?_map] at hs
      simp only [List.length_append, bookendShapes, List.length_cons, List.length_nil,
        List.length_map] at hs
      rw [show k - (0 + 1 + 1 + 1 + 1 + (programSlots bp J).length) =
          k - 4 - (programSlots bp J).length by omega, List.getElem?_eq_getElem hL2] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      refine ⟨false, _, List.getElem_mem hL2, ?_, hs.symm⟩
      simp only [hdl, Bool.false_eq_true, if_false]
      rw [hnd.idxOf_getElem]
      omega

lemma no_path_from_snk (J : Finset (Fin bp.ℓ)) :
    ∀ (b : Color) (u : List ℕ), ¬ IsPath (initShapes bp J) .snk b u
  | _, [], h => h
  | _, k :: _, ⟨s, hs, hl, _⟩ => by
    rcases handle_cases J hs with ⟨pr, -, rfl⟩ | ⟨pr, -, rfl⟩ | ⟨pr, x, -, -, rfl⟩
    · exact absurd hl (by simp)
    · exact pc_ne_snk pr _ hl
    · rw [stepShape_eq] at hl
      exact pc_ne_snk pr _ hl

/-- A run of slots for the consecutive steps `i, i+1, …`. -/
def IsRun (bp : BP) (J : Finset (Fin bp.ℓ)) (i : ℕ) (xs : List (Fin bp.n × Bool)) : Prop :=
  ∀ t (ht : t < xs.length), xs[t] ∈ programSlots bp J ∧ xs[t].1.val = i + t

lemma IsRun.cons {J : Finset (Fin bp.ℓ)} {i : ℕ} {x : Fin bp.n × Bool}
    {xs : List (Fin bp.n × Bool)} (hx : x ∈ programSlots bp J) (hxi : x.1.val = i)
    (h : IsRun bp J (i + 1) xs) : IsRun bp J i (x :: xs) := by
  intro t ht
  cases t with
  | zero => exact ⟨hx, by simpa using hxi⟩
  | succ t =>
    obtain ⟨h1, h2⟩ := h t (by simpa using ht)
    exact ⟨h1, by simp [h2]; omega⟩

/-- Structure of a path starting at a step colour: a run of step handles of one program,
possibly followed by the bookend `t̃` / `t̃′`. -/
theorem path_from_step (J : Finset (Fin bp.ℓ)) (pr : Bool) :
    ∀ (u : List ℕ) (i : ℕ) (b : Color), IsPath (initShapes bp J) (pc pr (i + 1)) b u →
      ∃ xs, IsRun bp J i xs ∧
        ((xs ≠ [] ∧ u = xs.map (hdl bp J pr) ∧ b = pc pr (i + 1 + xs.length)) ∨
          (u = xs.map (hdl bp J pr) ++ [tH pr] ∧ i + xs.length = bp.n ∧ b = .snk))
  | [], _, _, h => h.elim
  | k :: u, i, b, ⟨s, hs, hl, h⟩ => by
    rcases handle_cases J hs with ⟨pr', -, rfl⟩ | ⟨pr', rfl, rfl⟩ | ⟨pr', x, hx, rfl, rfl⟩
    · exact absurd hl.symm (pc_ne_src _ _)
    · obtain ⟨rfl, hi⟩ := pc_inj hl
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨[], fun t ht => by simp at ht, Or.inr ⟨by simp, by simpa using hi.symm, rfl⟩⟩
      · exact absurd h (no_path_from_snk J _ _)
    · rw [stepShape_eq] at hl h
      obtain ⟨rfl, hi⟩ := pc_inj hl
      have hxi : x.1.val = i := by omega
      rcases h with ⟨rfl, rfl⟩ | h
      · refine ⟨[x], ?_, Or.inl ⟨by simp, rfl, by simp [hxi]⟩⟩
        exact IsRun.cons hx hxi (fun t ht => by simp at ht)
      · simp only at h
        rw [show x.1.val + 2 = (i + 1) + 1 by omega] at h
        obtain ⟨xs, hrun, hxs⟩ := path_from_step J pr' u (i + 1) b h
        refine ⟨x :: xs, IsRun.cons hx hxi hrun, ?_⟩
        rcases hxs with ⟨-, rfl, rfl⟩ | ⟨rfl, hlen, rfl⟩
        · exact Or.inl ⟨by simp, rfl, by simp; ring_nf⟩
        · exact Or.inr ⟨by simp, by simp; omega, rfl⟩

/-- Structure of a path starting at `src`: the bookend `s̃` / `s̃′` followed by a path from colour
`1` / `1′` (or nothing). -/
theorem path_from_src (J : Finset (Fin bp.ℓ)) {b : Color} {u : List ℕ}
    (h : IsPath (initShapes bp J) .src b u) :
    ∃ pr u', u = sH pr :: u' ∧ ((u' = [] ∧ b = pc pr 1) ∨ IsPath (initShapes bp J) (pc pr 1) b u') := by
  rcases u with _ | ⟨k, u⟩
  · exact h.elim
  obtain ⟨s, hs, hl, h⟩ := h
  rcases handle_cases J hs with ⟨pr, rfl, rfl⟩ | ⟨pr, -, rfl⟩ | ⟨pr, x, -, -, rfl⟩
  · refine ⟨pr, u, rfl, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr h
  · exact absurd hl (pc_ne_src _ _)
  · rw [stepShape_eq] at hl
    exact absurd hl (pc_ne_src _ _)

end Handles

/-! ### Scalar coordinates of a sample and the Schwartz–Zippel lemma -/

section Coordinates

/-- The scalar coordinates of a sample: everything except the randomizing matrices and the
bookend 5-vectors. -/
inductive Coord (bp : BP)
  | d (primal : Bool) (k : Fin bp.n) (b : Bool) (c : Fin (2 * mDim bp.n))
  | sMid (primal : Bool) (c : Fin (mDim bp.n))
  | tLow (primal : Bool) (c : Fin (mDim bp.n))
  | γ (j : Fin bp.ℓ) (b : Bool) (x : Fin (2 * bp.n))
  deriving DecidableEq, Fintype

variable {bp : BP}

/-- The value of a scalar coordinate. -/
def coordVal (ω : Sample p bp) : Coord bp → ZMod p
  | .d true k b c => ω.d k b c
  | .d false k b c => ω.d' k b c
  | .sMid true c => ω.sMid c
  | .sMid false c => ω.s'Mid c
  | .tLow true c => ω.tLow c
  | .tLow false c => ω.t'Low c
  | .γ j b x => ω.γ j b x

/-- The non-scalar part of a sample: randomizers and bookend 5-vectors. -/
abbrev Rest (p : ℕ) (bp : BP) :=
  (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) ×
  (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) × Bookends p

/-- A sample is its non-scalar part together with its scalar coordinates. -/
def sampleEquiv : Sample p bp ≃ Rest p bp × (Coord bp → ZMod p) where
  toFun ω := ((ω.1, ω.2.1, ω.2.2.2.2.2.2.2.2.1), coordVal ω)
  invFun x := (x.1.1, x.1.2.1, fun k b c => x.2 (.d true k b c),
    fun k b c => x.2 (.d false k b c), fun c => x.2 (.sMid true c),
    fun c => x.2 (.sMid false c), fun c => x.2 (.tLow true c), fun c => x.2 (.tLow false c),
    x.1.2.2, fun j b y => x.2 (.γ j b y))
  left_inv ω := rfl
  right_inv x := by
    refine Prod.ext rfl (funext fun c => ?_)
    cases c with
    | d pr k b c => cases pr <;> rfl
    | sMid pr c => cases pr <;> rfl
    | tLow pr c => cases pr <;> rfl
    | γ j b y => rfl

lemma sampleEquiv_snd (ω : Sample p bp) : (sampleEquiv ω).2 = coordVal ω := rfl

lemma sampleEquiv_bookends (ω : Sample p bp) :
    (sampleEquiv ω).1.2.2 = ω.2.2.2.2.2.2.2.2.1 := rfl

instance instNeZeroOfPrime [Fact p.Prime] : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

instance instFintypeRest [Fact p.Prime] : Fintype (Rest p bp) := by
  unfold Rest
  infer_instance

variable [Fact p.Prime]

open Classical in
/-- An event depending only on the scalar coordinates. -/
lemma card_filter_coord (Q : (Coord bp → ZMod p) → Prop) [DecidablePred Q]
    [DecidablePred fun ω : Sample p bp => Q (coordVal ω)] :
    (Finset.univ.filter fun ω : Sample p bp => Q (coordVal ω)).card =
      Fintype.card (Rest p bp) * (Finset.univ.filter Q).card := by
  calc (Finset.univ.filter fun ω : Sample p bp => Q (coordVal ω)).card
      = ((Finset.univ.filter fun ω : Sample p bp => Q (coordVal ω)).map
          sampleEquiv.toEmbedding).card := (Finset.card_map _).symm
    _ = ((Finset.univ : Finset (Rest p bp)) ×ˢ Finset.univ.filter Q).card := by
        congr 1
        ext x
        simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product]
        have h1 : (sampleEquiv (sampleEquiv.symm x)).2 = x.2 := by simp
        rw [sampleEquiv_snd] at h1
        rw [h1]
    _ = _ := by rw [Finset.card_product, Finset.card_univ]

open Classical in
/-- An event depending on the bookend vectors and the scalar coordinates. -/
lemma card_filter_bk_coord (Q : Bookends p → (Coord bp → ZMod p) → Prop)
    [∀ bk, DecidablePred (Q bk)]
    [DecidablePred fun ω : Sample p bp => Q ω.2.2.2.2.2.2.2.2.1 (coordVal ω)]
    [DecidablePred fun x : Rest p bp × (Coord bp → ZMod p) => Q x.1.2.2 x.2] :
    (Finset.univ.filter fun ω : Sample p bp => Q ω.2.2.2.2.2.2.2.2.1 (coordVal ω)).card =
      ∑ x : Rest p bp, (Finset.univ.filter (Q x.2.2)).card := by
  calc (Finset.univ.filter fun ω : Sample p bp => Q ω.2.2.2.2.2.2.2.2.1 (coordVal ω)).card
      = ((Finset.univ.filter fun ω : Sample p bp => Q ω.2.2.2.2.2.2.2.2.1 (coordVal ω)).map
          sampleEquiv.toEmbedding).card := (Finset.card_map _).symm
    _ = (Finset.univ.filter fun x : Rest p bp × (Coord bp → ZMod p) => Q x.1.2.2 x.2).card := by
        congr 1
        ext x
        simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : (sampleEquiv (sampleEquiv.symm x)).2 = x.2 := by simp
        have h2 : (sampleEquiv (sampleEquiv.symm x)).1.2.2 = x.1.2.2 := by simp
        rw [sampleEquiv_snd] at h1
        rw [sampleEquiv_bookends] at h2
        rw [h1, h2]
    _ = _ := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl fun y _ => if_congr Iff.rfl rfl rfl

/-- Schwartz–Zippel on the scalar coordinates. -/
lemma sz_coord (P : MvPolynomial (Coord bp) (ZMod p)) (hP : P ≠ 0) :
    ((Finset.univ.filter fun z : Coord bp → ZMod p => MvPolynomial.eval z P = 0).card : ℝ) ≤
      P.totalDegree / p * Fintype.card (Coord bp → ZMod p) := by
  classical
  set e := Fintype.equivFin (Coord bp)
  set P' : MvPolynomial (Fin (Fintype.card (Coord bp))) (ZMod p) := MvPolynomial.rename e P
  have hP' : P' ≠ 0 := fun h => hP (MvPolynomial.rename_injective e e.injective (by simpa using h))
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP' (Finset.univ : Finset (ZMod p))
  rw [Fintype.piFinset_univ] at hsz
  have hcard : (Finset.univ.filter fun f : Fin (Fintype.card (Coord bp)) → ZMod p =>
      MvPolynomial.eval f P' = 0).card =
      (Finset.univ.filter fun z : Coord bp → ZMod p => MvPolynomial.eval z P = 0).card := by
    refine Finset.card_bij (fun f _ => f ∘ e) (fun f hf => ?_) (fun f _ g _ h => ?_)
      (fun z hz => ⟨z ∘ e.symm, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      simpa [P', MvPolynomial.eval_rename] using hf
    · funext i
      have := congrFun h (e.symm i)
      simpa using this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      simpa [P', MvPolynomial.eval_rename, Function.comp_def] using hz
    · funext c
      simp
  rw [hcard] at hsz
  have hdeg : P'.totalDegree ≤ P.totalDegree := MvPolynomial.totalDegree_rename_le _ _
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcardV : (Fintype.card (Coord bp → ZMod p) : ℝ) =
      (p : ℝ) ^ Fintype.card (Coord bp) := by
    rw [Fintype.card_fun, ZMod.card]
    push_cast
    ring
  have hsz' : ((Finset.univ.filter fun z : Coord bp → ZMod p =>
      MvPolynomial.eval z P = 0).card : ℝ) / (p : ℝ) ^ Fintype.card (Coord bp) ≤
      (P'.totalDegree : ℝ) / p := by
    have := (NNRat.cast_le (K := ℝ)).2 hsz
    simpa [Finset.card_univ, ZMod.card, NNRat.cast_div, NNRat.cast_pow] using this
  rw [hcardV]
  rw [div_le_iff₀ (by positivity)] at hsz'
  calc _ ≤ (P'.totalDegree : ℝ) / p * (p : ℝ) ^ Fintype.card (Coord bp) := hsz'
    _ ≤ _ := by gcongr

end Coordinates

/-! ### Block-diagonal algebra and bookend entries -/

section BlockDiag

variable {r : ℕ}

lemma blockDiag_mul (d d' : Fin r → ZMod p) (B B' : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    blockDiag d B * blockDiag d' B' = blockDiag (d * d') (B * B') := by
  simp only [blockDiag, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rfl

lemma blockDiag_one : blockDiag (1 : Fin r → ZMod p) (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) = 1 := by
  simp only [blockDiag, Matrix.reindex_apply]
  rw [show Matrix.diagonal (1 : Fin r → ZMod p) = 1 from Matrix.diagonal_one, Matrix.fromBlocks_one,
    Matrix.submatrix_one_equiv]

lemma prod_blockDiag {α : Type} (l : List α) (f : α → Fin r → ZMod p)
    (g : α → Matrix (Fin 5) (Fin 5) (ZMod p)) :
    (l.map fun a => blockDiag (f a) (g a)).prod = blockDiag (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => simp [blockDiag_one]
  | cons a l ih => simp [ih, blockDiag_mul]

lemma blockDiag_castAdd (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (c c' : Fin r) :
    blockDiag d B (Fin.castAdd 5 c) (Fin.castAdd 5 c') = if c = c' then d c else 0 := by
  simp [blockDiag, Matrix.diagonal_apply]

lemma blockDiag_natAdd_castAdd (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (i : Fin 5) (c : Fin r) : blockDiag d B (Fin.natAdd r i) (Fin.castAdd 5 c) = 0 := by
  simp [blockDiag]

lemma blockDiag_castAdd_natAdd (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (c : Fin r) (i : Fin 5) : blockDiag d B (Fin.castAdd 5 c) (Fin.natAdd r i) = 0 := by
  simp [blockDiag]

lemma blockDiag_natAdd (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (i j : Fin 5) :
    blockDiag d B (Fin.natAdd r i) (Fin.natAdd r j) = B i j := by
  simp [blockDiag]

/-- Row `0` of a padded row vector times a block-diagonal matrix, in a diagonal coordinate. -/
lemma padRow_mul_blockDiag (R : Matrix (Fin 1) (Fin (r + 5)) (ZMod p)) (d : Fin r → ZMod p)
    (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (c : Fin r) :
    (padMat (r + 5) R * blockDiag d B) ⟨0, by omega⟩ (Fin.castAdd 5 c) =
      R 0 (Fin.castAdd 5 c) * d c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd 5 c)]
  · simp only [padMat, blockDiag_castAdd, if_pos rfl]
    rw [dif_pos (by omega), dif_pos (by omega)]
    rfl
  · intro k _ hk
    refine Fin.addCases (fun c' hk => ?_) (fun i _ => ?_) k hk
    · rw [blockDiag_castAdd, if_neg (fun h => hk (by rw [h])), mul_zero]
    · rw [blockDiag_natAdd_castAdd, mul_zero]
  · simp

/-- A block-diagonal matrix times a padded column vector, in a diagonal coordinate. -/
lemma blockDiag_mul_padCol (C : Matrix (Fin (r + 5)) (Fin 1) (ZMod p)) (d : Fin r → ZMod p)
    (B : Matrix (Fin 5) (Fin 5) (ZMod p)) (c : Fin r) :
    (blockDiag d B * padMat (r + 5) C) (Fin.castAdd 5 c) ⟨0, by omega⟩ =
      d c * C (Fin.castAdd 5 c) 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd 5 c)]
  · simp only [padMat, blockDiag_castAdd, if_pos rfl]
    rw [dif_pos (by omega), dif_pos (by omega)]
    rfl
  · intro k _ hk
    refine Fin.addCases (fun c' hk => ?_) (fun i _ => ?_) k hk
    · rw [blockDiag_castAdd, if_neg (fun h => hk (by rw [h])), zero_mul]
    · rw [blockDiag_castAdd_natAdd, zero_mul]
  · simp

end BlockDiag

lemma bookendRow_castAdd {m : ℕ} (mid : Fin m → ZMod p) (star : Fin 5 → ZMod p) (c : Fin (2 * m)) :
    bookendRow mid star 0 (Fin.castAdd 5 c) =
      if h : c.val < m then 0 else mid ⟨c.val - m, by omega⟩ := by
  simp [bookendRow, Fin.append_left]

lemma bookendRow_natAdd {m : ℕ} (mid : Fin m → ZMod p) (star : Fin 5 → ZMod p) (i : Fin 5) :
    bookendRow mid star 0 (Fin.natAdd (2 * m) i) = star i := by
  simp [bookendRow, Fin.append_right]

lemma bookendCol_castAdd {m : ℕ} (low : Fin m → ZMod p) (star : Fin 5 → ZMod p) (c : Fin (2 * m)) :
    bookendCol low star (Fin.castAdd 5 c) 0 = if h : c.val < m then low ⟨c.val, h⟩ else 0 := by
  simp [bookendCol, Fin.append_left]

lemma bookendCol_natAdd {m : ℕ} (low : Fin m → ZMod p) (star : Fin 5 → ZMod p) (i : Fin 5) :
    bookendCol low star (Fin.natAdd (2 * m) i) 0 = star i := by
  simp [bookendCol, Fin.append_right]

/-! ### The unrandomized records of the initial database -/

section Unrand

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- The random diagonals of the primal (`d`) or dummy (`d′`) program. -/
def dsel (pr : Bool) (ω : Sample p bp) : Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p :=
  if pr then ω.d else ω.d'

/-- The `5 × 5` blocks `α_{i,b} A_{i,b}` (primal) or `α′_{i,b} I` (dummy). -/
def Bsel (pr : Bool) (ω : Sample p bp) (i : Fin bp.n) (b : Bool) : Matrix (Fin 5) (Fin 5) (ZMod p) :=
  if pr then alpha bp ω.γ i b • (bp.A i b).permMatrix (ZMod p) else alpha' bp ω.γ i b • 1

/-- Middle entries of `s` / `s′`. -/
def sMidSel (pr : Bool) (ω : Sample p bp) : Fin (mDim bp.n) → ZMod p := if pr then ω.sMid else ω.s'Mid
/-- Bookend vector `s*` / `s*′`. -/
def sStarSel (pr : Bool) (ω : Sample p bp) : Fin 5 → ZMod p := if pr then ω.sStar else ω.s'Star
/-- Low entries of `t` / `t′`. -/
def tLowSel (pr : Bool) (ω : Sample p bp) : Fin (mDim bp.n) → ZMod p := if pr then ω.tLow else ω.t'Low
/-- Bookend vector `t*` / `t*′`. -/
def tStarSel (pr : Bool) (ω : Sample p bp) : Fin 5 → ZMod p := if pr then ω.tStar else ω.t'Star

lemma idxOf_lt {x : Fin bp.n × Bool} (hx : x ∈ programSlots bp J) :
    (programSlots bp J).idxOf x < (programSlots bp J).length := List.idxOf_lt_length_of_mem hx

lemma initDB_hdl (ω : Sample p bp) (pr : Bool) {x : Fin bp.n × Bool}
    (hx : x ∈ programSlots bp J) :
    (initDB bp J σ ω)[hdl bp J pr x]? = some (stepRec ω pr x.1 (act bp J σ x)) := by
  have hi := idxOf_lt (J := J) hx
  unfold initDB
  rw [programRecs_eq_slots, programRecs_eq_slots]
  cases pr
  · rw [List.getElem?_append_right (by simp [hdl]; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, hdl,
      Bool.false_eq_true, if_false]
    rw [show 4 + (programSlots bp J).length + (programSlots bp J).idxOf x -
        (0 + 1 + 1 + 1 + 1 + (programSlots bp J).length) = (programSlots bp J).idxOf x by omega,
      List.getElem?_map, List.getElem?_idxOf hx]
    rfl
  · rw [List.getElem?_append_left (by simp [hdl]; omega),
      List.getElem?_append_right (by simp [hdl])]
    simp only [List.length_cons, List.length_nil, hdl, if_true, add_zero]
    rw [show 4 + (programSlots bp J).idxOf x - (0 + 1 + 1 + 1 + 1) =
        (programSlots bp J).idxOf x by omega, List.getElem?_map, List.getElem?_idxOf hx]
    rfl

lemma hmat_hdl (ω : Sample p bp) (pr : Bool) {x : Fin bp.n × Bool}
    (hx : x ∈ programSlots bp J) :
    hmat (NDim bp.n) (initDB bp J σ (unrand ω)) (hdl bp J pr x) =
      blockDiag (dsel pr ω x.1 (act bp J σ x)) (Bsel pr ω x.1 (act bp J σ x)) := by
  rw [hmat, initDB_hdl _ pr hx, Option.getD_some]
  cases pr <;> simp [stepRec, pad, padMat_square, DTil, D'Til, Dmat, D'mat, unrand, Sample.R,
    Sample.R', dsel, Bsel, Sample.d, Sample.d', Sample.γ]

lemma hmat_sH (ω : Sample p bp) (pr : Bool) :
    hmat (NDim bp.n) (initDB bp J σ (unrand ω)) (sH pr) =
      padMat (NDim bp.n) (bookendRow (sMidSel pr ω) (sStarSel pr ω)) := by
  cases pr
  · change padMat (NDim bp.n) (s'Til (unrand ω)) = _
    simp [s'Til, unrand, Sample.R', sMidSel, sStarSel, Sample.s'Mid, Sample.s'Star]
  · change padMat (NDim bp.n) (sTil (unrand ω)) = _
    simp [sTil, unrand, Sample.R, sMidSel, sStarSel, Sample.sMid, Sample.sStar]

lemma hmat_tH (ω : Sample p bp) (pr : Bool) :
    hmat (NDim bp.n) (initDB bp J σ (unrand ω)) (tH pr) =
      padMat (NDim bp.n) (bookendCol (tLowSel pr ω) (tStarSel pr ω)) := by
  cases pr
  · change padMat (NDim bp.n) (t'Til (unrand ω)) = _
    simp [t'Til, unrand, Sample.R', tLowSel, tStarSel, Sample.t'Low, Sample.t'Star]
  · change padMat (NDim bp.n) (tTil (unrand ω)) = _
    simp [tTil, unrand, Sample.R, tLowSel, tStarSel, Sample.tLow, Sample.tStar]

/-- The unrandomized product along a run of step handles. -/
lemma prod_run (ω : Sample p bp) (pr : Bool) (xs : List (Fin bp.n × Bool))
    (hxs : ∀ x ∈ xs, x ∈ programSlots bp J) :
    ((xs.map (hdl bp J pr)).map (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod =
      blockDiag (xs.map fun x => dsel pr ω x.1 (act bp J σ x)).prod
        (xs.map fun x => Bsel pr ω x.1 (act bp J σ x)).prod := by
  rw [List.map_map, ← prod_blockDiag]
  congr 1
  refine List.map_congr_left fun x hx => ?_
  exact hmat_hdl ω pr (hxs x hx)

end Unrand

/-! ### The shape of colour paths, uniformly -/

section PathForm

variable {bp : BP} {J : Finset (Fin bp.ℓ)}

/-- The bookend prefix / suffix of a path. -/
def preL (hs : Bool) (pr : Bool) : List ℕ := if hs then [sH pr] else []
/-- The bookend suffix of a path. -/
def postL (ht : Bool) (pr : Bool) : List ℕ := if ht then [tH pr] else []

/-- Every colour path is an optional `s̃`, a run of step handles of one program starting at step
`i`, and an optional `t̃`; its endpoints are determined by these data. -/
theorem path_form {a b : Color} {u : List ℕ} (h : IsPath (initShapes bp J) a b u) :
    ∃ (pr hs ht : Bool) (i : ℕ) (xs : List (Fin bp.n × Bool)), IsRun bp J i xs ∧
      u = preL hs pr ++ xs.map (hdl bp J pr) ++ postL ht pr ∧
      (hs = true → i = 0) ∧ (ht = true → i + xs.length = bp.n) ∧
      a = (if hs then .src else pc pr (i + 1)) ∧
      b = (if ht then .snk else pc pr (i + 1 + xs.length)) := by
  by_cases ha : a = .src
  · subst ha
    obtain ⟨pr, u', rfl, h'⟩ := path_from_src J h
    rcases h' with ⟨rfl, rfl⟩ | h'
    · exact ⟨pr, true, false, 0, [], fun t ht => by simp at ht, by simp [preL, postL],
        fun _ => rfl, by simp, rfl, by simp⟩
    · obtain ⟨xs, hrun, hxs⟩ := path_from_step J pr u' 0 b (by simpa using h')
      rcases hxs with ⟨-, rfl, rfl⟩ | ⟨rfl, hlen, rfl⟩
      · exact ⟨pr, true, false, 0, xs, hrun, by simp [preL, postL], fun _ => rfl,
          by simp, rfl, by simp⟩
      · exact ⟨pr, true, true, 0, xs, hrun, by simp [preL, postL], fun _ => rfl,
          fun _ => hlen, rfl, rfl⟩
  · -- `a` is the left colour of the first handle, a step colour or `t̃`'s colour
    rcases u with _ | ⟨k, u'⟩
    · exact h.elim
    have hpc : ∃ pr i, a = pc pr (i + 1) := by
      obtain ⟨s, hs, hl, -⟩ := h
      rcases handle_cases J hs with ⟨pr, -, rfl⟩ | ⟨pr, -, rfl⟩ | ⟨pr, x, -, -, rfl⟩
      · exact absurd hl.symm ha
      · exact ⟨pr, bp.n, hl.symm⟩
      · rw [stepShape_eq] at hl
        exact ⟨pr, x.1.val, hl.symm⟩
    obtain ⟨pr, i, rfl⟩ := hpc
    obtain ⟨xs, hrun, hxs⟩ := path_from_step J pr (k :: u') i b h
    rcases hxs with ⟨-, hu, rfl⟩ | ⟨hu, hlen, rfl⟩
    · exact ⟨pr, false, false, i, xs, hrun, by simp [preL, postL, hu], by simp, by simp,
        by simp, by simp⟩
    · exact ⟨pr, false, true, i, xs, hrun, by simp [preL, postL, hu], by simp,
        fun _ => hlen, by simp, rfl⟩

lemma IsRun.length_le {i : ℕ} {xs : List (Fin bp.n × Bool)} (h : IsRun bp J i xs) :
    xs.length ≤ bp.n := by
  by_cases hne : xs = []
  · simp [hne]
  · have hpos := List.length_pos_iff.2 hne
    have := (h (xs.length - 1) (by omega)).2
    have hlt := (xs[xs.length - 1]'(by omega)).1.isLt
    omega

end PathForm

/-! ### The coordinate polynomial of a combination of partial paths -/

section PartialPoly

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- Decoding a handle into a program slot (`none` for the four bookends). -/
def slotOf (bp : BP) (J : Finset (Fin bp.ℓ)) (k : ℕ) : Option (Bool × (Fin bp.n × Bool)) :=
  if h : 4 ≤ k ∧ k - 4 < (programSlots bp J).length then some (true, (programSlots bp J)[k - 4])
  else if h' : 4 + (programSlots bp J).length ≤ k ∧
      k - 4 - (programSlots bp J).length < (programSlots bp J).length then
    some (false, (programSlots bp J)[k - 4 - (programSlots bp J).length])
  else none

lemma slotOf_hdl (pr : Bool) {x : Fin bp.n × Bool} (hx : x ∈ programSlots bp J) :
    slotOf bp J (hdl bp J pr x) = some (pr, x) := by
  have hi := idxOf_lt (J := J) hx
  cases pr
  · unfold slotOf
    rw [dif_neg (by simp [hdl]; omega), dif_pos (by simp [hdl]; omega)]
    simp only [hdl, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq, true_and]
    conv_rhs => rw [← List.getElem_idxOf hi]
    congr 1
    omega
  · unfold slotOf
    rw [dif_pos (by simp [hdl]; omega)]
    simp only [hdl, if_true, add_zero, Option.some.injEq, Prod.mk.injEq, true_and]
    conv_rhs => rw [← List.getElem_idxOf hi]
    congr 1
    omega

lemma slotOf_lt_four {k : ℕ} (hk : k < 4) : slotOf bp J k = none := by
  unfold slotOf
  rw [dif_neg (by omega), dif_neg (by omega)]

/-- The first middle / low coordinate. -/
def c0m (n : ℕ) : Fin (mDim n) := ⟨0, by unfold mDim; omega⟩

/-- The variable attached to a handle for the diagonal coordinate `c`. -/
def hvar (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (c : Fin (2 * mDim bp.n))
    (k : ℕ) : Coord bp :=
  match slotOf bp J k with
  | some (pr, x) => .d pr x.1 (act bp J σ x) c
  | none => if k = 0 then .sMid true (c0m bp.n) else if k = 1 then .sMid false (c0m bp.n)
      else if k = 2 then .tLow true (c0m bp.n) else .tLow false (c0m bp.n)

lemma hvar_hdl (c : Fin (2 * mDim bp.n)) (pr : Bool) {x : Fin bp.n × Bool}
    (hx : x ∈ programSlots bp J) :
    hvar bp J σ c (hdl bp J pr x) = .d pr x.1 (act bp J σ x) c := by
  simp [hvar, slotOf_hdl pr hx]

lemma hvar_sH (c : Fin (2 * mDim bp.n)) (pr : Bool) :
    hvar bp J σ c (sH pr) = .sMid pr (c0m bp.n) := by
  cases pr <;> simp [hvar, sH, slotOf_lt_four]

lemma hvar_tH (c : Fin (2 * mDim bp.n)) (pr : Bool) :
    hvar bp J σ c (tH pr) = .tLow pr (c0m bp.n) := by
  cases pr <;> simp [hvar, tH, slotOf_lt_four]

lemma coordVal_d (ω : Sample p bp) (pr : Bool) (k : Fin bp.n) (b : Bool)
    (c : Fin (2 * mDim bp.n)) : coordVal ω (.d pr k b c) = dsel pr ω k b c := by
  cases pr <;> rfl

lemma coordVal_sMid (ω : Sample p bp) (pr : Bool) (c : Fin (mDim bp.n)) :
    coordVal ω (.sMid pr c) = sMidSel pr ω c := by
  cases pr <;> rfl

lemma coordVal_tLow (ω : Sample p bp) (pr : Bool) (c : Fin (mDim bp.n)) :
    coordVal ω (.tLow pr c) = tLowSel pr ω c := by
  cases pr <;> rfl

/-- The exponent vector of a path word. -/
noncomputable def monoOf (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (c : Fin (2 * mDim bp.n)) (u : List ℕ) : Coord bp →₀ ℕ :=
  (u.map fun k => Finsupp.single (hvar bp J σ c k) 1).sum

lemma monoOf_append (c : Fin (2 * mDim bp.n)) (u v : List ℕ) :
    monoOf bp J σ c (u ++ v) = monoOf bp J σ c u + monoOf bp J σ c v := by
  simp [monoOf]

lemma prod_monoOf (ω : Sample p bp) (c : Fin (2 * mDim bp.n)) (u : List ℕ) :
    (monoOf bp J σ c u).prod (fun v e => coordVal ω v ^ e) =
      (u.map fun k => coordVal ω (hvar bp J σ c k)).prod := by
  induction u with
  | nil => simp [monoOf]
  | cons k u ih =>
    simp only [monoOf, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih]
    simp [Finsupp.prod_single_index]

lemma degree_monoOf (c : Fin (2 * mDim bp.n)) (u : List ℕ) :
    (monoOf bp J σ c u).sum (fun _ => id) = u.length := by
  induction u with
  | nil => simp [monoOf]
  | cons k u ih =>
    simp only [monoOf, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ih,
      Finsupp.sum_single_index rfl, List.length_cons]
    simp only [id_eq]
    ring

/-- The coordinate polynomial of a combination of path words. -/
noncomputable def Ppoly (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (c : Fin (2 * mDim bp.n)) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) :
    MvPolynomial (Coord bp) (ZMod p) :=
  ∑ u ∈ w.coeff.support, MvPolynomial.monomial (monoOf bp J σ c (FreeMonoid.toList u)) (w.coeff u)

lemma eval_Ppoly (ω : Sample p bp) (c : Fin (2 * mDim bp.n))
    (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) :
    MvPolynomial.eval (coordVal ω) (Ppoly bp J σ c w) =
      ∑ u ∈ w.coeff.support, w.coeff u *
        ((FreeMonoid.toList u).map fun k => coordVal ω (hvar bp J σ c k)).prod := by
  simp only [Ppoly, map_sum, MvPolynomial.eval_monomial, prod_monoOf]

/-- Exponent vectors of runs determine the runs. -/
lemma run_eq_of_mono {pr : Bool} {i : ℕ} {c : Fin (2 * mDim bp.n)}
    {xs xs' : List (Fin bp.n × Bool)} (h : IsRun bp J i xs) (h' : IsRun bp J i xs')
    (hlen : xs.length = xs'.length)
    (hm : (xs.map fun x => Finsupp.single (Coord.d pr x.1 (act bp J σ x) c) 1).sum =
      (xs'.map fun x => Finsupp.single (Coord.d pr x.1 (act bp J σ x) c) 1).sum) : xs = xs' := by
  have hmem : ∀ (ys : List (Fin bp.n × Bool)) (v : Coord bp),
      (ys.map fun x => Finsupp.single (Coord.d pr x.1 (act bp J σ x) c) 1).sum v ≠ 0 ↔
        ∃ y ∈ ys, Coord.d pr y.1 (act bp J σ y) c = v := by
    intro ys v
    induction ys with
    | nil => simp
    | cons y ys ih =>
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, Finsupp.single_apply]
      constructor
      · intro h
        by_cases hc : Coord.d pr y.1 (act bp J σ y) c = v
        · exact ⟨y, by simp, hc⟩
        · rw [if_neg hc, zero_add] at h
          obtain ⟨z, hz, hzv⟩ := ih.1 h
          exact ⟨z, List.mem_cons_of_mem _ hz, hzv⟩
      · rintro ⟨z, hz, hzv⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · rw [if_pos hzv]
          omega
        · have := ih.2 ⟨z, hz, hzv⟩
          omega
  refine List.ext_getElem hlen fun t ht ht' => ?_
  have hv : (xs'.map fun x => Finsupp.single (Coord.d pr x.1 (act bp J σ x) c) 1).sum
      (Coord.d pr xs[t].1 (act bp J σ xs[t]) c) ≠ 0 := by
    rw [← hm, hmem]
    exact ⟨xs[t], List.getElem_mem ht, rfl⟩
  rw [hmem] at hv
  obtain ⟨y, hy, hyv⟩ := hv
  obtain ⟨t', ht'', rfl⟩ := List.getElem_of_mem hy
  simp only [Coord.d.injEq] at hyv
  obtain ⟨-, h1, h2, -⟩ := hyv
  have hst : t' = t := by
    have e1 := (h t ht).2
    have e2 := (h' t' ht'').2
    have := congrArg Fin.val h1
    omega
  subst hst
  exact slot_eq_of_act σ (h t' ht).1 (h' t' ht'').1 h1.symm h2.symm

end PartialPoly

/-! ### Collision bound for partial evaluations -/

section PartialBound

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- The diagonal coordinate used for a class: `m` (first middle entry) after `s̃`, else `0`. -/
def ccoord (n : ℕ) (hs : Bool) : Fin (2 * mDim n) :=
  if hs then ⟨mDim n, by unfold mDim; omega⟩ else ⟨0, by unfold mDim; omega⟩

/-- Row index of the witnessing entry. -/
def rowIdx (n : ℕ) (hs : Bool) : Fin (NDim n) :=
  if hs then ⟨0, by unfold NDim; omega⟩ else Fin.castAdd 5 (ccoord n hs)

/-- Column index of the witnessing entry. -/
def colIdx (n : ℕ) (hs ht : Bool) : Fin (NDim n) :=
  if ht then ⟨0, by unfold NDim; omega⟩ else Fin.castAdd 5 (ccoord n hs)

lemma form_unique {n : ℕ} {pr pr' hs hs' ht ht' : Bool} {i i' L L' : ℕ}
    (hnot : ¬ (hs = true ∧ ht = true)) (h1 : hs = true → i = 0) (h1' : hs' = true → i' = 0)
    (h2 : ht = true → i + L = n) (h2' : ht' = true → i' + L' = n)
    (ha : (if hs then Color.src else pc pr (i + 1)) = (if hs' then Color.src else pc pr' (i' + 1)))
    (hb : (if ht then Color.snk else pc pr (i + 1 + L)) =
      (if ht' then Color.snk else pc pr' (i' + 1 + L'))) :
    pr = pr' ∧ hs = hs' ∧ ht = ht' ∧ i = i' ∧ L = L' := by
  cases hs <;> cases hs' <;> cases ht <;> cases ht' <;>
    simp only [if_true, if_false, Bool.false_eq_true] at ha hb
  -- (hs, hs', ht, ht') = (F,F,F,F)
  · obtain ⟨h5, h3⟩ := pc_inj ha
    obtain ⟨-, h4⟩ := pc_inj hb
    exact ⟨h5, rfl, rfl, by omega, by omega⟩
  · exact absurd hb (pc_ne_snk _ _)
  · exact absurd hb.symm (pc_ne_snk _ _)
  -- (F,F,T,T)
  · obtain ⟨h5, h3⟩ := pc_inj ha
    have e1 := h2 rfl
    have e2 := h2' rfl
    exact ⟨h5, rfl, rfl, by omega, by omega⟩
  all_goals first
    | exact absurd ha (pc_ne_src _ _)
    | exact absurd ha.symm (pc_ne_src _ _)
    | skip
  -- (T,T,F,F)
  · obtain ⟨h5, h4⟩ := pc_inj hb
    have e1 := h1 rfl
    have e2 := h1' rfl
    exact ⟨h5, rfl, rfl, by omega, by omega⟩
  · exact absurd hb (pc_ne_snk _ _)
  · exact absurd hb.symm (pc_ne_snk _ _)
  · exact absurd ⟨rfl, rfl⟩ hnot

/-- The value of the witnessing entry along a partial path. -/
lemma entry_path (ω : Sample p bp) (pr hs ht : Bool) (i : ℕ) (xs : List (Fin bp.n × Bool))
    (hrun : IsRun bp J i xs) (hnot : ¬ (hs = true ∧ ht = true)) :
    ((preL hs pr ++ xs.map (hdl bp J pr) ++ postL ht pr).map
        (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod (rowIdx bp.n hs) (colIdx bp.n hs ht) =
      ((preL hs pr ++ xs.map (hdl bp J pr) ++ postL ht pr).map
        fun k => coordVal ω (hvar bp J σ (ccoord bp.n hs) k)).prod := by
  have hxs : ∀ x ∈ xs, x ∈ programSlots bp J := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    exact (hrun t ht).1
  have hvars : (xs.map (hdl bp J pr)).map (fun k => coordVal ω (hvar bp J σ (ccoord bp.n hs) k)) =
      xs.map fun x => dsel pr ω x.1 (act bp J σ x) (ccoord bp.n hs) := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp [hvar_hdl _ pr (hxs x hx), coordVal_d]
  rcases hs with _ | _ <;> rcases ht with _ | _
  · -- run only
    simp only [preL, postL, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
    rw [prod_run ω pr xs hxs, hvars]
    simp only [rowIdx, colIdx, Bool.false_eq_true, if_false]
    rw [blockDiag_castAdd, if_pos rfl, Pi.list_prod_apply, List.map_map]
    rfl
  · -- run, then `t̃`
    simp only [preL, postL, Bool.false_eq_true, if_false, if_true, List.nil_append,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [prod_run ω pr xs hxs, hvars, hmat_tH, hvar_tH, coordVal_tLow]
    simp only [rowIdx, colIdx, Bool.false_eq_true, if_false, if_true]
    rw [blockDiag_mul_padCol, bookendCol_castAdd, Pi.list_prod_apply, List.map_map]
    simp [ccoord, c0m]
    rfl
  · -- `s̃`, then run
    simp only [preL, postL, Bool.false_eq_true, if_false, if_true, List.append_nil,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, one_mul, List.singleton_append]
    rw [prod_run ω pr xs hxs, hvars, hmat_sH, hvar_sH, coordVal_sMid]
    simp only [rowIdx, colIdx, Bool.false_eq_true, if_false, if_true]
    rw [padRow_mul_blockDiag, bookendRow_castAdd, Pi.list_prod_apply, List.map_map]
    simp [ccoord, c0m]
    rfl
  · exact absurd ⟨rfl, rfl⟩ hnot

/-- Entries of the evaluation of a formal combination. -/
lemma liftDB_apply (M : ℕ) (db : List (Record p)) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (r c : Fin M) :
    liftDB M db w r c = ∑ u ∈ w.coeff.support,
      w.coeff u * ((FreeMonoid.toList u).map (hmat M db)).prod r c := by
  simp only [liftDB, MonoidAlgebra.lift_apply, Finsupp.sum, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, FreeMonoid.lift_apply]
  rfl

variable [Fact p.Prime]

lemma card_sample_eq : Fintype.card (Sample p bp) =
    Fintype.card (Rest p bp) * Fintype.card (Coord bp → ZMod p) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_eq.2 ⟨sampleEquiv⟩

/-- **Partial evaluations.** A nonzero combination of colour paths between `a` and `b`, not from
`src` to `snk`, has a vanishing unrandomized value with probability at most `(n+1)/p`. -/
theorem partial_card_le (a b : Color) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, IsPath (initShapes bp J) a b (FreeMonoid.toList u))
    (hw0 : w ≠ 0) (hab : ¬ (a = .src ∧ b = .snk)) :
    ((Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0).card : ℝ) ≤
      (bp.n + 1) / p * Fintype.card (Sample p bp) := by
  classical
  -- a path in the support fixes the class
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ ∈ w.coeff.support := by
    by_contra hcon
    push_neg at hcon
    apply hw0
    ext u
    by_contra hu
    exact hcon u (Finsupp.mem_support_iff.2 (by simpa using hu))
  obtain ⟨pr, hs, ht, i, xs₀, hrun₀, hu₀f, hi₀, hl₀, ha₀, hb₀⟩ := path_form (hw u₀ hu₀)
  have hnot : ¬ (hs = true ∧ ht = true) := by
    rintro ⟨rfl, rfl⟩
    exact hab ⟨by simpa using ha₀, by simpa using hb₀⟩
  have hform : ∀ u ∈ w.coeff.support, ∃ xs, IsRun bp J i xs ∧ xs.length = xs₀.length ∧
      FreeMonoid.toList u = preL hs pr ++ xs.map (hdl bp J pr) ++ postL ht pr := by
    intro u hu
    obtain ⟨pr', hs', ht', i', xs, hrun, huf, hi, hl, ha, hb⟩ := path_form (hw u hu)
    obtain ⟨rfl, rfl, rfl, rfl, hlen⟩ := form_unique hnot hi₀ hi hl₀ hl (ha₀.symm.trans ha)
      (hb₀.symm.trans hb)
    exact ⟨xs, hrun, hlen.symm, huf⟩
  set c := ccoord bp.n hs
  set P := Ppoly bp J σ c w
  -- the witnessing entry is the evaluation of `P`
  have hentry : ∀ ω : Sample p bp,
      liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w (rowIdx bp.n hs) (colIdx bp.n hs ht) =
        MvPolynomial.eval (coordVal ω) P := by
    intro ω
    rw [liftDB_apply, eval_Ppoly]
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨xs, hrun, -, huf⟩ := hform u hu
    rw [huf, entry_path ω pr hs ht i xs hrun hnot]
  -- `P` is nonzero: distinct paths of the class have distinct exponent vectors
  have hinj : ∀ u ∈ w.coeff.support, ∀ u' ∈ w.coeff.support,
      monoOf bp J σ c (FreeMonoid.toList u) = monoOf bp J σ c (FreeMonoid.toList u') → u = u' := by
    intro u hu u' hu' hm
    obtain ⟨xs, hrun, hlen, huf⟩ := hform u hu
    obtain ⟨xs', hrun', hlen', huf'⟩ := hform u' hu'
    rw [huf, huf', monoOf_append, monoOf_append, monoOf_append, monoOf_append] at hm
    have hm' := add_left_cancel (add_right_cancel hm)
    have hrunm : ∀ ys : List (Fin bp.n × Bool), IsRun bp J i ys →
        monoOf bp J σ c (ys.map (hdl bp J pr)) =
          (ys.map fun x => Finsupp.single (Coord.d pr x.1 (act bp J σ x) c) 1).sum := by
      intro ys hys
      simp only [monoOf, List.map_map]
      congr 1
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      simp [hvar_hdl c pr (hys t ht).1]
    rw [hrunm xs hrun, hrunm xs' hrun'] at hm'
    have := run_eq_of_mono hrun hrun' (hlen.trans hlen'.symm) hm'
    apply FreeMonoid.toList.injective
    rw [huf, huf', this]
  have hP0 : P ≠ 0 := by
    intro hP
    have hc := congrArg (MvPolynomial.coeff (monoOf bp J σ c (FreeMonoid.toList u₀))) hP
    rw [MvPolynomial.coeff_zero] at hc
    simp only [P, Ppoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
    rw [Finset.sum_eq_single u₀ (fun u hu hne => by
        rw [if_neg (fun h => hne (hinj u hu u₀ hu₀ h))])
      (fun h => absurd hu₀ h), if_pos rfl] at hc
    exact (Finsupp.mem_support_iff.1 hu₀) hc
  have hdeg : P.totalDegree ≤ bp.n + 1 := by
    refine MvPolynomial.totalDegree_finsetSum_le fun u hu => ?_
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    rw [degree_monoOf]
    obtain ⟨xs, hrun, -, huf⟩ := hform u hu
    rw [huf]
    have := hrun.length_le
    rcases hs with _ | _ <;> rcases ht with _ | _ <;>
      simp [preL, postL] <;> first | omega | exact absurd ⟨rfl, rfl⟩ hnot
  -- counting
  have hsub : (Finset.univ.filter fun ω : Sample p bp =>
      liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0) ⊆
      Finset.univ.filter fun ω : Sample p bp => MvPolynomial.eval (coordVal ω) P = 0 := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [← hentry, hω]
    rfl
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc ((Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0).card : ℝ)
      ≤ (Finset.univ.filter fun ω : Sample p bp =>
          MvPolynomial.eval (coordVal ω) P = 0).card := by exact_mod_cast Finset.card_le_card hsub
    _ = Fintype.card (Rest p bp) *
          ((Finset.univ.filter fun z : Coord bp → ZMod p => MvPolynomial.eval z P = 0).card : ℝ) := by
        rw [card_filter_coord (fun z => MvPolynomial.eval z P = 0)]
        push_cast
        rfl
    _ ≤ Fintype.card (Rest p bp) * (P.totalDegree / p * Fintype.card (Coord bp → ZMod p)) := by
        gcongr
        exact sz_coord P hP0
    _ ≤ Fintype.card (Rest p bp) * ((bp.n + 1) / p * Fintype.card (Coord bp → ZMod p)) := by
        gcongr
        exact_mod_cast hdeg
    _ = (bp.n + 1) / p * Fintype.card (Sample p bp) := by
        rw [card_sample_eq]
        push_cast
        ring

end PartialBound

/-! ### Partial shapes: identical equality is equality of formal words -/

instance instNonemptySampleC (p : ℕ) [Fact p.Prime] (bp : BP) : Nonempty (Sample p bp) :=
  ⟨(fun _ => 1, fun _ => 1, fun _ _ _ => 0, fun _ _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ⟨(0, 0, 0, 0), by simp⟩, fun _ _ _ => 0)⟩

section PartialShapes

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma word_sub_support {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) :
    ∀ u ∈ (word e - word e').coeff.support,
      IsPath (initShapes bp J) s.2.2.1 s.2.2.2 (FreeMonoid.toList u) := by
  intro u hu
  rw [MonoidAlgebra.coeff_sub] at hu
  rcases Finset.mem_union.1 (Finsupp.support_sub hu) with hu | hu
  · exact word_support e s hs u hu
  · exact word_support e' s hs' u hu

open Classical in
lemma filter_eval_eq {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) :
    (Finset.univ.filter fun ω : Sample p bp =>
        e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω)) =
      Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) (word e - word e') = 0 := by
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eval_eq_iff ω hs hs'

/-- For partial shapes and `p > n + 1`, two expressions are identically equal exactly when their
formal words agree (in particular, independently of `σ`). -/
theorem idEq_iff_word_eq {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) (hpart : ¬ (s.2.2.1 = .src ∧ s.2.2.2 = .snk))
    (hp : bp.n + 1 < p) :
    IdenticallyEqual bp J σ e e' ↔ word e = word e' := by
  classical
  constructor
  · intro hid
    by_contra hne
    have hw0 : word e - word e' ≠ 0 := sub_ne_zero.2 hne
    have hbound := partial_card_le (J := J) (σ := σ) s.2.2.1 s.2.2.2 _
      (word_sub_support hs hs') hw0 hpart
    have hall : (Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) (word e - word e') = 0) =
        Finset.univ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact (eval_eq_iff ω hs hs').1 (hid ω)
    rw [hall, Finset.card_univ] at hbound
    have hΩ : (0 : ℝ) < Fintype.card (Sample p bp) := by
      exact_mod_cast Fintype.card_pos_iff.2 (instNonemptySampleC p bp)
    have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hlt : ((bp.n : ℝ) + 1) / p < 1 := by
      rw [div_lt_one hpR]
      exact_mod_cast hp
    nlinarith
  · intro hw ω
    rw [eval_eq_iff ω hs hs', hw, sub_self, map_zero]

end PartialShapes

/-! ### Blocks and positions -/

section Blocks

variable {bp : BP}

lemma pos_lt_blockSize (i : Fin bp.n) : pos bp i < blockSize bp (bp.inp i) := by
  unfold pos blockSize BP.block
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  · have := h (show i ∈ Finset.univ.filter fun i' => bp.inp i' = bp.inp i by simp)
    simp at this

lemma blockSize_le (j : Fin bp.ℓ) : blockSize bp j ≤ bp.n := by
  unfold blockSize BP.block
  calc _ ≤ (Finset.univ : Finset (Fin bp.n)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = bp.n := by simp

lemma blockSize_pos (i : Fin bp.n) : 0 < blockSize bp (bp.inp i) :=
  lt_of_le_of_lt (Nat.zero_le _) (pos_lt_blockSize i)

lemma pos_strictMono {i i' : Fin bp.n} (hb : bp.inp i = bp.inp i') (h : i < i') :
    pos bp i < pos bp i' := by
  unfold pos
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans h, hx.2.trans hb⟩
  · have := hsub (show i ∈ Finset.univ.filter fun x => x < i' ∧ bp.inp x = bp.inp i' by
      simp [h, hb])
    simp at this

lemma pos_inj {i i' : Fin bp.n} (hb : bp.inp i = bp.inp i') (h : pos bp i = pos bp i') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (pos_strictMono hb hlt).ne
  · exact heq
  · exact absurd h (pos_strictMono hb.symm hgt).ne'

lemma pos_surj (i : Fin bp.n) {r : ℕ} (hr : r < blockSize bp (bp.inp i)) :
    ∃ i', bp.inp i' = bp.inp i ∧ pos bp i' = r := by
  classical
  set B := bp.block (bp.inp i)
  have himg : B.image (pos bp) = Finset.range (blockSize bp (bp.inp i)) := by
    refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
    · obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 hr
      simp only [B, BP.block, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      rw [Finset.mem_range, ← hi']
      exact pos_lt_blockSize i'
    · rw [Finset.card_range, Finset.card_image_of_injOn]
      · rfl
      · intro a ha b hb hab
        simp only [B, BP.block, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at ha hb
        exact pos_inj (ha.trans hb.symm) hab
  have : r ∈ B.image (pos bp) := by rw [himg]; exact Finset.mem_range.2 hr
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 this
  simp only [B, BP.block, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  exact ⟨i', hi', rfl⟩

lemma two_pos_succ_lt (i : Fin bp.n) : 2 * pos bp i + 1 < 2 * bp.n := by
  have := pos_lt_blockSize i
  have := blockSize_le (bp.inp i)
  omega

lemma mod_two_block_lt (i : Fin bp.n) :
    (2 * pos bp i + 2) % (2 * blockSize bp (bp.inp i)) < 2 * bp.n := by
  have h1 := blockSize_pos i
  have h2 := blockSize_le (bp.inp i)
  have := Nat.mod_lt (2 * pos bp i + 2) (show 0 < 2 * blockSize bp (bp.inp i) by omega)
  omega

end Blocks

/-! ### The bundling scalars as monomials in the γ's -/

section Bundling

variable {bp : BP}

/-- The first γ-index of the bundling scalar of step `i` (`2r` primal, `2r+1` dummy). -/
def gidx1 (pr : Bool) (i : Fin bp.n) : Fin (2 * bp.n) :=
  if pr then ⟨2 * pos bp i, by have := two_pos_succ_lt i; omega⟩ else ⟨2 * pos bp i + 1, two_pos_succ_lt i⟩

/-- The second γ-index (`2r+1` primal, `(2r+2) mod 2k` dummy). -/
def gidx2 (pr : Bool) (i : Fin bp.n) : Fin (2 * bp.n) :=
  if pr then ⟨2 * pos bp i + 1, two_pos_succ_lt i⟩
  else ⟨(2 * pos bp i + 2) % (2 * blockSize bp (bp.inp i)), mod_two_block_lt i⟩

/-- Exponent vector of the bundling scalar `α_{i,b}` (primal) or `α′_{i,b}` (dummy). -/
noncomputable def gexpStep (pr : Bool) (i : Fin bp.n) (b : Bool) : Coord bp →₀ ℕ :=
  Finsupp.single (.γ (bp.inp i) b (gidx1 pr i)) 1 + Finsupp.single (.γ (bp.inp i) b (gidx2 pr i)) 1

/-- The bundling scalar of a program. -/
def alphaSel (pr : Bool) (ω : Sample p bp) (i : Fin bp.n) (b : Bool) : ZMod p :=
  if pr then alpha bp ω.γ i b else alpha' bp ω.γ i b

lemma alphaSel_eq (pr : Bool) (ω : Sample p bp) (i : Fin bp.n) (b : Bool) :
    alphaSel pr ω i b = (gexpStep pr i b).prod fun v e => coordVal ω v ^ e := by
  rw [gexpStep, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod_single_index, pow_zero, pow_one]
  cases pr
  · simp only [alphaSel, Bool.false_eq_true, if_false, alpha', gam, gidx1, gidx2, coordVal]
    rw [dif_pos (two_pos_succ_lt i), dif_pos (mod_two_block_lt i)]
  · simp only [alphaSel, if_true, alpha, gam, gidx1, gidx2, coordVal]
    rw [dif_pos (by have := two_pos_succ_lt i; omega), dif_pos (two_pos_succ_lt i)]

end Bundling

/-! ### The straddling structure of the bundling monomials -/

section Straddling

variable {bp : BP}

/-- Exponent vector of `∏_t α_{t, β_t}` (primal) or `∏_t α′_{t, β_t}` (dummy). -/
noncomputable def gexp (pr : Bool) (β : Fin bp.n → Bool) : Coord bp →₀ ℕ :=
  ∑ t : Fin bp.n, gexpStep pr t (β t)

/-- Consistency of a bit assignment along the steps: equal bits on every block. -/
def Consistent (β : Fin bp.n → Bool) : Prop := ∀ t t', bp.inp t = bp.inp t' → β t = β t'

lemma gexpStep_apply (pr : Bool) (i : Fin bp.n) (b : Bool) (v : Coord bp) :
    gexpStep pr i b v = (if Coord.γ (bp.inp i) b (gidx1 pr i) = v then 1 else 0) +
      (if Coord.γ (bp.inp i) b (gidx2 pr i) = v then 1 else 0) := by
  simp [gexpStep, Finsupp.single_apply]

lemma exists_of_gexp_ne_zero {pr : Bool} {β : Fin bp.n → Bool} {v : Coord bp}
    (h : gexp pr β v ≠ 0) :
    ∃ t, Coord.γ (bp.inp t) (β t) (gidx1 pr t) = v ∨ Coord.γ (bp.inp t) (β t) (gidx2 pr t) = v := by
  simp only [gexp, Finsupp.finset_sum_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [gexpStep_apply] at ht
  refine ⟨t, ?_⟩
  by_contra hcon
  push_neg at hcon
  rw [if_neg hcon.1, if_neg hcon.2] at ht
  exact ht rfl

lemma gexp_ne_zero_of₁ {pr : Bool} {β : Fin bp.n → Bool} (t : Fin bp.n) :
    gexp pr β (Coord.γ (bp.inp t) (β t) (gidx1 pr t)) ≠ 0 := by
  simp only [gexp, Finsupp.finset_sum_apply]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ t)))
  rw [gexpStep_apply]
  simp

lemma gexp_ne_zero_of₂ {pr : Bool} {β : Fin bp.n → Bool} (t : Fin bp.n) :
    gexp pr β (Coord.γ (bp.inp t) (β t) (gidx2 pr t)) ≠ 0 := by
  simp only [gexp, Finsupp.finset_sum_apply]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ t)))
  rw [gexpStep_apply]
  simp

lemma gidx1_true (i : Fin bp.n) : (gidx1 true i).val = 2 * pos bp i := rfl
lemma gidx2_true (i : Fin bp.n) : (gidx2 true i).val = 2 * pos bp i + 1 := rfl
lemma gidx1_false (i : Fin bp.n) : (gidx1 false i).val = 2 * pos bp i + 1 := rfl
lemma gidx2_false (i : Fin bp.n) :
    (gidx2 false i).val = (2 * pos bp i + 2) % (2 * blockSize bp (bp.inp i)) := rfl

lemma mod_even (r k : ℕ) : ((2 * r + 2) % (2 * k)) % 2 = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.mod_mod_of_dvd _ (Dvd.intro k rfl)]
    omega

/-- Decoding a γ-coordinate shared by two steps. -/
lemma gamma_coord_eq {j j' : Fin bp.ℓ} {b b' : Bool} {x x' : Fin (2 * bp.n)}
    (h : Coord.γ (bp := bp) j b x = Coord.γ j' b' x') : j = j' ∧ b = b' ∧ x.val = x'.val := by
  simp only [Coord.γ.injEq] at h
  exact ⟨h.1, h.2.1, congrArg Fin.val h.2.2⟩

/-- Same program: the bundling monomial determines the bits. -/
theorem gexp_inj {pr : Bool} {β β' : Fin bp.n → Bool} (h : gexp pr β = gexp pr β') : β = β' := by
  funext t
  cases pr
  · -- dummy: the odd index `2r+1` occurs only as a first index
    have hv := gexp_ne_zero_of₁ (pr := false) (β := β) t
    rw [h] at hv
    obtain ⟨t', ht'⟩ := exists_of_gexp_ne_zero hv
    have hpar := mod_even (pos bp t') (blockSize bp (bp.inp t'))
    rcases ht' with h' | h' <;> obtain ⟨hb, hbit, hidx⟩ := gamma_coord_eq h'
    · rw [gidx1_false, gidx1_false] at hidx
      rw [pos_inj hb (by omega)] at hbit
      exact hbit.symm
    · rw [gidx2_false, gidx1_false] at hidx
      omega
  · -- primal: the even index `2r` occurs only as a first index
    have hv := gexp_ne_zero_of₁ (pr := true) (β := β) t
    rw [h] at hv
    obtain ⟨t', ht'⟩ := exists_of_gexp_ne_zero hv
    rcases ht' with h' | h' <;> obtain ⟨hb, hbit, hidx⟩ := gamma_coord_eq h'
    · rw [gidx1_true, gidx1_true] at hidx
      rw [pos_inj hb (by omega)] at hbit
      exact hbit.symm
    · rw [gidx2_true, gidx1_true] at hidx
      omega

/-- Primal against dummy: equal bundling monomials force equal and consistent bits. -/
theorem gexp_cross {β β' : Fin bp.n → Bool} (h : gexp true β = gexp false β') :
    β = β' ∧ Consistent (bp := bp) β := by
  -- odd indices: the bits agree
  have hbb : β = β' := by
    funext t
    have hv := gexp_ne_zero_of₂ (pr := true) (β := β) t
    rw [h] at hv
    obtain ⟨t', ht'⟩ := exists_of_gexp_ne_zero hv
    have hpar := mod_even (pos bp t') (blockSize bp (bp.inp t'))
    rcases ht' with h' | h' <;> obtain ⟨hb, hbit, hidx⟩ := gamma_coord_eq h'
    · rw [gidx1_false, gidx2_true] at hidx
      rw [pos_inj hb (by omega)] at hbit
      exact hbit.symm
    · rw [gidx2_false, gidx2_true] at hidx
      omega
  subst hbb
  refine ⟨rfl, ?_⟩
  -- even indices: the bit at position `r ≥ 1` equals the one at position `r - 1`
  have hstep : ∀ t : Fin bp.n, 1 ≤ pos bp t → ∃ t', bp.inp t' = bp.inp t ∧
      pos bp t' + 1 = pos bp t ∧ β t' = β t := by
    intro t ht
    have hv := gexp_ne_zero_of₁ (pr := true) (β := β) t
    rw [h] at hv
    obtain ⟨t', ht'⟩ := exists_of_gexp_ne_zero hv
    have hlt := pos_lt_blockSize t'
    rcases ht' with h' | h' <;> obtain ⟨hb, hbit, hidx⟩ := gamma_coord_eq h'
    · rw [gidx1_false, gidx1_true] at hidx
      omega
    · rw [gidx2_false, gidx1_true] at hidx
      refine ⟨t', hb, ?_, hbit⟩
      by_cases hk : pos bp t' + 1 < blockSize bp (bp.inp t')
      · rw [Nat.mod_eq_of_lt (by omega)] at hidx
        omega
      · rw [show 2 * pos bp t' + 2 = 2 * blockSize bp (bp.inp t') by omega, Nat.mod_self] at hidx
        omega
  -- every step of a block has the bit of the block's position-0 step
  have hall : ∀ r : ℕ, ∀ t t₀ : Fin bp.n, bp.inp t = bp.inp t₀ → pos bp t₀ = 0 →
      pos bp t = r → β t = β t₀ := by
    intro r
    induction r with
    | zero =>
      intro t t₀ hb h0 hr
      rw [pos_inj hb (hr.trans h0.symm)]
    | succ r ih =>
      intro t t₀ hb h0 hr
      obtain ⟨t', hb', hpos, hbit⟩ := hstep t (by omega)
      rw [← hbit]
      exact ih t' t₀ (hb'.trans hb) h0 (by omega)
  intro t t' hb
  obtain ⟨t₀, hb₀, h0⟩ := pos_surj t (blockSize_pos t)
  rw [hall _ t t₀ hb₀.symm h0 rfl, hall _ t' t₀ (hb.symm.trans hb₀.symm) h0 rfl]

/-- The successor of a step within its block (cyclically). -/
noncomputable def blockSucc (t : Fin bp.n) : Fin bp.n :=
  Classical.choose (pos_surj t (r := (pos bp t + 1) % blockSize bp (bp.inp t))
    (Nat.mod_lt _ (blockSize_pos t)))

lemma blockSucc_spec (t : Fin bp.n) : bp.inp (blockSucc t) = bp.inp t ∧
    pos bp (blockSucc t) = (pos bp t + 1) % blockSize bp (bp.inp t) :=
  Classical.choose_spec (pos_surj t (r := (pos bp t + 1) % blockSize bp (bp.inp t))
    (Nat.mod_lt _ (blockSize_pos t)))

lemma blockSucc_injective : Function.Injective (blockSucc (bp := bp)) := by
  intro t t' h
  obtain ⟨h1, h2⟩ := blockSucc_spec t
  obtain ⟨h1', h2'⟩ := blockSucc_spec t'
  have hb : bp.inp t = bp.inp t' := by rw [← h1, ← h1', h]
  have hk := pos_lt_blockSize t
  have hk' := pos_lt_blockSize t'
  have hmod : (pos bp t + 1) % blockSize bp (bp.inp t) =
      (pos bp t' + 1) % blockSize bp (bp.inp t) := by
    rw [← h2, h, h2', hb]
  rw [← hb] at hk'
  refine pos_inj hb ?_
  by_cases ha : pos bp t + 1 < blockSize bp (bp.inp t) <;>
    by_cases hb' : pos bp t' + 1 < blockSize bp (bp.inp t)
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb'] at hmod
    omega
  · rw [Nat.mod_eq_of_lt ha, show pos bp t' + 1 = blockSize bp (bp.inp t) by omega,
      Nat.mod_self] at hmod
    omega
  · rw [Nat.mod_eq_of_lt hb', show pos bp t + 1 = blockSize bp (bp.inp t) by omega,
      Nat.mod_self] at hmod
    omega
  · omega

/-- Shifting positions cyclically within blocks: the even γ-indices `2r` of the primal monomial
are the indices `(2r+2) mod 2k` of the dummy one. -/
lemma sum_even_shift {β : Fin bp.n → Bool} (hβ : Consistent (bp := bp) β) :
    ∑ t : Fin bp.n, Finsupp.single (Coord.γ (bp.inp t) (β t) (gidx1 true t)) 1 =
      ∑ t : Fin bp.n, Finsupp.single (Coord.γ (bp.inp t) (β t) (gidx2 false t)) 1 := by
  have hbij : Function.Bijective (blockSucc (bp := bp)) :=
    (Finite.injective_iff_bijective).1 blockSucc_injective
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbij)
    (fun t => Finsupp.single (Coord.γ (bp.inp t) (β t) (gidx1 true t)) (1 : ℕ))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.ofBijective_apply]
  obtain ⟨h1, h2⟩ := blockSucc_spec t
  have hidx : gidx1 true (blockSucc t) = gidx2 false t := by
    ext
    rw [gidx1_true, gidx2_false, h2]
    have := blockSize_pos t
    have := pos_lt_blockSize t
    by_cases ha : pos bp t + 1 < blockSize bp (bp.inp t)
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]
      all_goals ring
    · rw [show pos bp t + 1 = blockSize bp (bp.inp t) by omega, Nat.mod_self,
        show 2 * pos bp t + 2 = 2 * blockSize bp (bp.inp t) by omega, Nat.mod_self]
  rw [hidx, hβ (blockSucc t) t h1, h1]

/-- Consistent bits give the same monomial in both programs (the γ-procedure of p. 42). -/
theorem gexp_consistent {β : Fin bp.n → Bool} (hβ : Consistent (bp := bp) β) :
    gexp true β = gexp false β := by
  unfold gexp
  simp only [gexpStep, Finset.sum_add_distrib]
  rw [sum_even_shift hβ, add_comm]
  rfl

end Straddling

/-! ### The value of a full evaluation -/

section FullValue

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma padMat_row_apply {N : ℕ} (R : Matrix (Fin 1) (Fin N) (ZMod p)) (hN : 0 < N) (k : Fin N) :
    padMat N R ⟨0, hN⟩ k = R 0 k := by
  simp [padMat]

lemma padMat_col_apply {N : ℕ} (C : Matrix (Fin N) (Fin 1) (ZMod p)) (hN : 0 < N) (k : Fin N) :
    padMat N C k ⟨0, hN⟩ = C k 0 := by
  simp [padMat]

lemma pad_triple_apply {N : ℕ} (R : Matrix (Fin 1) (Fin N) (ZMod p))
    (M : Matrix (Fin N) (Fin N) (ZMod p)) (C : Matrix (Fin N) (Fin 1) (ZMod p)) (hN : 0 < N) :
    (padMat N R * M * padMat N C) ⟨0, hN⟩ ⟨0, hN⟩ = ∑ k, ∑ l, R 0 k * M k l * C l 0 := by
  simp only [Matrix.mul_apply, padMat_row_apply _ hN, padMat_col_apply _ hN, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The `(0,0)` entry of `s · blockDiag(d, B) · t` for bookend vectors: the random diagonal
cancels and only `s* B t*` survives. -/
lemma bookend_triple {m : ℕ} (mid low : Fin m → ZMod p) (star star' : Fin 5 → ZMod p)
    (d : Fin (2 * m) → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    (padMat (2 * m + 5) (bookendRow mid star) * blockDiag d B *
      padMat (2 * m + 5) (bookendCol low star')) ⟨0, by omega⟩ ⟨0, by omega⟩ =
      star ⬝ᵥ (B *ᵥ star') := by
  rw [pad_triple_apply]
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, blockDiag_castAdd, blockDiag_natAdd_castAdd,
    blockDiag_castAdd_natAdd, blockDiag_natAdd, bookendRow_natAdd, bookendCol_natAdd,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  have h0 : ∀ c : Fin (2 * m), ∑ x : Fin (2 * m),
      bookendRow mid star 0 (Fin.castAdd 5 c) * (if c = x then d c else 0) *
        bookendCol low star' (Fin.castAdd 5 x) 0 = 0 := by
    intro c
    rw [Finset.sum_eq_single c (fun x _ hx => by simp [Ne.symm hx])
      (by simp), if_pos rfl, bookendRow_castAdd, bookendCol_castAdd]
    split_ifs <;> simp
  simp only [h0, Finset.sum_const_zero, zero_add, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `∏ (a_x • M_x) = (∏ a_x) • ∏ M_x` for scalars and matrices. -/
lemma list_prod_smul {α : Type} (l : List α) (a : α → ZMod p)
    (M : α → Matrix (Fin 5) (Fin 5) (ZMod p)) :
    (l.map fun x => a x • M x).prod = (l.map a).prod • (l.map M).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih, smul_mul_smul_comm]

/-- The permutation product of a run (primal) or the identity (dummy). -/
def piSel (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (pr : Bool)
    (xs : List (Fin bp.n × Bool)) : Matrix (Fin 5) (Fin 5) (ZMod p) :=
  if pr then (xs.map fun x => (bp.A x.1 (act bp J σ x)).permMatrix (ZMod p)).prod else 1

lemma prod_Bsel (ω : Sample p bp) (pr : Bool) (xs : List (Fin bp.n × Bool)) :
    (xs.map fun x => Bsel pr ω x.1 (act bp J σ x)).prod =
      (xs.map fun x => alphaSel pr ω x.1 (act bp J σ x)).prod • piSel bp J σ pr xs := by
  cases pr
  · simp only [Bsel, alphaSel, piSel, Bool.false_eq_true, if_false]
    rw [list_prod_smul]
    simp
  · simp only [Bsel, alphaSel, piSel, if_true]
    exact list_prod_smul _ _ _

/-- The unrandomized value of the full path `s̃ D̃… t̃` (or its dummy version) along a run. -/
theorem entry_full (ω : Sample p bp) (pr : Bool) (xs : List (Fin bp.n × Bool))
    (hxs : ∀ x ∈ xs, x ∈ programSlots bp J) :
    (([sH pr] ++ xs.map (hdl bp J pr) ++ [tH pr]).map
        (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod
      ⟨0, by unfold NDim; omega⟩ ⟨0, by unfold NDim; omega⟩ =
      (xs.map fun x => alphaSel pr ω x.1 (act bp J σ x)).prod *
        (sStarSel pr ω ⬝ᵥ (piSel bp J σ pr xs *ᵥ tStarSel pr ω)) := by
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [prod_run ω pr xs hxs, hmat_sH, hmat_tH, prod_Bsel, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  rw [bookend_triple]
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end FullValue

/-! ### Full evaluations: the bookend 5-vectors -/

section BookendProb

/-- `s*` of a bookend quadruple. -/
def sS (bk : Bookends p) : Fin 5 → ZMod p := bk.1.1
/-- `t*`. -/
def tS (bk : Bookends p) : Fin 5 → ZMod p := bk.1.2.1
/-- `s*′`. -/
def s'S (bk : Bookends p) : Fin 5 → ZMod p := bk.1.2.2.1
/-- `t*′`. -/
def t'S (bk : Bookends p) : Fin 5 → ZMod p := bk.1.2.2.2

lemma bookends_dot (bk : Bookends p) : sS bk ⬝ᵥ tS bk = s'S bk ⬝ᵥ t'S bk := bk.2

/-- Coefficient data whose bookend scalar is not identically zero. -/
def GoodCoef (P : Equiv.Perm (Fin 5)) (c c' : ZMod p) : Prop :=
  (P ≠ 1 ∧ ¬ (c = 0 ∧ c' = 0)) ∨ (P = 1 ∧ c + c' ≠ 0)

variable [Fact p.Prime]

/-- Counting over the constrained bookend vectors is counting over the filter `S` of the
consistent-display lemma. -/
lemma card_bookends_filter (Q : ((Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
      (Fin 5 → ZMod p)) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun bk : Bookends p => Q bk.1).card =
      ((Finset.univ.filter fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) => x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2).filter Q).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨bk, hbk, rfl⟩
    exact ⟨bk.2, hbk⟩
  · rintro ⟨hx, hq⟩
    exact ⟨⟨x, hx⟩, hq, rfl⟩

open Classical in
lemma card_bookends :
    Fintype.card (Bookends p) =
      (Finset.univ.filter fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) => x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2).card := by
  rw [Fintype.card_subtype]

open Classical in
/-- **The bookend estimate.** For good coefficients, the bookend scalar
`c · s* P t* + c′ · ⟨s*′, t*′⟩` vanishes with probability below `2/p`. -/
theorem bookend_card_le (P : Equiv.Perm (Fin 5)) (c c' : ZMod p) (hg : GoodCoef P c c') :
    ((Finset.univ.filter fun bk : Bookends p =>
        c * (sS bk ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ tS bk)) + c' * (s'S bk ⬝ᵥ t'S bk) = 0).card : ℝ) ≤
      2 / p * Fintype.card (Bookends p) := by
  have hSpos : (0 : ℝ) < Fintype.card (Bookends p) := by
    have : Nonempty (Bookends p) := ⟨⟨(0, 0, 0, 0), by simp⟩⟩
    exact_mod_cast Fintype.card_pos
  rcases hg with ⟨hP, hc⟩ | ⟨rfl, hc⟩
  · have h := (consistent_display p P hP c c' hc).2
    try simp only at h
    rw [← card_bookends, div_lt_iff₀ hSpos] at h
    have heq : (Finset.univ.filter fun bk : Bookends p =>
        c * (sS bk ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ tS bk)) + c' * (s'S bk ⬝ᵥ t'S bk) = 0).card =
        ((Finset.univ.filter fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) => x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2).filter fun x =>
            c' * (x.2.2.1 ⬝ᵥ x.2.2.2) + c * (x.1 ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ x.2.1)) = 0).card := by
      rw [← card_bookends_filter (fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) × (Fin 5 → ZMod p) =>
          c' * (x.2.2.1 ⬝ᵥ x.2.2.2) + c * (x.1 ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ x.2.1)) = 0)]
      refine congrArg Finset.card (Finset.filter_congr fun bk _ => ?_)
      simp only [sS, tS, s'S, t'S]
      exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
    rw [heq]
    convert h.le using 2
  · -- identity permutation: the scalar is `(c + c') ⟨s*′, t*′⟩`
    have hP0 : (Equiv.swap (0 : Fin 5) 1) ≠ 1 := by
      intro h
      have := congrArg (fun f : Equiv.Perm (Fin 5) => f 0) h
      simp at this
    have h := (consistent_display p (Equiv.swap 0 1) hP0 0 1 (by simp)).2
    try simp only at h
    rw [← card_bookends, div_lt_iff₀ hSpos] at h
    have heq : (Finset.univ.filter fun bk : Bookends p =>
        c * (sS bk ⬝ᵥ ((1 : Equiv.Perm (Fin 5)).permMatrix (ZMod p) *ᵥ tS bk)) +
          c' * (s'S bk ⬝ᵥ t'S bk) = 0).card =
        ((Finset.univ.filter fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) => x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2).filter fun x =>
            1 * (x.2.2.1 ⬝ᵥ x.2.2.2) +
              0 * (x.1 ⬝ᵥ ((Equiv.swap (0 : Fin 5) 1).permMatrix (ZMod p) *ᵥ x.2.1)) = 0).card := by
      rw [← card_bookends_filter (fun x : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) ×
          (Fin 5 → ZMod p) × (Fin 5 → ZMod p) =>
          1 * (x.2.2.1 ⬝ᵥ x.2.2.2) +
            0 * (x.1 ⬝ᵥ ((Equiv.swap (0 : Fin 5) 1).permMatrix (ZMod p) *ᵥ x.2.1)) = 0)]
      refine congrArg Finset.card (Finset.filter_congr fun bk _ => ?_)
      simp only [sS, tS, s'S, t'S, Matrix.permMatrix_one, Matrix.one_mulVec, one_mul, zero_mul,
        add_zero]
      rw [show bk.1.1 ⬝ᵥ bk.1.2.1 = bk.1.2.2.1 ⬝ᵥ bk.1.2.2.2 from bk.2, ← add_mul]
      constructor
      · intro h0
        exact (mul_eq_zero.1 h0).resolve_left hc
      · intro h0
        rw [h0, mul_zero]
    rw [heq]
    convert h.le using 2

end BookendProb

/-! ### Full evaluations: runs over all steps -/

section FullRuns

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- A run covering all steps `0, …, n-1`. -/
def IsFullRun (bp : BP) (J : Finset (Fin bp.ℓ)) (xs : List (Fin bp.n × Bool)) : Prop :=
  IsRun bp J 0 xs ∧ xs.length = bp.n

/-- The full path word `s̃ D̃_{0,·} ⋯ D̃_{n-1,·} t̃` (or its dummy version) of a run. -/
def fullWord (bp : BP) (J : Finset (Fin bp.ℓ)) (pr : Bool) (xs : List (Fin bp.n × Bool)) :
    List ℕ :=
  [sH pr] ++ xs.map (hdl bp J pr) ++ [tH pr]

/-- The actual bits along a run. -/
def betaOf (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (xs : List (Fin bp.n × Bool)) (t : Fin bp.n) : Bool :=
  match xs[t.val]? with
  | some x => act bp J σ x
  | none => false

lemma IsFullRun.getElem {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs) (t : Fin bp.n) :
    ∃ x, xs[t.val]? = some x ∧ x ∈ programSlots bp J ∧ x.1 = t := by
  have ht : t.val < xs.length := by rw [h.2]; exact t.isLt
  refine ⟨xs[t.val], List.getElem?_eq_getElem ht, (h.1 t.val ht).1, Fin.ext ?_⟩
  simpa using (h.1 t.val ht).2

lemma betaOf_eq {xs : List (Fin bp.n × Bool)} {t : Fin bp.n} {x : Fin bp.n × Bool}
    (hx : xs[t.val]? = some x) : betaOf bp J σ xs t = act bp J σ x := by
  simp [betaOf, hx]

lemma IsFullRun.mem {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs) :
    ∀ x ∈ xs, x ∈ programSlots bp J := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
  exact (h.1 t ht).1

/-- Sums along a full run are sums over the steps. -/
lemma sum_fullRun {M : Type} [AddCommMonoid M] {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) (g : Fin bp.n → Bool → M) :
    (xs.map fun x => g x.1 (act bp J σ x)).sum = ∑ t : Fin bp.n, g t (betaOf bp J σ xs t) := by
  conv_lhs => rw [← List.ofFn_getElem (xs := xs), List.map_ofFn, List.sum_ofFn]
  refine Fintype.sum_equiv (finCongr h.2) _ _ fun i => ?_
  obtain ⟨x, hx, -, hx1⟩ := h.getElem (finCongr h.2 i)
  have hxi : xs[i.val] = x := by
    simpa [List.getElem?_eq_getElem i.isLt] using hx
  simp only [Function.comp_apply]
  rw [betaOf_eq hx, ← hxi]
  congr 1
  rw [hxi, hx1]

/-- Products along a full run are products over the steps. -/
lemma prod_fullRun {M : Type} [CommMonoid M] {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) (g : Fin bp.n → Bool → M) :
    (xs.map fun x => g x.1 (act bp J σ x)).prod = ∏ t : Fin bp.n, g t (betaOf bp J σ xs t) := by
  conv_lhs => rw [← List.ofFn_getElem (xs := xs), List.map_ofFn, List.prod_ofFn]
  refine Fintype.prod_equiv (finCongr h.2) _ _ fun i => ?_
  obtain ⟨x, hx, -, hx1⟩ := h.getElem (finCongr h.2 i)
  have hxi : xs[i.val] = x := by
    simpa [List.getElem?_eq_getElem i.isLt] using hx
  simp only [Function.comp_apply]
  rw [betaOf_eq hx, ← hxi]
  congr 1
  rw [hxi, hx1]

/-- The bits determine a full run. -/
lemma fullRun_eq_of_betaOf {xs xs' : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs)
    (h' : IsFullRun bp J xs') (hb : betaOf bp J σ xs = betaOf bp J σ xs') : xs = xs' := by
  refine List.ext_getElem (h.2.trans h'.2.symm) fun t ht ht' => ?_
  obtain ⟨x, hx, hxm, hx1⟩ := h.getElem ⟨t, h.2 ▸ ht⟩
  obtain ⟨x', hx', hxm', hx1'⟩ := h'.getElem ⟨t, h.2 ▸ ht⟩
  have e1 : xs[t] = x := by simpa [List.getElem?_eq_getElem ht] using hx
  have e2 : xs'[t] = x' := by simpa [List.getElem?_eq_getElem ht'] using hx'
  rw [e1, e2]
  have hact := congrFun hb ⟨t, h.2 ▸ ht⟩
  rw [betaOf_eq hx, betaOf_eq hx'] at hact
  exact slot_eq_of_act σ hxm hxm' (hx1.trans hx1'.symm) hact

/-- Full path words of full runs determine the program and the run. -/
lemma fullWord_inj {pr pr' : Bool} {xs xs' : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs)
    (h' : IsFullRun bp J xs') (he : fullWord bp J pr xs = fullWord bp J pr' xs') :
    pr = pr' ∧ xs = xs' := by
  simp only [fullWord, List.singleton_append, List.cons_append, List.cons.injEq] at he
  obtain ⟨hs, he⟩ := he
  have hpr : pr = pr' := by cases pr <;> cases pr' <;> simp_all [sH]
  subst hpr
  have hm : xs.map (hdl bp J pr) = xs'.map (hdl bp J pr) := List.append_cancel_right he
  refine ⟨rfl, List.ext_getElem (by simpa using congrArg List.length hm) fun t ht ht' => ?_⟩
  have hget := congrArg (fun l => l[t]?) hm
  simp only [List.getElem?_map, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem ht',
    Option.map_some, Option.some.injEq] at hget
  have hx := (h.1 t ht).1
  have hx' := (h'.1 t ht').1
  have hidx : (programSlots bp J).idxOf xs[t] = (programSlots bp J).idxOf xs'[t] := by
    simp only [hdl] at hget
    omega
  exact (List.idxOf_inj hx).1 hidx

end FullRuns

/-! ### Full evaluations: the γ-polynomial with bookend coefficients -/

section FullPoly

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

/-- The γ-exponent of a handle (`0` for the bookends). -/
noncomputable def gexpH (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (k : ℕ) :
    Coord bp →₀ ℕ :=
  match slotOf bp J k with
  | some (pr, x) => gexpStep pr x.1 (act bp J σ x)
  | none => 0

/-- The permutation matrix of a primal step handle (`1` otherwise). -/
def piH (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (k : ℕ) :
    Matrix (Fin 5) (Fin 5) (ZMod p) :=
  match slotOf bp J k with
  | some (true, x) => (bp.A x.1 (act bp J σ x)).permMatrix (ZMod p)
  | _ => 1

/-- The bookend coefficient of a path word. -/
def coefU (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (bk : Bookends p)
    (u : List ℕ) : ZMod p :=
  if u.head? = some (sH true) then sS bk ⬝ᵥ ((u.map (piH bp J σ)).prod *ᵥ tS bk)
  else s'S bk ⬝ᵥ ((u.map (piH bp J σ)).prod *ᵥ t'S bk)

/-- The full evaluation as a polynomial in the γ's, for fixed bookend vectors. -/
noncomputable def Qfull (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (bk : Bookends p) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) :
    MvPolynomial (Coord bp) (ZMod p) :=
  ∑ u ∈ w.coeff.support, MvPolynomial.monomial
    (((FreeMonoid.toList u).map (gexpH bp J σ)).sum)
    (w.coeff u * coefU bp J σ bk (FreeMonoid.toList u))

lemma gexpH_fullWord (pr : Bool) {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs) :
    ((fullWord bp J pr xs).map (gexpH bp J σ)).sum = gexp pr (betaOf bp J σ xs) := by
  have h0 : gexpH bp J σ (sH pr) = 0 := by cases pr <;> simp [gexpH, sH, slotOf_lt_four]
  have h1 : gexpH bp J σ (tH pr) = 0 := by cases pr <;> simp [gexpH, tH, slotOf_lt_four]
  have hmid : (xs.map (hdl bp J pr)).map (gexpH bp J σ) =
      xs.map fun x => gexpStep pr x.1 (act bp J σ x) := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp [gexpH, slotOf_hdl pr (h.mem x hx)]
  simp only [fullWord, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, h0, h1, add_zero, zero_add, hmid]
  exact sum_fullRun h _

lemma prod_piH_fullWord (pr : Bool) {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs) :
    ((fullWord bp J pr xs).map (piH (p := p) bp J σ)).prod = piSel bp J σ pr xs := by
  have h0 : piH (p := p) bp J σ (sH pr) = 1 := by cases pr <;> simp [piH, sH, slotOf_lt_four]
  have h1 : piH (p := p) bp J σ (tH pr) = 1 := by cases pr <;> simp [piH, tH, slotOf_lt_four]
  have hmid : (xs.map (hdl bp J pr)).map (piH (p := p) bp J σ) =
      xs.map fun x => if pr then (bp.A x.1 (act bp J σ x)).permMatrix (ZMod p) else 1 := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    cases pr <;> simp [piH, slotOf_hdl _ (h.mem x hx)]
  simp only [fullWord, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, h0, h1, mul_one, one_mul, hmid]
  cases pr
  · simp [piSel]
  · simp [piSel]

lemma coefU_fullWord (bk : Bookends p) (pr : Bool) {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) :
    coefU bp J σ bk (fullWord bp J pr xs) =
      (if pr then sS bk else s'S bk) ⬝ᵥ (piSel bp J σ pr xs *ᵥ (if pr then tS bk else t'S bk)) := by
  unfold coefU
  rw [prod_piH_fullWord pr h]
  cases pr <;> simp [fullWord, sH]

/-- The unrandomized full evaluation is the evaluation of `Qfull` at the scalar coordinates. -/
theorem entry_full_eval (ω : Sample p bp) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs) :
    liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w ⟨0, by unfold NDim; omega⟩
        ⟨0, by unfold NDim; omega⟩ =
      MvPolynomial.eval (coordVal ω) (Qfull bp J σ ω.2.2.2.2.2.2.2.2.1 w) := by
  rw [liftDB_apply, Qfull, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨pr, xs, h, hu'⟩ := hw u hu
  rw [MvPolynomial.eval_monomial, hu', gexpH_fullWord pr h, coefU_fullWord _ pr h]
  rw [show fullWord bp J pr xs = [sH pr] ++ xs.map (hdl bp J pr) ++ [tH pr] from rfl,
    entry_full ω pr xs h.mem]
  rw [prod_fullRun h (fun t b => alphaSel pr ω t b)]
  simp only [alphaSel_eq]
  rw [gexp, Finsupp.prod_finset_sum_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  cases pr <;> simp only [sStarSel, tStarSel, if_true, Bool.false_eq_true, if_false,
    Sample.sStar, Sample.tStar, Sample.s'Star, Sample.t'Star, sS, tS, s'S, t'S] <;> ring

/-- Equal bundling monomials of two full paths: the same path, or the two programs on one
consistent run. -/
lemma gexp_group {pr pr₀ : Bool} {β β₀ : Fin bp.n → Bool} (h : gexp pr β = gexp pr₀ β₀) :
    (pr = pr₀ ∧ β = β₀) ∨ (pr ≠ pr₀ ∧ β = β₀ ∧ Consistent (bp := bp) β₀) := by
  cases pr <;> cases pr₀
  · exact Or.inl ⟨rfl, gexp_inj h⟩
  · obtain ⟨h1, h2⟩ := gexp_cross h.symm
    exact Or.inr ⟨by decide, h1.symm, h2⟩
  · obtain ⟨h1, h2⟩ := gexp_cross h
    exact Or.inr ⟨by decide, h1, h1 ▸ h2⟩
  · exact Or.inl ⟨rfl, gexp_inj h⟩

end FullPoly

/-! ### Full evaluations: cancellation, collision bound, invariance -/

section FullBound

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma list_prod_permMatrix {R : Type} [CommRing R] (l : List (Equiv.Perm (Fin 5))) :
    (l.map fun s => s.permMatrix R).prod = (l.reverse.prod).permMatrix R := by
  induction l with
  | nil => simp [Matrix.permMatrix_one]
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.reverse_cons, List.prod_append, List.prod_singleton,
      Matrix.permMatrix_mul]

lemma permMatrix_eq_one_iff {R : Type} [CommRing R] [Nontrivial R] (P : Equiv.Perm (Fin 5)) :
    P.permMatrix R = 1 ↔ P = 1 := by
  constructor
  · intro h
    ext i
    simp only [Equiv.Perm.one_apply]
    have := congrFun (congrFun h i) (P i)
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, if_true, Matrix.one_apply] at this
    by_contra hne
    rw [if_neg (fun h' => hne (congrArg Fin.val h'.symm))] at this
    exact one_ne_zero this
  · rintro rfl
    exact Matrix.permMatrix_one

/-- The permutation of a run. -/
def runPerm (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (xs : List (Fin bp.n × Bool)) : Equiv.Perm (Fin 5) :=
  ((xs.map fun x => bp.A x.1 (act bp J σ x)).reverse).prod

lemma piSel_true (xs : List (Fin bp.n × Bool)) :
    piSel bp J σ true xs = (runPerm bp J σ xs).permMatrix (ZMod p) := by
  rw [piSel, if_pos rfl, runPerm, ← list_prod_permMatrix, List.map_map]
  rfl

/-- The coefficients of the two words of a run. -/
noncomputable def wT (bp : BP) (J : Finset (Fin bp.ℓ)) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (xs : List (Fin bp.n × Bool)) : ZMod p := w.coeff (FreeMonoid.ofList (fullWord bp J true xs))
/-- The dummy coefficient. -/
noncomputable def wF (bp : BP) (J : Finset (Fin bp.ℓ)) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (xs : List (Fin bp.n × Bool)) : ZMod p := w.coeff (FreeMonoid.ofList (fullWord bp J false xs))

/-- A run whose primal and dummy words cancel identically (accepting consistent input with
opposite coefficients). -/
def Cancels (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) (xs : List (Fin bp.n × Bool)) : Prop :=
  Consistent (bp := bp) (betaOf bp J σ xs) ∧ runPerm bp J σ xs = 1 ∧ wT bp J w xs + wF bp J w xs = 0

/-- Every path of the support cancels. -/
def AllCancel (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) : Prop :=
  ∀ u ∈ w.coeff.support, ∀ pr xs, IsFullRun bp J xs → FreeMonoid.toList u = fullWord bp J pr xs →
    Cancels bp J σ w xs

end FullBound

section FullBound2

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma padMat_row_zero {N b : ℕ} (R : Matrix (Fin 1) (Fin b) (ZMod p)) (i k : Fin N)
    (hi : i.val ≠ 0) : padMat N R i k = 0 := by
  simp [padMat, show ¬ i.val < 1 by omega]

lemma padMat_col_zero {N a : ℕ} (C : Matrix (Fin a) (Fin 1) (ZMod p)) (k j : Fin N)
    (hj : j.val ≠ 0) : padMat N C k j = 0 := by
  unfold padMat
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

/-- Full paths only produce the `(0,0)` entry. -/
lemma full_entry_zero (ω : Sample p bp) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs)
    (i j : Fin (NDim bp.n)) (hij : ¬ (i.val = 0 ∧ j.val = 0)) :
    liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w i j = 0 := by
  rw [liftDB_apply]
  refine Finset.sum_eq_zero fun u hu => ?_
  obtain ⟨pr, xs, h, hu'⟩ := hw u hu
  rw [hu']
  simp only [fullWord, List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, hmat_sH, hmat_tH]
  rw [Matrix.mul_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ?_)
  by_cases hi : i.val = 0
  · rw [padMat_col_zero _ k j (fun hj => hij ⟨hi, hj⟩), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun l _ => by rw [padMat_row_zero _ i l hi, zero_mul],
      zero_mul]

/-- The value of a full path word. -/
lemma fullValue (ω : Sample p bp) (pr : Bool) {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) :
    ((fullWord bp J pr xs).map (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod
        ⟨0, by unfold NDim; omega⟩ ⟨0, by unfold NDim; omega⟩ =
      (gexp pr (betaOf bp J σ xs)).prod (fun v e => coordVal ω v ^ e) *
        (sStarSel pr ω ⬝ᵥ (piSel bp J σ pr xs *ᵥ tStarSel pr ω)) := by
  rw [show fullWord bp J pr xs = [sH pr] ++ xs.map (hdl bp J pr) ++ [tH pr] from rfl,
    entry_full ω pr xs h.mem, prod_fullRun h (fun t b => alphaSel pr ω t b)]
  simp only [alphaSel_eq]
  rw [gexp, Finsupp.prod_finset_sum_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

/-- **Cancellation.** If every path of the support cancels, the full evaluation vanishes. -/
theorem full_zero_of_allCancel (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs)
    (hc : AllCancel bp J σ w) (ω : Sample p bp) :
    liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0 := by
  classical
  ext i j
  by_cases hij : i.val = 0 ∧ j.val = 0
  swap
  · exact full_entry_zero ω w hw i j hij
  obtain ⟨hi, hj⟩ := hij
  have ei : i = ⟨0, by unfold NDim; omega⟩ := Fin.ext hi
  have ej : j = ⟨0, by unfold NDim; omega⟩ := Fin.ext hj
  rw [ei, ej, Matrix.zero_apply, liftDB_apply]
  have hd : ∀ u ∈ w.coeff.support, ∃ d : Bool × List (Fin bp.n × Bool), IsFullRun bp J d.2 ∧
      FreeMonoid.toList u = fullWord bp J d.1 d.2 := fun u hu => by
    obtain ⟨pr, xs, h, e⟩ := hw u hu
    exact ⟨(pr, xs), h, e⟩
  -- the value of a path depends only on its run when the run cancels
  have hval : ∀ (xs : List (Fin bp.n × Bool)), IsFullRun bp J xs → Cancels bp J σ w xs →
      ((fullWord bp J true xs).map (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod
          ⟨0, by unfold NDim; omega⟩ ⟨0, by unfold NDim; omega⟩ =
        ((fullWord bp J false xs).map (hmat (NDim bp.n) (initDB bp J σ (unrand ω)))).prod
          ⟨0, by unfold NDim; omega⟩ ⟨0, by unfold NDim; omega⟩ := by
    intro xs h hcan
    rw [fullValue ω true h, fullValue ω false h, gexp_consistent hcan.1, piSel_true, hcan.2.1,
      Matrix.permMatrix_one]
    simp only [piSel, Bool.false_eq_true, if_false, Matrix.one_mulVec, sStarSel, tStarSel,
      if_true]
    rw [show ω.sStar ⬝ᵥ ω.tStar = ω.s'Star ⬝ᵥ ω.t'Star from ω.2.2.2.2.2.2.2.2.1.2]
  -- regroup the support into the primal/dummy pairs of its runs
  set runOf : FreeMonoid ℕ → List (Fin bp.n × Bool) := fun u =>
    if h : ∃ d : Bool × List (Fin bp.n × Bool), IsFullRun bp J d.2 ∧
        FreeMonoid.toList u = fullWord bp J d.1 d.2 then (Classical.choose h).2 else []
  have hrun : ∀ u ∈ w.coeff.support, IsFullRun bp J (runOf u) ∧
      ∃ pr, FreeMonoid.toList u = fullWord bp J pr (runOf u) := by
    intro u hu
    have hex := hd u hu
    simp only [runOf, dif_pos hex]
    exact ⟨(Classical.choose_spec hex).1, _, (Classical.choose_spec hex).2⟩
  set D := w.coeff.support.image runOf
  have hD : ∀ xs ∈ D, IsFullRun bp J xs := by
    intro xs hxs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hxs
    exact (hrun u hu).1
  have hsub : w.coeff.support ⊆ D.biUnion fun xs =>
      ({FreeMonoid.ofList (fullWord bp J true xs), FreeMonoid.ofList (fullWord bp J false xs)} :
        Finset (FreeMonoid ℕ)) := by
    intro u hu
    obtain ⟨-, pr, e⟩ := hrun u hu
    refine Finset.mem_biUnion.2 ⟨runOf u, Finset.mem_image_of_mem _ hu, ?_⟩
    have hu' : u = FreeMonoid.ofList (fullWord bp J pr (runOf u)) := by
      rw [← e]
      rfl
    rw [Finset.mem_insert, Finset.mem_singleton]
    cases pr
    · exact Or.inr hu'
    · exact Or.inl hu'
  rw [Finset.sum_subset hsub (fun u _ hu => by rw [Finsupp.notMem_support_iff.1 hu, zero_mul])]
  rw [Finset.sum_biUnion]
  · refine Finset.sum_eq_zero fun xs hxs => ?_
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hxs
    obtain ⟨h, pr, e⟩ := hrun u hu
    have hcan := hc u hu pr (runOf u) h e
    have hne : FreeMonoid.ofList (fullWord bp J true (runOf u)) ≠
        FreeMonoid.ofList (fullWord bp J false (runOf u)) := by
      intro heq
      have := (fullWord_inj h h (congrArg FreeMonoid.toList heq)).1
      simp at this
    rw [Finset.sum_pair hne]
    simp only [FreeMonoid.toList_ofList]
    rw [hval _ h hcan, ← add_mul]
    have hsum := hcan.2.2
    simp only [wT, wF] at hsum
    rw [hsum, zero_mul]
  · intro xs hxs xs' hxs' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hu'
    have key : ∀ pr pr', FreeMonoid.ofList (fullWord bp J pr xs) =
        FreeMonoid.ofList (fullWord bp J pr' xs') → False := by
      intro pr pr' heq
      exact hne (fullWord_inj (hD xs hxs) (hD xs' hxs') (congrArg FreeMonoid.toList heq)).2
    rcases hu with rfl | rfl <;> rcases hu' with h' | h'
    all_goals exact key _ _ h'

end FullBound2

section FullBound3

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma degree_gexp (pr : Bool) (β : Fin bp.n → Bool) :
    (gexp pr β).sum (fun _ => id) = 2 * bp.n := by
  rw [gexp, ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have : ∀ t : Fin bp.n, (gexpStep pr t (β t)).sum (fun _ => id) = 2 := by
    intro t
    rw [gexpStep, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    rfl
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The coefficient of the bundling monomial of a path in `Qfull`. -/
lemma coeff_Qfull (bk : Bookends p) (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs)
    (pr₀ : Bool) {xs₀ : List (Fin bp.n × Bool)} (h₀ : IsFullRun bp J xs₀) :
    MvPolynomial.coeff (gexp pr₀ (betaOf bp J σ xs₀)) (Qfull bp J σ bk w) =
      (if gexp true (betaOf bp J σ xs₀) = gexp pr₀ (betaOf bp J σ xs₀) then
        wT bp J w xs₀ * (sS bk ⬝ᵥ (piSel bp J σ true xs₀ *ᵥ tS bk)) else 0) +
      (if gexp false (betaOf bp J σ xs₀) = gexp pr₀ (betaOf bp J σ xs₀) then
        wF bp J w xs₀ * (s'S bk ⬝ᵥ t'S bk) else 0) := by
  classical
  set M₀ := gexp pr₀ (betaOf bp J σ xs₀)
  set uT := FreeMonoid.ofList (fullWord bp J true xs₀)
  set uF := FreeMonoid.ofList (fullWord bp J false xs₀)
  have hTF : uT ≠ uF := by
    intro heq
    have := (fullWord_inj h₀ h₀ (congrArg FreeMonoid.toList heq)).1
    simp at this
  set F : FreeMonoid ℕ → ZMod p := fun u =>
    if ((FreeMonoid.toList u).map (gexpH bp J σ)).sum = M₀ then
      w.coeff u * coefU bp J σ bk (FreeMonoid.toList u) else 0
  have hQ : MvPolynomial.coeff M₀ (Qfull bp J σ bk w) = ∑ u ∈ w.coeff.support, F u := by
    simp only [Qfull, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, F]
  rw [hQ]
  -- only the two words of `xs₀` can carry the monomial `M₀`
  have h1 : ∑ u ∈ w.coeff.support, F u = ∑ u ∈ w.coeff.support ∪ {uT, uF}, F u := by
    refine Finset.sum_subset Finset.subset_union_left fun u hu hnot => ?_
    simp only [F, Finsupp.notMem_support_iff.1 hnot, zero_mul, ite_self]
  have h2 : ∑ u ∈ w.coeff.support ∪ {uT, uF}, F u = ∑ u ∈ ({uT, uF} : Finset _), F u := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun u hu hnot => ?_
    have hsupp : u ∈ w.coeff.support := by
      rcases Finset.mem_union.1 hu with h | h
      · exact h
      · exact absurd h hnot
    obtain ⟨pr, xs, h, e⟩ := hw u hsupp
    simp only [F, e, gexpH_fullWord pr h]
    rw [if_neg]
    intro hM
    have hb : betaOf bp J σ xs = betaOf bp J σ xs₀ := by
      rcases gexp_group hM with ⟨-, hb⟩ | ⟨-, hb, -⟩
      · exact hb
      · exact hb
    have hxs := fullRun_eq_of_betaOf h h₀ hb
    rw [hxs] at e
    apply hnot
    have hu : u = FreeMonoid.ofList (fullWord bp J pr xs₀) := by rw [← e]; rfl
    rw [hu]
    cases pr <;> simp [uT, uF]
  rw [h1, h2, Finset.sum_pair hTF]
  simp only [F, uT, uF, FreeMonoid.toList_ofList, gexpH_fullWord true h₀, gexpH_fullWord false h₀,
    coefU_fullWord bk true h₀, coefU_fullWord bk false h₀, if_true, Bool.false_eq_true, if_false]
  simp [piSel, wT, wF]

/-- **Full evaluations.** If some path of the support does not cancel, the full evaluation
vanishes with probability at most `2(n+1)/p`. -/
theorem full_card_le (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ))
    (hw : ∀ u ∈ w.coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs)
    (hnc : ¬ AllCancel bp J σ w) :
    ((Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0).card : ℝ) ≤
      2 * (bp.n + 1) / p * Fintype.card (Sample p bp) := by
  classical
  simp only [AllCancel] at hnc
  push_neg at hnc
  obtain ⟨u₀, hu₀, pr₀, xs₀, h₀, e₀, hnc⟩ := hnc
  set β₀ := betaOf bp J σ xs₀
  set P := runPerm bp J σ xs₀
  set a := wT bp J w xs₀
  set b := wF bp J w xs₀
  have hu₀' : u₀ = FreeMonoid.ofList (fullWord bp J pr₀ xs₀) := by rw [← e₀]; rfl
  have hw₀ : (if pr₀ then a else b) ≠ 0 := by
    have := Finsupp.mem_support_iff.1 hu₀
    rw [hu₀'] at this
    cases pr₀ <;> simpa [a, b, wT, wF] using this
  -- the coefficient of `M₀` in `Qfull bk w` is a good bookend scalar
  obtain ⟨c, c', hgood, hcoef⟩ : ∃ c c' : ZMod p, GoodCoef P c c' ∧ ∀ bk : Bookends p,
      MvPolynomial.coeff (gexp pr₀ β₀) (Qfull bp J σ bk w) =
        c * (sS bk ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ tS bk)) + c' * (s'S bk ⬝ᵥ t'S bk) := by
    by_cases hcons : Consistent (bp := bp) β₀
    · have heq := gexp_consistent hcons
      refine ⟨a, b, ?_, fun bk => ?_⟩
      · by_cases hP : P = 1
        · refine Or.inr ⟨hP, fun hab => hnc ⟨hcons, hP, hab⟩⟩
        · refine Or.inl ⟨hP, fun ⟨ha, hb⟩ => hw₀ ?_⟩
          cases pr₀ <;> simp [ha, hb]
      · rw [coeff_Qfull bk w hw pr₀ h₀, piSel_true]
        cases pr₀ <;> simp [heq, β₀, a, b, P]
    · have hne : gexp true β₀ ≠ gexp false β₀ := fun h => hcons (gexp_cross h).2
      cases pr₀
      · refine ⟨0, b, ?_, fun bk => ?_⟩
        · have hb : b ≠ 0 := by simpa using hw₀
          by_cases hP : P = 1
          · exact Or.inr ⟨hP, by simpa using hb⟩
          · exact Or.inl ⟨hP, fun ⟨_, h⟩ => hb h⟩
        · rw [coeff_Qfull bk w hw false h₀]
          simp [hne, β₀, b]
      · refine ⟨a, 0, ?_, fun bk => ?_⟩
        · have ha : a ≠ 0 := by simpa using hw₀
          by_cases hP : P = 1
          · exact Or.inr ⟨hP, by simpa using ha⟩
          · exact Or.inl ⟨hP, fun ⟨h, _⟩ => ha h⟩
        · rw [coeff_Qfull bk w hw true h₀, piSel_true]
          simp [hne.symm, β₀, P, a]
  -- counting
  set C : Bookends p → ZMod p := fun bk =>
    c * (sS bk ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ tS bk)) + c' * (s'S bk ⬝ᵥ t'S bk)
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hdeg : ∀ bk : Bookends p, (Qfull bp J σ bk w).totalDegree ≤ 2 * bp.n := by
    intro bk
    refine MvPolynomial.totalDegree_finsetSum_le fun u hu => ?_
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    obtain ⟨pr, xs, h, e⟩ := hw u hu
    rw [e, gexpH_fullWord pr h, degree_gexp]
  have hV : ∀ bk : Bookends p, ((Finset.univ.filter fun z : Coord bp → ZMod p =>
      MvPolynomial.eval z (Qfull bp J σ bk w) = 0).card : ℝ) ≤
      2 * bp.n / p * Fintype.card (Coord bp → ZMod p) +
        (if C bk = 0 then (Fintype.card (Coord bp → ZMod p) : ℝ) else 0) := by
    intro bk
    by_cases hC : C bk = 0
    · rw [if_pos hC]
      have : ((Finset.univ.filter fun z : Coord bp → ZMod p =>
          MvPolynomial.eval z (Qfull bp J σ bk w) = 0).card : ℝ) ≤
          Fintype.card (Coord bp → ZMod p) := by exact_mod_cast Finset.card_le_univ _
      have h0 : (0 : ℝ) ≤ 2 * bp.n / p * Fintype.card (Coord bp → ZMod p) := by positivity
      linarith
    · rw [if_neg hC, add_zero]
      have hQ : Qfull bp J σ bk w ≠ 0 := by
        intro hQ
        apply hC
        have := hcoef bk
        rw [hQ, MvPolynomial.coeff_zero] at this
        exact this.symm
      calc _ ≤ ((Qfull bp J σ bk w).totalDegree : ℝ) / p *
            (Fintype.card (Coord bp → ZMod p) : ℝ) := sz_coord _ hQ
        _ ≤ _ := by
            have hd : ((Qfull bp J σ bk w).totalDegree : ℝ) ≤ 2 * bp.n := by exact_mod_cast hdeg bk
            gcongr
  have hsub : (Finset.univ.filter fun ω : Sample p bp =>
      liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0) ⊆
      Finset.univ.filter fun ω : Sample p bp =>
        MvPolynomial.eval (coordVal ω) (Qfull bp J σ ω.2.2.2.2.2.2.2.2.1 w) = 0 := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [← entry_full_eval ω w hw, hω]
    rfl
  have hcount := card_filter_bk_coord (p := p) (bp := bp)
    (fun bk z => MvPolynomial.eval z (Qfull bp J σ bk w) = 0)
  have hrest : ((Finset.univ.filter fun x : Rest p bp => C x.2.2 = 0).card : ℝ) ≤
      2 / p * Fintype.card (Rest p bp) := by
    have hfib : (Finset.univ.filter fun x : Rest p bp => C x.2.2 = 0).card =
        Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) *
          (Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) *
            (Finset.univ.filter fun bk : Bookends p => C bk = 0).card) := by
      calc (Finset.univ.filter fun x : Rest p bp => C x.2.2 = 0).card
          = ((Finset.univ : Finset (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p))) ×ˢ
              ((Finset.univ : Finset (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p))) ×ˢ
                (Finset.univ.filter fun bk : Bookends p => C bk = 0))).card := by
            congr 1
            ext x
            simp [Finset.mem_product]
        _ = _ := by rw [Finset.card_product, Finset.card_product, Finset.card_univ]
    have hbk := bookend_card_le P c c' hgood
    rw [hfib]
    push_cast
    rw [show Fintype.card (Rest p bp) =
        Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) *
          (Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) *
            Fintype.card (Bookends p)) by simp [Rest, Fintype.card_prod]]
    push_cast
    have hA : (0 : ℝ) ≤ Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) :=
      Nat.cast_nonneg _
    calc _ ≤ (Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) : ℝ) *
          ((Fintype.card (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) : ℝ) *
            (2 / p * Fintype.card (Bookends p))) := by gcongr
      _ = _ := by ring
  calc ((Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) w = 0).card : ℝ)
      ≤ ((Finset.univ.filter fun ω : Sample p bp =>
          MvPolynomial.eval (coordVal ω) (Qfull bp J σ ω.2.2.2.2.2.2.2.2.1 w) = 0).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ∑ x : Rest p bp, ((Finset.univ.filter fun z : Coord bp → ZMod p =>
          MvPolynomial.eval z (Qfull bp J σ x.2.2 w) = 0).card : ℝ) := by
        rw [show ((Finset.univ.filter fun ω : Sample p bp =>
          MvPolynomial.eval (coordVal ω) (Qfull bp J σ ω.2.2.2.2.2.2.2.2.1 w) = 0).card : ℝ) =
            ((∑ x : Rest p bp, (Finset.univ.filter fun z : Coord bp → ZMod p =>
              MvPolynomial.eval z (Qfull bp J σ x.2.2 w) = 0).card : ℕ) : ℝ) by
          exact_mod_cast hcount]
        push_cast
        rfl
    _ ≤ ∑ x : Rest p bp, (2 * bp.n / p * Fintype.card (Coord bp → ZMod p) +
          (if C x.2.2 = 0 then (Fintype.card (Coord bp → ZMod p) : ℝ) else 0)) :=
        Finset.sum_le_sum fun x _ => hV x.2.2
    _ = Fintype.card (Rest p bp) * (2 * bp.n / p * Fintype.card (Coord bp → ZMod p)) +
          ((Finset.univ.filter fun x : Rest p bp => C x.2.2 = 0).card : ℝ) *
            Fintype.card (Coord bp → ZMod p) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card (Rest p bp) * (2 * bp.n / p * Fintype.card (Coord bp → ZMod p)) +
          2 / p * Fintype.card (Rest p bp) * Fintype.card (Coord bp → ZMod p) := by
        gcongr
    _ = 2 * (bp.n + 1) / p * Fintype.card (Sample p bp) := by
        rw [card_sample_eq]
        push_cast
        ring

end FullBound3

/-! ### Full evaluations: cancellation depends on `σ` only through `F|_σ` -/

section FullInvariance

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)}

/-- The slot bits along a run (independent of the assignment). -/
def slotBit (xs : List (Fin bp.n × Bool)) (t : Fin bp.n) : Bool :=
  match xs[t.val]? with
  | some x => x.2
  | none => false

/-- The input read off a run: on each block, the slot bit of one of its steps. -/
noncomputable def chiOf (xs : List (Fin bp.n × Bool)) (j : Fin bp.ℓ) : Bool :=
  if h : ∃ t : Fin bp.n, bp.inp t = j then slotBit xs (Classical.choose h) else false

lemma betaOf_full (τ : Fin bp.ℓ → Bool) {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs)
    (t : Fin bp.n) :
    betaOf bp J τ xs t = if bp.inp t ∈ J then τ (bp.inp t) else slotBit xs t := by
  obtain ⟨x, hx, -, hx1⟩ := h.getElem t
  rw [betaOf_eq hx]
  simp [act, slotBit, hx, hx1]

lemma consistent_iff (σ σ' : Fin bp.ℓ → Bool) {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) :
    Consistent (bp := bp) (betaOf bp J σ xs) ↔ Consistent (bp := bp) (betaOf bp J σ' xs) := by
  have key : ∀ τ : Fin bp.ℓ → Bool, Consistent (bp := bp) (betaOf bp J τ xs) ↔
      ∀ t t' : Fin bp.n, bp.inp t = bp.inp t' → bp.inp t ∉ J → slotBit xs t = slotBit xs t' := by
    intro τ
    constructor
    · intro hc t t' hb hJ
      have := hc t t' hb
      rw [betaOf_full τ h, betaOf_full τ h, if_neg hJ, if_neg (hb ▸ hJ)] at this
      exact this
    · intro hs t t' hb
      rw [betaOf_full τ h, betaOf_full τ h]
      by_cases hJ : bp.inp t ∈ J
      · rw [if_pos hJ, if_pos (hb ▸ hJ), hb]
      · rw [if_neg hJ, if_neg (hb ▸ hJ)]
        exact hs t t' hb hJ
  rw [key σ, key σ']

/-- On a consistent run, the actual bits are those of the input `fix J σ (chiOf xs)`. -/
lemma act_eq_fix (σ : Fin bp.ℓ → Bool) {xs : List (Fin bp.n × Bool)} (h : IsFullRun bp J xs)
    (hc : Consistent (bp := bp) (betaOf bp J σ xs)) (t : Fin bp.n) :
    betaOf bp J σ xs t = fix J σ (chiOf xs) (bp.inp t) := by
  obtain ⟨x, hx, -, hx1⟩ := h.getElem t
  rw [betaOf_eq hx]
  unfold fix chiOf
  by_cases hJ : bp.inp t ∈ J
  · simp [act, hx1, hJ]
  · have hex : ∃ t' : Fin bp.n, bp.inp t' = bp.inp t := ⟨t, rfl⟩
    rw [if_neg hJ, dif_pos hex]
    set t₀ := Classical.choose hex
    have ht₀ : bp.inp t₀ = bp.inp t := Classical.choose_spec hex
    have hcons := hc t t₀ ht₀.symm
    obtain ⟨x₀, hx₀, -, hx₀1⟩ := h.getElem t₀
    rw [betaOf_eq hx, betaOf_eq hx₀] at hcons
    simp only [slotBit, hx₀]
    simp only [act, hx1, hx₀1, ht₀, hJ, if_false] at hcons ⊢
    exact hcons

lemma runPerm_eq_one_iff (σ : Fin bp.ℓ → Bool) {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) (hc : Consistent (bp := bp) (betaOf bp J σ xs)) :
    runPerm bp J σ xs = 1 ↔ bp.eval (fix J σ (chiOf xs)) = true := by
  have hlist : xs.map (fun x => bp.A x.1 (act bp J σ x)) =
      List.ofFn fun i : Fin bp.n => bp.A i (fix J σ (chiOf xs) (bp.inp i)) := by
    conv_lhs => rw [← List.ofFn_getElem (xs := xs), List.map_ofFn]
    refine List.ext_getElem (by simp [h.2]) fun t ht ht' => ?_
    simp only [List.getElem_ofFn, Function.comp_apply]
    obtain ⟨x, hx, -, hx1⟩ := h.getElem ⟨t, by simpa using ht'⟩
    have hxt : xs[t]'(by simpa [h.2] using ht') = x := by
      have hx' : xs[t]? = some x := hx
      rw [List.getElem?_eq_getElem (by simpa [h.2] using ht')] at hx'
      exact Option.some_injective _ hx'
    rw [hxt, ← act_eq_fix σ h hc, betaOf_eq hx, hx1]
  have hmapZ : (List.ofFn fun i : Fin bp.n =>
      (bp.A i (fix J σ (chiOf xs) (bp.inp i))).permMatrix ℤ) =
      (List.ofFn fun i : Fin bp.n => bp.A i (fix J σ (chiOf xs) (bp.inp i))).map
        (fun s => s.permMatrix ℤ) := by
    simp [List.map_ofFn, Function.comp_def]
  unfold BP.eval runPerm
  rw [hlist, decide_eq_true_iff, hmapZ, list_prod_permMatrix, permMatrix_eq_one_iff]

/-- Cancellation is the same for functionally equivalent assignments. -/
theorem cancels_iff {σ σ' : Fin bp.ℓ → Bool} (hFE : FunctionallyEquivalent bp J σ σ')
    (w : MonoidAlgebra (ZMod p) (FreeMonoid ℕ)) {xs : List (Fin bp.n × Bool)}
    (h : IsFullRun bp J xs) : Cancels bp J σ w xs ↔ Cancels bp J σ' w xs := by
  unfold Cancels
  constructor
  · rintro ⟨hc, hP, hw⟩
    have hc' := (consistent_iff σ σ' h).1 hc
    refine ⟨hc', ?_, hw⟩
    rw [runPerm_eq_one_iff σ' h hc', ← hFE (chiOf xs)]
    exact (runPerm_eq_one_iff σ h hc).1 hP
  · rintro ⟨hc', hP, hw⟩
    have hc := (consistent_iff σ σ' h).2 hc'
    refine ⟨hc, ?_, hw⟩
    rw [runPerm_eq_one_iff σ h hc, hFE (chiOf xs)]
    exact (runPerm_eq_one_iff σ' h hc').1 hP

end FullInvariance

/-! ### The full-evaluation statements -/

section FullFinal

variable [Fact p.Prime] {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma full_support {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) (hsrc : s.2.2.1 = .src) (hsnk : s.2.2.2 = .snk) :
    ∀ u ∈ (word e - word e').coeff.support, ∃ pr xs, IsFullRun bp J xs ∧
      FreeMonoid.toList u = fullWord bp J pr xs := by
  intro u hu
  have hpath := word_sub_support hs hs' u hu
  rw [hsrc, hsnk] at hpath
  obtain ⟨pr, hs₁, ht₁, i, xs, hrun, huf, hi, hl, ha, hb⟩ := path_form hpath
  have hs₁' : hs₁ = true := by
    by_contra hne
    simp only [hne, Bool.false_eq_true, if_false] at ha
    exact pc_ne_src _ _ ha.symm
  have ht₁' : ht₁ = true := by
    by_contra hne
    simp only [hne, Bool.false_eq_true, if_false] at hb
    exact pc_ne_snk _ _ hb.symm
  subst hs₁' ht₁'
  have hi0 := hi rfl
  subst hi0
  refine ⟨pr, xs, ⟨hrun, by simpa using hl rfl⟩, ?_⟩
  rw [huf]
  rfl

/-- **Full evaluations: the collision bound.** -/
theorem full_collision_main (e e' : QExpr p) (s : Shape) (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) (hsrc : s.2.2.1 = .src) (hsnk : s.2.2.2 = .snk)
    (hne : ¬ IdenticallyEqual bp J σ e e') :
    ((Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) (word e - word e') = 0).card : ℝ) ≤
      2 * (bp.n + 1) / p * Fintype.card (Sample p bp) := by
  refine full_card_le _ (full_support hs hs' hsrc hsnk) fun hc => hne fun ω => ?_
  rw [eval_eq_iff ω hs hs']
  exact full_zero_of_allCancel _ (full_support hs hs' hsrc hsnk) hc ω

/-- **Full evaluations: identical equality is cancellation** (for `p > 2(n+1)`). -/
theorem idEq_iff_allCancel {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) (hsrc : s.2.2.1 = .src) (hsnk : s.2.2.2 = .snk)
    (hp : 2 * (bp.n + 1) < p) :
    IdenticallyEqual bp J σ e e' ↔ AllCancel bp J σ (word e - word e') := by
  classical
  constructor
  · intro hid
    by_contra hnc
    have hbound := full_card_le _ (full_support hs hs' hsrc hsnk) hnc
    have hall : (Finset.univ.filter fun ω : Sample p bp =>
        liftDB (NDim bp.n) (initDB bp J σ (unrand ω)) (word e - word e') = 0) =
        Finset.univ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact (eval_eq_iff ω hs hs').1 (hid ω)
    rw [hall, Finset.card_univ] at hbound
    have hΩ : (0 : ℝ) < Fintype.card (Sample p bp) := by
      exact_mod_cast Fintype.card_pos_iff.2 (instNonemptySampleC p bp)
    have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hlt : 2 * ((bp.n : ℝ) + 1) / p < 1 := by
      rw [div_lt_one hpR]
      exact_mod_cast hp
    nlinarith
  · intro hc ω
    rw [eval_eq_iff ω hs hs']
    exact full_zero_of_allCancel _ (full_support hs hs' hsrc hsnk) hc ω

/-- **Full evaluations: invariance.** -/
theorem full_invariance_main {σ σ' : Fin bp.ℓ → Bool} (hFE : FunctionallyEquivalent bp J σ σ')
    (hp : 2 * (bp.n + 1) < p) {e e' : QExpr p} {s : Shape} (hs : e.shape bp J = some s)
    (hs' : e'.shape bp J = some s) (hsrc : s.2.2.1 = .src) (hsnk : s.2.2.2 = .snk) :
    IdenticallyEqual bp J σ e e' ↔ IdenticallyEqual bp J σ' e e' := by
  rw [idEq_iff_allCancel hs hs' hsrc hsnk hp, idEq_iff_allCancel hs hs' hsrc hsnk hp]
  unfold AllCancel
  constructor
  · intro h u hu pr xs hr he
    exact (cancels_iff hFE _ hr).1 (h u hu pr xs hr he)
  · intro h u hu pr xs hr he
    exact (cancels_iff hFE _ hr).2 (h u hu pr xs hr he)

end FullFinal

end GGHRSW.ColoredMatrix.Collision

open GGHRSW.ColoredMatrix.Collision in
theorem solution : ∃ C : ℕ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP)
    (J : Finset (Fin bp.ℓ)) (σ σ' : Fin bp.ℓ → Bool), FunctionallyEquivalent bp J σ σ' →
    C * (bp.n + 1) < p → ∀ (e e' : QExpr p) (s : Shape),
      e.shape bp J = some s → e'.shape bp J = some s →
      (IdenticallyEqual bp J σ e e' ↔ IdenticallyEqual bp J σ' e e') := by
  refine ⟨2, ?_⟩
  intro p _ bp J σ σ' hFE hp e e' s hs hs'
  by_cases hfull : s.2.2.1 = .src ∧ s.2.2.2 = .snk
  · exact full_invariance_main hFE hp hs hs' hfull.1 hfull.2
  · have hp' : bp.n + 1 < p := by omega
    rw [idEq_iff_word_eq hs hs' hfull hp', idEq_iff_word_eq hs hs' hfull hp']
