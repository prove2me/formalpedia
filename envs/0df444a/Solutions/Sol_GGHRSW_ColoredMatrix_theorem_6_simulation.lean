-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.theorem_6_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T03:25:26.475524+00:00
-- url     : https://prove2.me/submissions/a9d9a4e0-424a-4973-871f-a9fde1597e73

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model
import Definitions.Def_GGHRSW_ColoredMatrix_Simulator
import Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_collision_bound
import Theorems.Thm_GGHRSW_ColoredMatrix_theorem_6_identity_invariance

open GGHRSW.ColoredMatrix

namespace GGHRSW.ColoredMatrix.SimulationProof

variable {p : ℕ}

/-! ### Shapes of the initial database and of expressions -/

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

lemma eval_eq_none_iff {bp : BP} {J : Finset (Fin bp.ℓ)} {db : List (Record p)}
    (hdb : db.map Record.shape = initShapes bp J) (e : QExpr p) :
    e.eval db = none ↔ e.shape bp J = none := by
  rw [← eval_map_shape hdb e, Option.map_eq_none_iff]

lemma shape_of_eval_eq_some {bp : BP} {J : Finset (Fin bp.ℓ)} {db : List (Record p)}
    (hdb : db.map Record.shape = initShapes bp J) {e : QExpr p} {r : Record p}
    (h : e.eval db = some r) : e.shape bp J = some r.shape := by
  rw [← eval_map_shape hdb e, h]
  rfl

/-! ### Identical equality -/

instance instNonemptySample (p : ℕ) [Fact p.Prime] (bp : BP) : Nonempty (Sample p bp) :=
  ⟨(fun _ => 1, fun _ => 1, fun _ _ _ => 0, fun _ _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, ⟨(0, 0, 0, 0), by simp⟩, fun _ _ _ => 0)⟩

variable [Fact p.Prime]

lemma shape_eq_of_idEq {bp : BP} {J : Finset (Fin bp.ℓ)} {τ : Fin bp.ℓ → Bool}
    {e e' : QExpr p} (h : IdenticallyEqual bp J τ e e') : e.shape bp J = e'.shape bp J := by
  obtain ⟨ω⟩ := instNonemptySample p bp
  rw [← eval_map_shape (initDB_shapes bp J τ ω) e, ← eval_map_shape (initDB_shapes bp J τ ω) e',
    h ω]

lemma idEq_of_shape_none {bp : BP} {J : Finset (Fin bp.ℓ)} (τ : Fin bp.ℓ → Bool)
    {e e' : QExpr p} (h : e.shape bp J = none) (h' : e'.shape bp J = none) :
    IdenticallyEqual bp J τ e e' := fun ω => by
  rw [(eval_eq_none_iff (initDB_shapes bp J τ ω) e).2 h,
    (eval_eq_none_iff (initDB_shapes bp J τ ω) e').2 h']

/-- Invariance on same-shape well-formed pairs extends to all pairs. -/
lemma idEq_eq_of_invariance {bp : BP} {J : Finset (Fin bp.ℓ)} {σ σ' : Fin bp.ℓ → Bool}
    (hB : ∀ (e e' : QExpr p) (s : Shape), e.shape bp J = some s → e'.shape bp J = some s →
      (IdenticallyEqual bp J σ e e' ↔ IdenticallyEqual bp J σ' e e')) :
    IdenticallyEqual (p := p) bp J σ = IdenticallyEqual bp J σ' := by
  funext e e'
  apply propext
  rcases hs : e.shape bp J with _ | s <;> rcases hs' : e'.shape bp J with _ | s'
  · exact ⟨fun _ => idEq_of_shape_none σ' hs hs', fun _ => idEq_of_shape_none σ hs hs'⟩
  · exact ⟨fun h => absurd ((shape_eq_of_idEq h).symm.trans hs) (by simp [hs']),
      fun h => absurd ((shape_eq_of_idEq h).symm.trans hs) (by simp [hs'])⟩
  · exact ⟨fun h => absurd ((shape_eq_of_idEq h).trans hs') (by simp [hs]),
      fun h => absurd ((shape_eq_of_idEq h).trans hs') (by simp [hs])⟩
  · by_cases hss : s = s'
    · subst hss
      exact hB e e' s hs hs'
    · have hne : e.shape bp J ≠ e'.shape bp J := by simp [hs, hs', hss]
      exact ⟨fun h => absurd (shape_eq_of_idEq h) hne, fun h => absurd (shape_eq_of_idEq h) hne⟩

/-! ### Coupling the real and the ideal oracle -/

section Coupling

variable {bp : BP} {J : Finset (Fin bp.ℓ)} {σ : Fin bp.ℓ → Bool}

lemma getElem?_of_forall₂ {α β : Type} {R : α → β → Prop} {f : α → Option β}
    (hR : ∀ a b, R a b ↔ f a = some b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ h : ℕ, l₂[h]? = (l₁[h]?).bind f
  | _, _, .nil, h => by simp
  | _, _, .cons hab hl, 0 => by simp [((hR _ _).1 hab)]
  | _, _, .cons _ hl, h + 1 => by simpa using getElem?_of_forall₂ hR hl h

lemma findIdx?_of_forall₂ {α β : Type} {R : α → β → Prop} (f : α → Bool) (g : β → Bool) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a ∈ l₁, ∀ b, R a b → f a = g b) → l₁.findIdx? f = l₂.findIdx? g
  | _, _, .nil, _ => rfl
  | _, _, .cons hab hl, hfg => by
    have h0 := hfg _ (by simp) _ hab
    have ih := findIdx?_of_forall₂ f g hl (fun a ha b hb => hfg a (by simp [ha]) b hb)
    simp only [List.findIdx?_cons, h0, ih]

/-- The real oracle evaluates the formal expression of the query. -/
lemma oracleStep_eq (ω : Sample p bp) {D : List (QExpr p)} {Dr : List (Record p)}
    (hrel : List.Forall₂ (fun e r => e.eval (initDB bp J σ ω) = some r) D Dr) (Q : Query p) :
    oracleStep Dr Q = respond Dr ((queryExpr D Q).bind fun e => e.eval (initDB bp J σ ω)) := by
  have hget := getElem?_of_forall₂ (f := fun e : QExpr p => e.eval (initDB bp J σ ω))
    (R := fun e r => e.eval (initDB bp J σ ω) = some r) (fun _ _ => Iff.rfl) hrel
  cases Q with
  | add h h' =>
    simp only [oracleStep, queryExpr, hget]
    rcases D[h]? with _ | e <;> rcases D[h']? with _ | e' <;> first | rfl | simp [QExpr.eval]
  | constMul h a =>
    simp only [oracleStep, queryExpr, hget]
    rcases D[h]? with _ | e
    · rfl
    · show respond Dr ((e.eval (initDB bp J σ ω)).bind fun r => some (constMulRec r a)) =
        respond Dr ((e.eval (initDB bp J σ ω)).map fun r => constMulRec r a)
      cases e.eval (initDB bp J σ ω) <;> rfl
  | mult h h' =>
    simp only [oracleStep, queryExpr, hget]
    rcases D[h]? with _ | e <;> rcases D[h']? with _ | e' <;> first | rfl | simp [QExpr.eval]

/-- One step: if no new non-identical collision happens at `ω`, the real and ideal oracles give
the same reply and stay related. -/
lemma step_couple (ω : Sample p bp) {D : List (QExpr p)} {Dr : List (Record p)}
    (hrel : List.Forall₂ (fun e r => e.eval (initDB bp J σ ω) = some r) D Dr) (Q : Query p)
    (hgood : ∀ e, queryExpr D Q = some e → ∀ x ∈ D,
      x.eval (initDB bp J σ ω) = e.eval (initDB bp J σ ω) → IdenticallyEqual bp J σ x e) :
    (idealStep bp J (IdenticallyEqual bp J σ) D Q).2 = (oracleStep Dr Q).2 ∧
      List.Forall₂ (fun e r => e.eval (initDB bp J σ ω) = some r)
        (idealStep bp J (IdenticallyEqual bp J σ) D Q).1 (oracleStep Dr Q).1 := by
  classical
  have hdb := initDB_shapes bp J σ ω
  rw [oracleStep_eq ω hrel Q]
  unfold idealStep
  rcases hq : queryExpr D Q with _ | e
  · exact ⟨rfl, hrel⟩
  · simp only [Option.bind_some]
    by_cases hs : (e.shape bp J).isNone
    · have hnone : e.eval (initDB bp J σ ω) = none :=
        (eval_eq_none_iff hdb e).2 (Option.isNone_iff_eq_none.1 hs)
      simp only [hs, if_true, hnone]
      exact ⟨rfl, hrel⟩
    · rw [if_neg hs]
      obtain ⟨r, hr⟩ : ∃ r, e.eval (initDB bp J σ ω) = some r := by
        rcases h : e.eval (initDB bp J σ ω) with _ | r
        · exact absurd (Option.isNone_iff_eq_none.2 ((eval_eq_none_iff hdb e).1 h)) hs
        · exact ⟨r, rfl⟩
      rw [hr]
      have key : D.findIdx? (fun x => decide (IdenticallyEqual bp J σ x e)) =
          Dr.findIdx? (fun x => decide (x = r)) := by
        refine findIdx?_of_forall₂ _ _ hrel ?_
        intro x hx y hxy
        simp only [decide_eq_decide]
        constructor
        · intro hid
          have := hid ω
          rw [hxy, hr] at this
          exact Option.some_injective _ this
        · intro hyr
          exact hgood e hq x hx (by rw [hxy, hr, hyr])
      simp only [respond, key]
      rcases Dr.findIdx? (fun x => decide (x = r)) with _ | h
      · refine ⟨by simp [hrel.length_eq], ?_⟩
        show List.Forall₂ _ (D ++ [e]) (Dr ++ [r])
        exact List.rel_append hrel (List.Forall₂.cons hr List.Forall₂.nil)
      · exact ⟨rfl, hrel⟩

/-- Pairs `(earlier record, new expression)` compared along the ideal run. -/
noncomputable def idealPairs (bp : BP) (J : Finset (Fin bp.ℓ)) (E : QExpr p → QExpr p → Prop)
    (A : Adversary p) (c : Fin A.K) :
    ℕ → List (QExpr p) × List (Option ℕ) → List (QExpr p × QExpr p)
  | 0, _ => []
  | k + 1, s =>
    (match queryExpr s.1 (A.next c s.2) with
      | none => []
      | some e => s.1.map fun x => (x, e)) ++
    idealPairs bp J E A c k ((idealStep bp J E s.1 (A.next c s.2)).1,
      s.2 ++ [(idealStep bp J E s.1 (A.next c s.2)).2])

lemma run_couple (A : Adversary p) (c : Fin A.K) (ω : Sample p bp) :
    ∀ (k : ℕ) (s : List (QExpr p) × List (Option ℕ)) (sr : List (Record p) × List (Option ℕ)),
      List.Forall₂ (fun e r => e.eval (initDB bp J σ ω) = some r) s.1 sr.1 → s.2 = sr.2 →
      (∀ pr ∈ idealPairs bp J (IdenticallyEqual bp J σ) A c k s,
        pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) →
          IdenticallyEqual bp J σ pr.1 pr.2) →
      (idealRunFrom bp J (IdenticallyEqual bp J σ) A c k s).2 = (runFrom A c k sr).2
  | 0, s, sr, _, h2, _ => by simpa [idealRunFrom, runFrom] using h2
  | k + 1, s, sr, hrel, h2, hgood => by
    have hstep := step_couple ω hrel (A.next c s.2) (by
      intro e he x hx hxe
      refine hgood (x, e) ?_ hxe
      simp only [idealPairs, he, List.mem_append, List.mem_map]
      exact Or.inl ⟨x, hx, rfl⟩)
    simp only [idealRunFrom, runFrom]
    rw [← h2]
    refine run_couple A c ω k _ _ hstep.2 (by simp [hstep.1]) ?_
    intro pr hpr
    exact hgood pr (by simp only [idealPairs, List.mem_append]; exact Or.inr hpr)

lemma idealStep_length (E : QExpr p → QExpr p → Prop) (D : List (QExpr p)) (Q : Query p) :
    (idealStep bp J E D Q).1.length ≤ D.length + 1 := by
  classical
  unfold idealStep
  rcases queryExpr D Q with _ | e
  · simp
  · simp only
    split_ifs
    · simp
    · rcases D.findIdx? (fun x => decide (E x e)) with _ | h <;> simp

lemma idealPairs_length (E : QExpr p → QExpr p → Prop) (A : Adversary p) (c : Fin A.K) :
    ∀ (k : ℕ) (s : List (QExpr p) × List (Option ℕ)),
      (idealPairs bp J E A c k s).length ≤ k * (s.1.length + k)
  | 0, _ => by simp [idealPairs]
  | k + 1, s => by
    have ih := idealPairs_length E A c k ((idealStep bp J E s.1 (A.next c s.2)).1,
      s.2 ++ [(idealStep bp J E s.1 (A.next c s.2)).2])
    have hl := idealStep_length (bp := bp) (J := J) E s.1 (A.next c s.2)
    have hfirst : (match queryExpr s.1 (A.next c s.2) with
        | none => []
        | some e => s.1.map fun x => (x, e)).length ≤ s.1.length := by
      rcases queryExpr s.1 (A.next c s.2) with _ | e <;> simp
    simp only [idealPairs, List.length_append]
    have h3 : k * ((idealStep bp J E s.1 (A.next c s.2)).1.length + k) ≤
        k * (s.1.length + 1 + k) := Nat.mul_le_mul_left _ (by omega)
    nlinarith

end Coupling

/-! ### Counting -/

open Classical in
lemma card_exists_mem_le {α Ω : Type} [Fintype Ω] (B : α → Ω → Prop) :
    ∀ L : List α, (Finset.univ.filter fun ω => ∃ a ∈ L, B a ω).card ≤
      (L.map fun a => (Finset.univ.filter fun ω => B a ω).card).sum
  | [] => by simp
  | a :: L => by
    classical
    have ih := card_exists_mem_le B L
    calc (Finset.univ.filter fun ω => ∃ x ∈ a :: L, B x ω).card
        = ((Finset.univ.filter fun ω => B a ω) ∪
            (Finset.univ.filter fun ω => ∃ x ∈ L, B x ω)).card := by
          congr 1
          ext ω
          simp
      _ ≤ (Finset.univ.filter fun ω => B a ω).card +
            (Finset.univ.filter fun ω => ∃ x ∈ L, B x ω).card := Finset.card_union_le _ _
      _ ≤ _ := by
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add_left ih _

lemma initShapes_length (bp : BP) (J : Finset (Fin bp.ℓ)) :
    (initShapes bp J).length = dbSize bp J := by
  have aux : ∀ l : List (Fin bp.n),
      (l.map fun i => if bp.inp i ∈ J then 2 else 4).sum =
        (l.filter fun i => bp.inp i ∈ J).length +
          (l.filter fun i => bp.inp i ∈ J).length +
          (2 * (l.filter fun i => bp.inp i ∉ J).length +
            2 * (l.filter fun i => bp.inp i ∉ J).length) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases h : bp.inp a ∈ J <;> simp [List.filter_cons, h, ih] <;> ring
  unfold initShapes programShapes dbSize
  rw [Fin.sum_univ_def, aux]
  simp [List.length_flatMap]
  ring

/-- The real view coincides with the simulated one outside the union of the pairwise collision
events of the ideal run. -/
lemma view_ne_imp (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (A : Adversary p)
    (c : Fin A.K) (ω : Sample p bp)
    (h : view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c) :
    ∃ pr ∈ idealPairs bp J (IdenticallyEqual bp J σ) A c A.q (initExprs bp J, []),
      pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
        ¬ IdenticallyEqual bp J σ pr.1 pr.2 := by
  by_contra hcon
  push_neg at hcon
  apply h
  have hrel : List.Forall₂ (fun e r => e.eval (initDB bp J σ ω) = some r)
      (initExprs bp J : List (QExpr p)) (initDB bp J σ ω) := by
    have hlen : (initDB bp J σ ω).length = (initShapes bp J).length := by
      rw [← initDB_shapes bp J σ ω, List.length_map]
    rw [List.forall₂_iff_get]
    refine ⟨by simp [initExprs, hlen], ?_⟩
    intro i h1 h2
    simp [initExprs, QExpr.eval]
  exact (run_couple A c ω A.q (initExprs bp J, []) (initDB bp J σ ω, []) hrel rfl hcon).symm

open Classical in
/-- Per-pair collision bound, in counting form, from the collision child lemma. -/
lemma pair_card_le {CA : ℝ}
    (hA : ∀ (p : ℕ) [Fact p.Prime] (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
      (e e' : QExpr p) (s : Shape),
      e.shape bp J = some s → e'.shape bp J = some s → ¬ IdenticallyEqual bp J σ e e' →
        ((Finset.univ.filter fun ω : Sample p bp =>
            e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω)).card : ℝ) /
          Fintype.card (Sample p bp) ≤ CA * (bp.n + 1) / p)
    (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (e e' : QExpr p) :
    ((Finset.univ.filter fun ω : Sample p bp =>
        e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) ∧
          ¬ IdenticallyEqual bp J σ e e').card : ℝ) ≤
      max CA 0 * (bp.n + 1) / p * Fintype.card (Sample p bp) := by
  classical
  have hΩ : (0 : ℝ) < Fintype.card (Sample p bp) := by
    exact_mod_cast Fintype.card_pos_iff.2 (instNonemptySample p bp)
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnonneg : 0 ≤ max CA 0 * (bp.n + 1) / p * Fintype.card (Sample p bp) := by
    have : (0 : ℝ) ≤ max CA 0 := le_max_right _ _
    positivity
  by_cases hid : IdenticallyEqual bp J σ e e'
  · have hempty : (Finset.univ.filter fun ω : Sample p bp =>
        e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) ∧
          ¬ IdenticallyEqual bp J σ e e') = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and, not_not]
      exact fun _ => hid
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact hnonneg
  · by_cases hs : ∃ s, e.shape bp J = some s ∧ e'.shape bp J = some s
    · obtain ⟨s, hs1, hs2⟩ := hs
      have h := hA p bp J σ e e' s hs1 hs2 hid
      have hfilter : (Finset.univ.filter fun ω : Sample p bp =>
          e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) ∧
            ¬ IdenticallyEqual bp J σ e e') =
          Finset.univ.filter fun ω : Sample p bp =>
            e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) := by
        ext ω
        simp [hid]
      rw [hfilter]
      rw [div_le_iff₀ hΩ] at h
      calc _ ≤ CA * (bp.n + 1) / p * Fintype.card (Sample p bp) := h
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · have hempty : (Finset.univ.filter fun ω : Sample p bp =>
          e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω) ∧
            ¬ IdenticallyEqual bp J σ e e') = ∅ := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and, not_not]
        intro heq
        exfalso
        have hdb := initDB_shapes bp J σ ω
        have hsh : e.shape bp J = e'.shape bp J := by
          rw [← eval_map_shape hdb e, ← eval_map_shape hdb e', heq]
        rcases hse : e.shape bp J with _ | s
        · exact hid (idEq_of_shape_none σ hse (hsh ▸ hse))
        · exact hs ⟨s, hse, hsh ▸ hse⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact hnonneg

open Classical in
/-- The main estimate: the real view differs from the simulated view with probability at most
`q (|DB| + q) · C (n+1) / p`. -/
lemma view_ideal_bound {CA : ℝ}
    (hA : ∀ (p : ℕ) [Fact p.Prime] (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
      (e e' : QExpr p) (s : Shape),
      e.shape bp J = some s → e'.shape bp J = some s → ¬ IdenticallyEqual bp J σ e e' →
        ((Finset.univ.filter fun ω : Sample p bp =>
            e.eval (initDB bp J σ ω) = e'.eval (initDB bp J σ ω)).card : ℝ) /
          Fintype.card (Sample p bp) ≤ CA * (bp.n + 1) / p)
    (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (A : Adversary p) :
    ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
        view bp J σ A x.1 x.2 ≠ idealView bp J (IdenticallyEqual bp J σ) A x.1).card : ℝ) /
      Fintype.card (Fin A.K × Sample p bp) ≤
    (A.q * (dbSize bp J + A.q) : ℕ) * (max CA 0 * (bp.n + 1) / p) := by
  classical
  set M : ℝ := max CA 0 * (bp.n + 1) / p * Fintype.card (Sample p bp) with hM
  have hΩ : (0 : ℝ) < Fintype.card (Sample p bp) := by
    exact_mod_cast Fintype.card_pos_iff.2 (instNonemptySample p bp)
  -- the bound for each coin
  have hcoin : ∀ c : Fin A.K,
      ((Finset.univ.filter fun ω : Sample p bp =>
        view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c).card : ℝ) ≤
        (A.q * (dbSize bp J + A.q) : ℕ) * M := by
    intro c
    set L := idealPairs bp J (IdenticallyEqual bp J σ) A c A.q (initExprs bp J, [])
    have hsub : (Finset.univ.filter fun ω : Sample p bp =>
        view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c) ⊆
        Finset.univ.filter fun ω => ∃ pr ∈ L,
          pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
            ¬ IdenticallyEqual bp J σ pr.1 pr.2 := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact view_ne_imp bp J σ A c ω hω
    have h1 : (Finset.univ.filter fun ω : Sample p bp =>
        view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c).card ≤
        (L.map fun pr => (Finset.univ.filter fun ω : Sample p bp =>
          pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
            ¬ IdenticallyEqual bp J σ pr.1 pr.2).card).sum := by
      refine Nat.le_trans (Finset.card_le_card hsub) ?_
      convert card_exists_mem_le (fun pr ω =>
        pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
          ¬ IdenticallyEqual bp J σ pr.1 pr.2) L
    have h2 : ((L.map fun pr => (Finset.univ.filter fun ω : Sample p bp =>
        pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
          ¬ IdenticallyEqual bp J σ pr.1 pr.2).card).sum : ℝ) ≤ L.length * M := by
      rw [Nat.cast_list_sum, List.map_map]
      have := List.sum_le_card_nsmul (L.map ((fun n : ℕ => (n : ℝ)) ∘ fun pr =>
        (Finset.univ.filter fun ω : Sample p bp =>
          pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
            ¬ IdenticallyEqual bp J σ pr.1 pr.2).card)) M (by
        intro x hx
        simp only [List.mem_map, Function.comp] at hx
        obtain ⟨pr, _, rfl⟩ := hx
        exact pair_card_le hA bp J σ pr.1 pr.2)
      simpa using this
    have hlen : L.length ≤ A.q * (dbSize bp J + A.q) := by
      have := idealPairs_length (bp := bp) (J := J) (IdenticallyEqual bp J σ) A c A.q
        (initExprs bp J, [])
      have hl : (initExprs bp J : List (QExpr p)).length = dbSize bp J := by
        simp [initExprs, initShapes_length]
      rw [hl] at this
      exact this
    have hM0 : 0 ≤ M := by
      have : (0 : ℝ) ≤ max CA 0 := le_max_right _ _
      have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      positivity
    calc _ ≤ ((L.map fun pr => (Finset.univ.filter fun ω : Sample p bp =>
            pr.1.eval (initDB bp J σ ω) = pr.2.eval (initDB bp J σ ω) ∧
              ¬ IdenticallyEqual bp J σ pr.1 pr.2).card).sum : ℝ) := by exact_mod_cast h1
      _ ≤ L.length * M := h2
      _ ≤ _ := by
        have : (L.length : ℝ) ≤ ((A.q * (dbSize bp J + A.q) : ℕ) : ℝ) := by exact_mod_cast hlen
        gcongr
  -- sum over the coins
  have hsum : ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
      view bp J σ A x.1 x.2 ≠ idealView bp J (IdenticallyEqual bp J σ) A x.1).card : ℝ) =
      ∑ c : Fin A.K, ((Finset.univ.filter fun ω : Sample p bp =>
        view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.card_filter, Nat.cast_sum]
  rw [hsum, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, div_le_iff₀ (by
    have : (0 : ℝ) < A.K := by exact_mod_cast A.K_pos
    positivity)]
  calc ∑ c : Fin A.K, ((Finset.univ.filter fun ω : Sample p bp =>
        view bp J σ A c ω ≠ idealView bp J (IdenticallyEqual bp J σ) A c).card : ℝ)
      ≤ ∑ _c : Fin A.K, ((A.q * (dbSize bp J + A.q) : ℕ) : ℝ) * M :=
        Finset.sum_le_sum fun c _ => hcoin c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hM]; ring

end GGHRSW.ColoredMatrix.SimulationProof

open GGHRSW.ColoredMatrix.SimulationProof in
theorem solution : ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime] (bp : BP), 0 < bp.n →
    ∀ (J : Finset (Fin bp.ℓ)) (A : Adversary p),
    ∃ Sim : ((Fin bp.ℓ → Bool) → Bool) → Fin A.K → List (Option ℕ),
      ∀ σ : Fin bp.ℓ → Bool,
        ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
            view bp J σ A x.1 x.2 ≠ Sim (fun χ => bp.eval (fix J σ χ)) x.1).card : ℝ) /
          Fintype.card (Fin A.K × Sample p bp) ≤
        C * bp.n * ((dbSize bp J + A.q : ℕ) : ℝ) ^ 2 / p := by
  obtain ⟨CA, hA⟩ := theorem_6_collision_bound
  obtain ⟨CB, hB⟩ := theorem_6_identity_invariance
  refine ⟨2 * max CA 0 + 2 * CB, ?_⟩
  intro p _ bp hn J A
  classical
  refine ⟨fun f c => if h : ∃ τ : Fin bp.ℓ → Bool, (fun χ => bp.eval (fix J τ χ)) = f then
    idealView bp J (IdenticallyEqual bp J h.choose) A c else [], ?_⟩
  intro σ
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnR : (1 : ℝ) ≤ bp.n := by exact_mod_cast hn
  have hCA : (0 : ℝ) ≤ max CA 0 := le_max_right _ _
  have hCB : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
  set T : ℝ := ((dbSize bp J + A.q : ℕ) : ℝ) with hT
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hT]
    exact_mod_cast (by unfold dbSize; omega : 1 ≤ dbSize bp J + A.q)
  have : Nonempty (Fin A.K) := ⟨⟨0, A.K_pos⟩⟩
  have hΩK : (0 : ℝ) < Fintype.card (Fin A.K × Sample p bp) := by
    exact_mod_cast Fintype.card_pos
  by_cases hpl : CB * (bp.n + 1) < p
  · -- Large `p`: the simulator equals the ideal oracle of `σ` and the collision bound applies.
    have hSim : ∀ c, (if h : ∃ τ : Fin bp.ℓ → Bool,
        (fun χ => bp.eval (fix J τ χ)) = (fun χ => bp.eval (fix J σ χ)) then
          idealView bp J (IdenticallyEqual bp J h.choose) A c else []) =
        idealView bp J (IdenticallyEqual bp J σ) A c := by
      intro c
      have hex : ∃ τ : Fin bp.ℓ → Bool,
          (fun χ => bp.eval (fix J τ χ)) = (fun χ => bp.eval (fix J σ χ)) := ⟨σ, rfl⟩
      rw [dif_pos hex]
      have hFE : FunctionallyEquivalent bp J hex.choose σ := fun x => congrFun hex.choose_spec x
      rw [idEq_eq_of_invariance (hB p bp J hex.choose σ hFE hpl)]
    simp only [hSim]
    refine (view_ideal_bound hA bp J σ A).trans ?_
    have hq : ((A.q * (dbSize bp J + A.q) : ℕ) : ℝ) ≤ T ^ 2 := by
      rw [hT]
      push_cast
      nlinarith [(Nat.cast_nonneg (dbSize bp J) : (0 : ℝ) ≤ dbSize bp J)]
    have hq0 : (0 : ℝ) ≤ ((A.q * (dbSize bp J + A.q) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((A.q * (dbSize bp J + A.q) : ℕ) : ℝ) * (max CA 0 * (bp.n + 1) / p)
        ≤ T ^ 2 * (max CA 0 * (2 * bp.n) / p) := by
          gcongr
          linarith
      _ = 2 * max CA 0 * bp.n * T ^ 2 / p := by ring
      _ ≤ (2 * max CA 0 + 2 * CB) * bp.n * T ^ 2 / p := by
          gcongr
          linarith
  · -- Small `p`: the bound is at least `1`.
    push_neg at hpl
    have hpl' : (p : ℝ) ≤ CB * (bp.n + 1) := by exact_mod_cast hpl
    have hfrac : ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
        view bp J σ A x.1 x.2 ≠ (if h : ∃ τ : Fin bp.ℓ → Bool,
          (fun χ => bp.eval (fix J τ χ)) = (fun χ => bp.eval (fix J σ χ)) then
            idealView bp J (IdenticallyEqual bp J h.choose) A x.1 else [])).card : ℝ) /
        Fintype.card (Fin A.K × Sample p bp) ≤ 1 := by
      rw [div_le_one hΩK]
      exact_mod_cast Finset.card_le_univ _
    refine hfrac.trans ?_
    rw [le_div_iff₀ hp]
    have hT2 : (1 : ℝ) ≤ T ^ 2 := by nlinarith
    nlinarith [mul_nonneg hCA (by linarith : (0 : ℝ) ≤ bp.n), mul_nonneg hCB (by linarith : (0 : ℝ) ≤ bp.n)]
