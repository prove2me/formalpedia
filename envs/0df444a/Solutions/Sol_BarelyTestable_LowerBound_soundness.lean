-- Prove2me | solution 1 for BarelyTestable.LowerBound.soundness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:34:26.521719+00:00
-- url     : https://prove2.me/submissions/672a349a-87d3-4b40-95bc-49e3adb9156e

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads
import Theorems.Thm_BarelyTestable_LowerBound_square_slack
import Theorems.Thm_BarelyTestable_LowerBound_repair_propagation
import Theorems.Thm_BarelyTestable_LowerBound_load_second_moment
import Theorems.Thm_BarelyTestable_LowerBound_balanced_centers

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_soundness

/-! ### Points of the cube as tuples `(X, Y, a, b)` -/

/-- The cube point with control parts `X`, `Y` and action bits `a`, `b`
(the same expression as inside `residual`). -/
noncomputable def emb {m : ℕ} (X Y : HalfSet m) (a b : Bool) : Cube (Coord m) :=
  (X.image (fun x => Sum.inr (Sum.inl x) : Half m → Coord m)) ∪
    (Y.image (fun y => Sum.inr (Sum.inr y) : Half m → Coord m)) ∪
    (if a then {actionA} else ∅) ∪ (if b then {actionB} else ∅)

lemma xPart_emb {m : ℕ} (X Y : HalfSet m) (a b : Bool) : xPart (emb X Y a b) = X := by
  ext x; cases a <;> cases b <;> simp [emb, xPart, actionA, actionB]

lemma yPart_emb {m : ℕ} (X Y : HalfSet m) (a b : Bool) : yPart (emb X Y a b) = Y := by
  ext x; cases a <;> cases b <;> simp [emb, yPart, actionA, actionB]

lemma actionA_mem_emb {m : ℕ} (X Y : HalfSet m) (a b : Bool) :
    (actionA : Coord m) ∈ emb X Y a b ↔ a = true := by
  cases a <;> cases b <;> simp [emb, actionA, actionB]

lemma actionB_mem_emb {m : ℕ} (X Y : HalfSet m) (a b : Bool) :
    (actionB : Coord m) ∈ emb X Y a b ↔ b = true := by
  cases a <;> cases b <;> simp [emb, actionA, actionB]

lemma hard_emb {m : ℕ} (r : Sample m) (X Y : HalfSet m) (a b : Bool) :
    hard r false (emb X Y a b) = slice r false X Y a b := by
  cases a <;> cases b <;> simp [hard, xPart_emb, yPart_emb, actionA_mem_emb, actionB_mem_emb]

lemma emb_parts {m : ℕ} (S : Cube (Coord m)) :
    emb (xPart S) (yPart S) (decide (actionA ∈ S)) (decide (actionB ∈ S)) = S := by
  ext z
  rcases z with c | h | h
  · by_cases hA : (actionA : Coord m) ∈ S <;> by_cases hB : (actionB : Coord m) ∈ S <;>
      cases c <;> simp_all [emb, actionA, actionB]
  · simp [emb, xPart]; split_ifs <;> simp [actionA, actionB]
  · simp [emb, yPart]; split_ifs <;> simp [actionA, actionB]

lemma residual_true {m : ℕ} (r : Sample m) (G : Oracle (Coord m)) (Y : HalfSet m) (b : Bool)
    (X : HalfSet m) :
    residual r G true Y b X = G (emb X Y false b) - hard r false (emb X Y false b) := by
  rw [hard_emb]; rfl

lemma residual_false {m : ℕ} (r : Sample m) (G : Oracle (Coord m)) (X : HalfSet m) (b : Bool)
    (Y : HalfSet m) :
    residual r G false X b Y = G (emb X Y true b) - hard r false (emb X Y true b) := by
  rw [hard_emb]; rfl

lemma center_swap {m : ℕ} (φA φB : LabelMap m) (X Y : HalfSet m) :
    Center φB φA Y X ↔ Center φA φB X Y := by
  simp only [Center, alpha, beta, Prod.ext_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩

/-! ### A center forces a changed corner -/

lemma corner_change {m : ℕ} (hm : 9 ≤ m) (r : Sample m) (G : Oracle (Coord m))
    (hG : Submodular G) (X Y : HalfSet m) (hc : Center r.1 r.2.1 X Y) :
    ∃ ab : Bool × Bool, G (emb X Y ab.1 ab.2) ≠ hard r false (emb X Y ab.1 ab.2) := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ a b : Bool, G (emb X Y a b) = hard r false (emb X Y a b) :=
    fun a b => hcon (a, b)
  have hAB : (actionA : Coord m) ≠ actionB := by simp [actionA, actionB]
  have hA0 : (actionA : Coord m) ∉ emb X Y false false := by simp [actionA_mem_emb]
  have hB0 : (actionB : Coord m) ∉ emb X Y false false := by simp [actionB_mem_emb]
  have hv : ValidSquare (emb X Y false false) actionA actionB := ⟨hAB, hA0, hB0⟩
  have h1 := (square_slack hm r false (emb X Y false false) actionA actionB hv).1
    ⟨by rwa [xPart_emb, yPart_emb], Or.inl ⟨rfl, rfl⟩⟩
  have e10 : insert actionA (emb X Y false false) = emb X Y true false := by
    ext z; simp [emb]
  have e01 : insert actionB (emb X Y false false) = emb X Y false true := by
    ext z; simp [emb]
  have e11 : insert actionA (insert actionB (emb X Y false false)) = emb X Y true true := by
    ext z; simp [emb]
  have hU : insert actionA (emb X Y false false) ∪ insert actionB (emb X Y false false) =
      emb X Y true true := by
    rw [← e11]; ext z; simp; tauto
  have hI : insert actionA (emb X Y false false) ∩ insert actionB (emb X Y false false) =
      emb X Y false false := by
    ext z; simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.symm.trans h2) hAB
      · exact h2
      · exact h1
      · exact h1
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
  have hsub := hG (insert actionA (emb X Y false false)) (insert actionB (emb X Y false false))
  rw [hU, hI, e10, e01] at hsub
  simp only [slack] at h1
  rw [e11, e10, e01] at h1
  rw [hall, hall, hall, hall] at hsub
  have hpos : (0 : ℝ) < 2 ^ dimension m := by positivity
  have : (if false = true then (1 : ℝ) else -1) / 2 ^ dimension m < 0 := by
    simp only [Bool.false_eq_true, if_false]
    exact div_neg_of_neg_of_pos (by norm_num) hpos
  linarith

/-! ### Loads of cube points -/

/-- The load assigned to a cube point (`L_τ(X,Y)` in the paper). -/
noncomputable def Ld {m : ℕ} (φA φB : LabelMap m) (x : Cube (Coord m)) : ℕ :=
  if (actionA : Coord m) ∈ x then loadX φA φB (xPart x) (yPart x)
  else loadY φA φB (yPart x) (xPart x)

/-- The triples counted by the load of the cube point `x`. -/
def LdPred {m : ℕ} (φA φB : LabelMap m) (x : Cube (Coord m))
    (t : HalfSet m × Selector m × Selector m) : Prop :=
  if (actionA : Coord m) ∈ x then
    Center φB φA t.1 (xPart x) ∧ LeadsTo t.1 (selected t.2.1) (selected t.2.2) (yPart x)
  else Center φA φB t.1 (yPart x) ∧ LeadsTo t.1 (selected t.2.1) (selected t.2.2) (xPart x)

lemma LdPred_pos {m : ℕ} (φA φB : LabelMap m) (x : Cube (Coord m))
    (t : HalfSet m × Selector m × Selector m) (h : (actionA : Coord m) ∈ x) :
    LdPred φA φB x t ↔
      Center φB φA t.1 (xPart x) ∧ LeadsTo t.1 (selected t.2.1) (selected t.2.2) (yPart x) := by
  unfold LdPred; rw [if_pos h]

lemma LdPred_neg {m : ℕ} (φA φB : LabelMap m) (x : Cube (Coord m))
    (t : HalfSet m × Selector m × Selector m) (h : (actionA : Coord m) ∉ x) :
    LdPred φA φB x t ↔
      Center φA φB t.1 (yPart x) ∧ LeadsTo t.1 (selected t.2.1) (selected t.2.2) (xPart x) := by
  unfold LdPred; rw [if_neg h]

open Classical in
lemma Ld_eq {m : ℕ} (φA φB : LabelMap m) (x : Cube (Coord m)) :
    (Finset.univ.filter (LdPred φA φB x)).card = Ld φA φB x := by
  by_cases h : (actionA : Coord m) ∈ x
  · rw [Ld, if_pos h]; unfold loadX loadY
    congr 1; ext t; simp only [Finset.mem_filter, LdPred_pos φA φB x t h]
  · rw [Ld, if_neg h]; unfold loadY
    congr 1; ext t; simp only [Finset.mem_filter, LdPred_neg φA φB x t h]

/-! ### The repaired slice attached to a center and a corner -/

/-- The residual function `g_{Y,τ}` (if `a = false`) or `g_{X,τ}` (if `a = true`). -/
noncomputable def gf {m : ℕ} (r : Sample m) (G : Oracle (Coord m)) (c : HalfSet m × HalfSet m)
    (a b : Bool) : HalfSet m → ℝ :=
  if a then residual r G false c.1 b else residual r G true c.2 b

/-- The varying coordinate of the center. -/
def Zf {m : ℕ} (c : HalfSet m × HalfSet m) (a : Bool) : HalfSet m := if a then c.2 else c.1

/-- The cube point at which `gf` is evaluated. -/
noncomputable def ptf {m : ℕ} (c : HalfSet m × HalfSet m) (a b : Bool) (U : HalfSet m) :
    Cube (Coord m) :=
  if a then emb c.1 U true b else emb U c.2 false b

lemma gf_eq {m : ℕ} (r : Sample m) (G : Oracle (Coord m)) (c : HalfSet m × HalfSet m)
    (a b : Bool) (U : HalfSet m) :
    gf r G c a b U = G (ptf c a b U) - hard r false (ptf c a b U) := by
  cases a
  · simp [gf, ptf, residual_true]
  · simp [gf, ptf, residual_false]

lemma ptf_Z {m : ℕ} (c : HalfSet m × HalfSet m) (a b : Bool) :
    ptf c a b (Zf c a) = emb c.1 c.2 a b := by
  cases a <;> rfl

lemma pp_bound {m : ℕ} (hm : 1 ≤ m) (r : Sample m) (G : Oracle (Coord m)) (hG : Submodular G)
    (c : HalfSet m × HalfSet m) (a b : Bool) (hbal : Balanced (Zf c a))
    (hne : gf r G c a b (Zf c a) ≠ 0) :
    (m : ℝ) ^ (2 * m) / 4 ≤ propagatedPairs (gf r G c a b) (Zf c a) := by
  cases a
  · exact repair_propagation hm r G hG true c.2 c.1 b hbal hne
  · exact repair_propagation hm r G hG false c.1 c.2 b hbal hne

/-- The pairs `(Γ, Γ')` counted by `propagatedPairs`. -/
def Good {m : ℕ} (g : HalfSet m → ℝ) (Z : HalfSet m) (p : Selector m × Selector m) : Prop :=
  g (Z ∪ selected p.1) ≠ 0 ∨ g (Z \ selected p.1) ≠ 0 ∨
    g (xorSet Z (selected p.1) ∪ selected p.2) ≠ 0

open Classical in
lemma good_card {m : ℕ} (g : HalfSet m → ℝ) (Z : HalfSet m) :
    (Finset.univ.filter (Good g Z)).card = propagatedPairs g Z := by
  unfold propagatedPairs Good; convert rfl

/-- A changed point reached from `Z` along the pair `p`. -/
noncomputable def pick {m : ℕ} (g : HalfSet m → ℝ) (Z : HalfSet m) (p : Selector m × Selector m) :
    HalfSet m := by
  classical
  exact if g (Z ∪ selected p.1) ≠ 0 then Z ∪ selected p.1
    else if g (Z \ selected p.1) ≠ 0 then Z \ selected p.1
    else xorSet Z (selected p.1) ∪ selected p.2

lemma pick_spec {m : ℕ} (g : HalfSet m → ℝ) (Z : HalfSet m) (p : Selector m × Selector m)
    (h : Good g Z p) :
    g (pick g Z p) ≠ 0 ∧ LeadsTo Z (selected p.1) (selected p.2) (pick g Z p) := by
  unfold pick Good at *
  split_ifs with h1 h2
  · exact ⟨h1, Or.inl rfl⟩
  · exact ⟨h2, Or.inr (Or.inl rfl)⟩
  · refine ⟨?_, Or.inr (Or.inr rfl)⟩
    rcases h with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

/-- A corner of the center `c` at which `G` differs from the hard function. -/
noncomputable def corner {m : ℕ} (r : Sample m) (G : Oracle (Coord m))
    (c : HalfSet m × HalfSet m) : Bool × Bool := by
  classical
  exact if h : ∃ ab : Bool × Bool,
      G (emb c.1 c.2 ab.1 ab.2) ≠ hard r false (emb c.1 c.2 ab.1 ab.2) then h.choose
    else (false, false)

lemma corner_spec {m : ℕ} (r : Sample m) (G : Oracle (Coord m)) (c : HalfSet m × HalfSet m)
    (h : ∃ ab : Bool × Bool,
      G (emb c.1 c.2 ab.1 ab.2) ≠ hard r false (emb c.1 c.2 ab.1 ab.2)) :
    G (emb c.1 c.2 (corner r G c).1 (corner r G c).2) ≠
      hard r false (emb c.1 c.2 (corner r G c).1 (corner r G c).2) := by
  unfold corner; rw [dif_pos h]; exact h.choose_spec

lemma ldpred_ptf {m : ℕ} (φA φB : LabelMap m) (c : HalfSet m × HalfSet m) (a b : Bool)
    (U : HalfSet m) (p : Selector m × Selector m) (hcen : Center φA φB c.1 c.2)
    (hL : LeadsTo (Zf c a) (selected p.1) (selected p.2) U) :
    LdPred φA φB (ptf c a b U) (Zf c a, p.1, p.2) := by
  cases a
  · have hA : (actionA : Coord m) ∉ ptf c false b U := by
      simp [ptf, actionA_mem_emb]
    rw [LdPred_neg φA φB _ _ hA]
    simp only [ptf, Zf, xPart_emb, yPart_emb, Bool.false_eq_true, if_false] at hL ⊢
    exact ⟨hcen, hL⟩
  · have hA : (actionA : Coord m) ∈ ptf c true b U := by
      simp [ptf, actionA_mem_emb]
    rw [LdPred_pos φA φB _ _ hA]
    simp only [ptf, Zf, xPart_emb, yPart_emb, if_true] at hL ⊢
    exact ⟨(center_swap φA φB c.1 c.2).2 hcen, hL⟩

lemma ptf_inj {m : ℕ} (c c' : HalfSet m × HalfSet m) (a a' b b' : Bool) (U U' : HalfSet m)
    (h : ptf c a b U = ptf c' a' b' U') (hZ : Zf c a = Zf c' a') : c = c' := by
  have ha : a = a' := by
    have := congrArg (fun x => (actionA : Coord m) ∈ x) h
    cases a <;> cases a' <;> simp [ptf, actionA_mem_emb] at this ⊢
  subst ha
  cases a
  · have h2 := congrArg yPart h
    simp only [ptf, Zf, yPart_emb, Bool.false_eq_true, if_false] at h2 hZ
    exact Prod.ext hZ h2
  · have h1 := congrArg xPart h
    simp only [ptf, Zf, xPart_emb, if_true] at h1 hZ
    exact Prod.ext h1 hZ

/-- Equation (1), first inequality: charging balanced centers to changed points. -/
lemma charging {m : ℕ} (hm : 9 ≤ m) (r : Sample m) (G : Oracle (Coord m)) (hG : Submodular G)
    (S : Finset (Cube (Coord m))) (hS : ∀ x, G x ≠ hard r false x → x ∈ S) :
    (m : ℝ) ^ (2 * m) / 4 * (balancedCenters r.1 r.2.1 : ℝ) ≤
      ∑ x ∈ S, (Ld r.1 r.2.1 x : ℝ) := by
  classical
  set φA := r.1 with hφA
  set φB := r.2.1 with hφB
  set Cset := Finset.univ.filter (fun c : HalfSet m × HalfSet m =>
    Center φA φB c.1 c.2 ∧ Balanced c.1 ∧ Balanced c.2) with hCset
  have hBC : balancedCenters φA φB = Cset.card := by unfold balancedCenters; convert rfl
  let A : HalfSet m × HalfSet m → Bool := fun c => (corner r G c).1
  let B : HalfSet m × HalfSet m → Bool := fun c => (corner r G c).2
  let g : HalfSet m × HalfSet m → HalfSet m → ℝ := fun c => gf r G c (A c) (B c)
  let Z : HalfSet m × HalfSet m → HalfSet m := fun c => Zf c (A c)
  let Q := Cset.sigma (fun c => Finset.univ.filter (Good (g c) (Z c)))
  let T := S.sigma (fun x => Finset.univ.filter (LdPred φA φB x))
  have hQ : (m : ℝ) ^ (2 * m) / 4 * Cset.card ≤ Q.card := by
    rw [Finset.card_sigma, Nat.cast_sum, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨_, hcen, hbX, hbY⟩ := hc
    have hex := corner_change hm r G hG c.1 c.2 hcen
    have hsp := corner_spec r G c hex
    rw [good_card]
    apply pp_bound (by omega) r G hG
    · show Balanced (Zf c (A c)); unfold Zf; split_ifs <;> assumption
    · rw [gf_eq, ptf_Z]; exact sub_ne_zero.mpr hsp
  have hT : (T.card : ℝ) = ∑ x ∈ S, (Ld φA φB x : ℝ) := by
    rw [Finset.card_sigma, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Ld_eq]
  let f : (Σ _ : HalfSet m × HalfSet m, Selector m × Selector m) →
      (Σ _ : Cube (Coord m), HalfSet m × Selector m × Selector m) :=
    fun q => ⟨ptf q.1 (A q.1) (B q.1) (pick (g q.1) (Z q.1) q.2), (Z q.1, q.2.1, q.2.2)⟩
  have hmaps : ∀ q ∈ Q, f q ∈ T := by
    rintro ⟨c, p⟩ hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hc, hp⟩ := hq
    have hgood := (Finset.mem_filter.1 hp).2
    have hc := (Finset.mem_filter.1 hc).2
    obtain ⟨hU, hL⟩ := pick_spec (g c) (Z c) p hgood
    rw [Finset.mem_sigma, Finset.mem_filter]
    refine ⟨hS _ ?_, Finset.mem_univ _, ldpred_ptf φA φB c (A c) (B c) _ p hc.1 hL⟩
    have := hU
    simp only [g, gf_eq] at this
    exact fun h => this (by rw [h]; ring)
  have hinj : Set.InjOn f Q := by
    rintro ⟨c, p⟩ - ⟨c', p'⟩ - hf
    simp only [f, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hf
    obtain ⟨h1, h2, h3, h4⟩ := hf
    have hc : c = c' := ptf_inj c c' _ _ _ _ _ _ h1 h2
    subst hc
    have hp : p = p' := Prod.ext h3 h4
    subst hp
    rfl
  have hle := Finset.card_le_card_of_injOn f hmaps hinj
  rw [hBC, ← hT]
  calc (m : ℝ) ^ (2 * m) / 4 * Cset.card ≤ Q.card := hQ
    _ ≤ T.card := by exact_mod_cast hle

/-! ### Sum of squared loads over the cube -/

lemma sum_Ld_sq_le {m : ℕ} (φA φB : LabelMap m) :
    ∑ x : Cube (Coord m), (Ld φA φB x : ℝ) ^ 2 ≤ totalSquaredLoad φA φB := by
  classical
  let π : Cube (Coord m) → HalfSet m × HalfSet m × Bool × Bool :=
    fun x => (xPart x, yPart x, decide (actionA ∈ x), decide (actionB ∈ x))
  let F : HalfSet m × HalfSet m × Bool × Bool → ℝ :=
    fun q => (((if q.2.2.1 then loadX φA φB q.1 q.2.1 else loadY φA φB q.2.1 q.1 : ℕ)) : ℝ) ^ 2
  have hπ : Function.Injective π := by
    intro x y h
    simp only [π, Prod.mk.injEq] at h
    rw [← emb_parts x, ← emb_parts y, h.1, h.2.1, h.2.2.1, h.2.2.2]
  have h1 : ∑ x : Cube (Coord m), (Ld φA φB x : ℝ) ^ 2 = ∑ q ∈ Finset.univ.image π, F q := by
    rw [Finset.sum_image (fun x _ y _ h => hπ h)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : (actionA : Coord m) ∈ x <;> simp [F, π, Ld, h]
  have h2 : ∑ q ∈ Finset.univ.image π, F q ≤ ∑ q, F q :=
    Finset.sum_le_univ_sum_of_nonneg (fun q => by positivity)
  have h3 : ∑ q, F q = totalSquaredLoad φA φB := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, F, totalSquaredLoad, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun Y _ => ?_))
    simp only [if_true, Bool.false_eq_true, if_false]
    ring
  linarith

/-! ### Finite probability lemmas -/

lemma uniformProb_eq {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) [DecidablePred P] :
    uniformProb P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  unfold uniformProb; convert rfl

lemma uniformProb_mono {α : Type} [Fintype α] [Nonempty α] {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  classical
  rw [uniformProb_eq, uniformProb_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun a ha => by
    rw [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, h a ha.2⟩)

lemma uniformProb_union_bound {α : Type} [Fintype α] [Nonempty α] (P Q : α → Prop) :
    1 - uniformProb (fun a => ¬ P a) - uniformProb (fun a => ¬ Q a) ≤
      uniformProb (fun a => P a ∧ Q a) := by
  classical
  rw [uniformProb_eq, uniformProb_eq, uniformProb_eq]
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcard : Fintype.card α ≤ (Finset.univ.filter (fun a => P a ∧ Q a)).card +
      (Finset.univ.filter (fun a => ¬ P a)).card + (Finset.univ.filter (fun a => ¬ Q a)).card := by
    calc Fintype.card α = (Finset.univ : Finset α).card := Finset.card_univ.symm
      _ ≤ ((Finset.univ.filter (fun a => P a ∧ Q a)) ∪ (Finset.univ.filter (fun a => ¬ P a)) ∪
            (Finset.univ.filter (fun a => ¬ Q a))).card := by
        apply Finset.card_le_card; intro a _
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      _ ≤ _ := (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _)
  have hcard' : (Fintype.card α : ℝ) ≤ (Finset.univ.filter (fun a => P a ∧ Q a)).card +
      (Finset.univ.filter (fun a => ¬ P a)).card +
        (Finset.univ.filter (fun a => ¬ Q a)).card := by exact_mod_cast hcard
  rw [← sub_nonneg]
  have : ((Finset.univ.filter (fun a => P a ∧ Q a)).card : ℝ) / Fintype.card α -
      (1 - ((Finset.univ.filter (fun a => ¬ P a)).card : ℝ) / Fintype.card α -
        ((Finset.univ.filter (fun a => ¬ Q a)).card : ℝ) / Fintype.card α) =
      (((Finset.univ.filter (fun a => P a ∧ Q a)).card : ℝ) +
        (Finset.univ.filter (fun a => ¬ P a)).card +
        (Finset.univ.filter (fun a => ¬ Q a)).card - Fintype.card α) / Fintype.card α := by
    field_simp; ring
  rw [this]
  exact div_nonneg (by linarith) hN.le

/-- Markov's inequality for the uniform law. -/
lemma markov {α : Type} [Fintype α] [Nonempty α] (h : α → ℝ) (hh : ∀ a, 0 ≤ h a) (c : ℝ)
    (hc : 0 < c) : uniformProb (fun a => c < h a) ≤ uniformMean h / c := by
  classical
  rw [uniformProb_eq]; unfold uniformMean
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have key : c * ((Finset.univ.filter (fun a => c < h a)).card : ℝ) ≤ ∑ a, h a := by
    calc c * ((Finset.univ.filter (fun a => c < h a)).card : ℝ)
        = ∑ a ∈ Finset.univ.filter (fun a => c < h a), c := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ Finset.univ.filter (fun a => c < h a), h a :=
          Finset.sum_le_sum (fun a ha => (Finset.mem_filter.1 ha).2.le)
      _ ≤ ∑ a, h a := Finset.sum_le_univ_sum_of_nonneg hh
  rw [div_div, div_le_div_iff₀ hN (mul_pos hN hc)]
  nlinarith

/-- Events depending only on the two label maps: `θ` is an independent coordinate. -/
lemma uniformProb_sample {m : ℕ} (P : LabelMap m × LabelMap m → Prop) :
    uniformProb (fun r : Sample m => P (r.1, r.2.1)) = uniformProb P := by
  classical
  rw [uniformProb_eq, uniformProb_eq]
  have hc : (Finset.univ.filter (fun r : Sample m => P (r.1, r.2.1))).card =
      ((Finset.univ.filter P) ×ˢ (Finset.univ : Finset (Table m))).card :=
    Finset.card_equiv (Equiv.prodAssoc _ _ _).symm (by rintro ⟨a, b, c⟩; simp)
  rw [hc, Finset.card_product, Finset.card_univ]
  simp only [Sample, Fintype.card_prod]
  have hT : (0 : ℝ) < Fintype.card (Table m) := by exact_mod_cast Fintype.card_pos
  have hL : (0 : ℝ) < Fintype.card (LabelMap m) := by exact_mod_cast Fintype.card_pos
  push_cast
  field_simp

/-! ### Expected sum of squared loads (Lemma 3.8 summed) -/

lemma card_halfSet (m : ℕ) : (Fintype.card (HalfSet m) : ℝ) = 2 ^ (m ^ 2) := by
  simp [HalfSet, Fintype.card_finset, Half, sq]

lemma mean_totalSquaredLoad {m : ℕ} (hm : 5 ≤ m) :
    uniformMean (fun q : LabelMap m × LabelMap m => totalSquaredLoad q.1 q.2) ≤
      4 * 2 ^ (m ^ 2) * (250 * (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by
  set Bd : ℝ := 250 * (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)
  set N : ℝ := (Fintype.card (LabelMap m) : ℝ) with hNdef
  have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
  have hL : ∀ (Y : HalfSet m) (φB : LabelMap m),
      ∑ φA : LabelMap m, ∑ U : HalfSet m, (loadY φA φB Y U : ℝ) ^ 2 ≤ N * Bd := by
    intro Y φB
    have := load_second_moment hm Y φB
    unfold uniformMean at this
    rw [div_le_iff₀ hN] at this; linarith
  have hsplit : ∀ φA φB : LabelMap m, totalSquaredLoad φA φB =
      2 * (∑ X : HalfSet m, ∑ Y : HalfSet m, (loadY φA φB Y X : ℝ) ^ 2) +
        2 * (∑ X : HalfSet m, ∑ Y : HalfSet m, (loadY φB φA X Y : ℝ) ^ 2) := by
    intro φA φB
    simp only [totalSquaredLoad, loadX, Finset.sum_add_distrib]; ring
  have e1 : ∑ φA : LabelMap m, ∑ φB : LabelMap m, ∑ X : HalfSet m, ∑ Y : HalfSet m,
      (loadY φA φB Y X : ℝ) ^ 2 =
      ∑ φB : LabelMap m, ∑ Y : HalfSet m, ∑ φA : LabelMap m, ∑ X : HalfSet m,
      (loadY φA φB Y X : ℝ) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun φB _ => ?_)
    calc ∑ φA : LabelMap m, ∑ X : HalfSet m, ∑ Y : HalfSet m, (loadY φA φB Y X : ℝ) ^ 2
        = ∑ φA : LabelMap m, ∑ Y : HalfSet m, ∑ X : HalfSet m, (loadY φA φB Y X : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun φA _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have e2 : ∑ φA : LabelMap m, ∑ φB : LabelMap m, ∑ X : HalfSet m, ∑ Y : HalfSet m,
      (loadY φB φA X Y : ℝ) ^ 2 =
      ∑ φA : LabelMap m, ∑ X : HalfSet m, ∑ φB : LabelMap m, ∑ Y : HalfSet m,
      (loadY φB φA X Y : ℝ) ^ 2 :=
    Finset.sum_congr rfl (fun φA _ => Finset.sum_comm)
  have b1 : ∑ φB : LabelMap m, ∑ Y : HalfSet m, ∑ φA : LabelMap m, ∑ X : HalfSet m,
      (loadY φA φB Y X : ℝ) ^ 2 ≤ N * (2 ^ (m ^ 2) * (N * Bd)) := by
    calc _ ≤ ∑ φB : LabelMap m, ∑ Y : HalfSet m, N * Bd :=
          Finset.sum_le_sum (fun φB _ => Finset.sum_le_sum (fun Y _ => hL Y φB))
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_halfSet, hNdef]
  have b2 : ∑ φA : LabelMap m, ∑ X : HalfSet m, ∑ φB : LabelMap m, ∑ Y : HalfSet m,
      (loadY φB φA X Y : ℝ) ^ 2 ≤ N * (2 ^ (m ^ 2) * (N * Bd)) := by
    calc _ ≤ ∑ φA : LabelMap m, ∑ X : HalfSet m, N * Bd :=
          Finset.sum_le_sum (fun φA _ => Finset.sum_le_sum (fun X _ => hL X φA))
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_halfSet, hNdef]
  unfold uniformMean
  rw [Fintype.card_prod, Nat.cast_mul, div_le_iff₀ (by positivity), Fintype.sum_prod_type]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e1, e2]
  rw [← hNdef]
  nlinarith

/-! ### Final arithmetic -/

lemma final_arith (μ t s C Ssum n L : ℝ) (hμ : 0 < μ) (ht : 0 < t) (hs : 0 < s) (hn : 0 ≤ n)
    (h1 : t ^ 2 * s ^ 6 / 4 < C) (h2 : L ≤ 10 ^ 4 * μ ^ 2 * t ^ 2 * s ^ 4)
    (hch : μ / 4 * C ≤ Ssum) (hcs : Ssum ^ 2 ≤ n * L) :
    1 / 10 ^ 8 ≤ n / (4 * t ^ 2 * s ^ 8) := by
  have a1 : μ * t ^ 2 * s ^ 6 / 16 ≤ Ssum := by
    have : μ / 4 * (t ^ 2 * s ^ 6 / 4) ≤ μ / 4 * C :=
      mul_le_mul_of_nonneg_left h1.le (by positivity)
    linarith
  have a2 : (μ * t ^ 2 * s ^ 6 / 16) ^ 2 ≤ Ssum ^ 2 := pow_le_pow_left₀ (by positivity) a1 2
  have a3 : n * L ≤ n * (10 ^ 4 * μ ^ 2 * t ^ 2 * s ^ 4) := mul_le_mul_of_nonneg_left h2 hn
  have hP : 0 < μ ^ 2 * t ^ 2 * s ^ 4 := by positivity
  have a4 : (t ^ 2 * s ^ 8 / 256) * (μ ^ 2 * t ^ 2 * s ^ 4) ≤
      (10 ^ 4 * n) * (μ ^ 2 * t ^ 2 * s ^ 4) := by
    have e1 : (μ * t ^ 2 * s ^ 6 / 16) ^ 2 = (t ^ 2 * s ^ 8 / 256) * (μ ^ 2 * t ^ 2 * s ^ 4) := by
      ring
    have e2 : n * (10 ^ 4 * μ ^ 2 * t ^ 2 * s ^ 4) = (10 ^ 4 * n) * (μ ^ 2 * t ^ 2 * s ^ 4) := by
      ring
    linarith
  have a5 := le_of_mul_le_mul_right a4 hP
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Distance bound on the good event -/

lemma card_cube (m : ℕ) : (Fintype.card (Cube (Coord m)) : ℝ) = 4 * ((2 : ℝ) ^ (m ^ 2)) ^ 2 := by
  simp only [Cube, Fintype.card_finset, Coord, Half, Fintype.card_sum, Fintype.card_bool,
    Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1; ring

lemma far_of_good {m : ℕ} (hm : 9 ≤ m) (r : Sample m)
    (h1 : (1 / 4 : ℝ) * (1 / 2) ^ (2 * m) * 2 ^ (2 * m ^ 2) < balancedCenters r.1 r.2.1)
    (h2 : totalSquaredLoad r.1 r.2.1 ≤
      10 * (4 * 2 ^ (m ^ 2) * (250 * (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)))) :
    Far Submodular (1 / 10 ^ 8 : ℝ) (hard r false) := by
  intro G hG
  unfold distance
  set S := Finset.univ.filter (fun x => hard r false x ≠ G x) with hSdef
  have hmis : mismatch (hard r false) G = S.card := by unfold mismatch; convert rfl
  have hch := charging hm r G hG S
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, Ne.symm hx⟩)
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun x => (Ld r.1 r.2.1 x : ℝ))
  have hsq : ∑ x ∈ S, (Ld r.1 r.2.1 x : ℝ) ^ 2 ≤ totalSquaredLoad r.1 r.2.1 :=
    (Finset.sum_le_univ_sum_of_nonneg (fun x => by positivity)).trans (sum_Ld_sq_le _ _)
  have hcs' : (∑ x ∈ S, (Ld r.1 r.2.1 x : ℝ)) ^ 2 ≤ (S.card : ℝ) * totalSquaredLoad r.1 r.2.1 :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  have h4 : 4 * m ≤ m ^ 2 := by nlinarith
  set t : ℝ := 2 ^ (m ^ 2 - 4 * m) with ht
  set s : ℝ := 2 ^ m with hs
  set μ : ℝ := (m : ℝ) ^ (2 * m) with hμ
  have hH : (2 : ℝ) ^ (m ^ 2) = t * s ^ 4 := by
    rw [ht, hs, ← pow_mul, ← pow_add]; congr 1; omega
  have hμpos : 0 < μ := by positivity
  have e1 : (1 / 4 : ℝ) * (1 / 2) ^ (2 * m) * 2 ^ (2 * m ^ 2) = t ^ 2 * s ^ 6 / 4 := by
    rw [show (2 : ℝ) ^ (2 * m ^ 2) = (2 ^ (m ^ 2)) ^ 2 by rw [← pow_mul]; ring_nf, hH,
      one_div_pow, show (2 : ℝ) ^ (2 * m) = s ^ 2 by rw [hs, ← pow_mul]; ring_nf]
    field_simp
  have e2 : 10 * (4 * 2 ^ (m ^ 2) * (250 * (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m))) =
      10 ^ 4 * μ ^ 2 * t ^ 2 * s ^ 4 := by
    rw [hH, hμ, ← pow_mul, ← ht]; ring_nf
  rw [e1] at h1
  rw [e2] at h2
  rw [hmis, card_cube, hH]
  have := final_arith μ t s _ _ _ _ hμpos (by positivity) (by positivity) (by positivity) h1 h2
    hch hcs'
  convert this using 2; ring

end BTHelper_soundness

open BTHelper_soundness in
theorem solution :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      (8/10 : ℝ) ≤ uniformProb (fun r : Sample m =>
        Far Submodular (1/10^8 : ℝ) (hard r false)) := by
  obtain ⟨M0, hM0⟩ := balanced_centers
  refine ⟨max M0 9, fun m hm => ?_⟩
  have hm9 : 9 ≤ m := le_of_max_le_right hm
  have hmM : M0 ≤ m := le_of_max_le_left hm
  set mb : ℝ := 4 * 2 ^ (m ^ 2) * (250 * (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) with hmb
  have hmbpos : 0 < mb := by
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  let E1 : LabelMap m × LabelMap m → Prop := fun q =>
    (1 / 4 : ℝ) * (1 / 2) ^ (2 * m) * 2 ^ (2 * m ^ 2) < balancedCenters q.1 q.2
  let E2 : LabelMap m × LabelMap m → Prop := fun q => totalSquaredLoad q.1 q.2 ≤ 10 * mb
  have hE1 : uniformProb (fun q => ¬ E1 q) ≤ 1 / 10 :=
    (uniformProb_mono (fun q hq => not_lt.mp hq)).trans (hM0 m hmM)
  have hE2 : uniformProb (fun q => ¬ E2 q) ≤ 1 / 10 := by
    refine (uniformProb_mono (fun q hq => not_le.mp hq)).trans ?_
    refine (markov (fun q : LabelMap m × LabelMap m => totalSquaredLoad q.1 q.2)
      (fun q => by unfold totalSquaredLoad; positivity) (10 * mb) (by positivity)).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have := mean_totalSquaredLoad (show 5 ≤ m by omega)
    rw [← hmb] at this
    linarith
  have hU := uniformProb_union_bound E1 E2
  calc (8 / 10 : ℝ) ≤ uniformProb (fun q => E1 q ∧ E2 q) := by linarith
    _ = uniformProb (fun r : Sample m => E1 (r.1, r.2.1) ∧ E2 (r.1, r.2.1)) :=
        (uniformProb_sample (fun q => E1 q ∧ E2 q)).symm
    _ ≤ _ := uniformProb_mono (fun r hr => far_of_good hm9 r hr.1 hr.2)
