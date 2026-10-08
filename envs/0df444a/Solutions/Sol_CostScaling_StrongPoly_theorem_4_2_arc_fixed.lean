-- Prove2me | solution 1 for CostScaling.StrongPoly.theorem_4_2_arc_fixed
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:09:06.56878+00:00
-- url     : https://prove2.me/submissions/6217639a-8359-4dc0-b369-252b9128cb6b

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal



namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
noncomputable def reachSet (E : Finset (V × V)) (g : V → V → ℝ) (w : V) : ℕ → Finset V
  | 0 => {w}
  | k + 1 => reachSet E g w k ∪ Finset.univ.filter
      (fun y => ∃ x ∈ reachSet E g w k, (x, y) ∈ E ∧ 0 < g x y)

lemma mem_reachSet_succ (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) (y : V) :
    y ∈ reachSet E g w (k + 1) ↔
      y ∈ reachSet E g w k ∨ ∃ x ∈ reachSet E g w k, (x, y) ∈ E ∧ 0 < g x y := by
  rw [reachSet]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

lemma reachSet_mono (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    reachSet E g w k ⊆ reachSet E g w (k + 1) := by
  intro x hx
  simp only [reachSet]
  exact Finset.mem_union_left _ hx

lemma reachSet_stable (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ)
    (h : reachSet E g w k = reachSet E g w (k + 1)) :
    reachSet E g w (k + 1) = reachSet E g w (k + 1 + 1) := by
  apply le_antisymm
  · exact reachSet_mono E g w (k + 1)
  · intro y hy
    rw [mem_reachSet_succ] at hy
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact hy
    · rw [mem_reachSet_succ]; right; rw [h]; exact ⟨x, hx, hxy⟩

lemma reachSet_dich (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    k + 1 ≤ (reachSet E g w k).card ∨ reachSet E g w k = reachSet E g w (k + 1) := by
  induction k with
  | zero => left; simp [reachSet]
  | succ k ih =>
    by_cases h : reachSet E g w k = reachSet E g w (k + 1)
    · exact Or.inr (reachSet_stable E g w k h)
    · left
      have h1 : k + 1 ≤ (reachSet E g w k).card := by tauto
      have hs : reachSet E g w k ⊂ reachSet E g w (k + 1) :=
        lt_of_le_of_ne (reachSet_mono E g w k) h
      have := Finset.card_lt_card hs
      omega

lemma reachSet_bound (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (D : ℝ) (q : V → ℝ)
    (hD : 0 ≤ D) (hstep : ∀ x y, (x, y) ∈ E → 0 < g x y → q y ≤ q x + D) (k : ℕ) :
    ∀ x ∈ reachSet E g w k, q x ≤ q w + k * D := by
  induction k with
  | zero => intro x hx; simp [reachSet] at hx; subst hx; simp
  | succ k ih =>
    intro y hy
    rw [mem_reachSet_succ] at hy
    rcases hy with hy | ⟨x, hx, hxy, hg⟩
    · have := ih y hy; push_cast; nlinarith
    · have := ih x hx; have := hstep x y hxy hg; push_cast; nlinarith

lemma cut_zero (N : CircNetwork V) (g : V → V → ℝ)
    (hanti : ∀ x y, (x, y) ∈ N.E → g x y = -g y x)
    (hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), g v w = 0)
    (S : Finset V) (hclosed : ∀ x ∈ S, ∀ y, (x, y) ∈ N.E → 0 < g x y → y ∈ S) :
    ∀ x ∈ S, ∀ y, y ∉ S → (x, y) ∈ N.E → g x y = 0 := by
  classical
  set F : V → V → ℝ := fun x v => if (x, v) ∈ N.E then g v x else 0 with hF
  have h0 : ∑ x ∈ S, ∑ v, F x v = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hcons x, Finset.sum_filter]
  have hsplit : ∑ x ∈ S, ∑ v, F x v = ∑ x ∈ S, ∑ v ∈ S, F x v + ∑ x ∈ S, ∑ v ∈ Sᶜ, F x v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_add_sum_compl]
  have hanF : ∀ x v, F v x = -F x v := by
    intro x v
    simp only [hF]
    by_cases h : (x, v) ∈ N.E
    · have h' : (v, x) ∈ N.E := (N.symm x v).1 h
      rw [if_pos h, if_pos h', hanti x v h]; try ring
    · have h' : (v, x) ∉ N.E := fun h' => h ((N.symm v x).1 h')
      rw [if_neg h, if_neg h']; try ring
  have hT1 : ∑ x ∈ S, ∑ v ∈ S, F x v = 0 := by
    have : ∑ x ∈ S, ∑ v ∈ S, F x v = -∑ x ∈ S, ∑ v ∈ S, F x v := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro v _
      exact hanF x v
    linarith
  have hT2 : ∑ x ∈ S, ∑ v ∈ Sᶜ, F x v = 0 := by linarith
  have hnn : ∀ x ∈ S, ∀ v ∈ Sᶜ, 0 ≤ F x v := by
    intro x hx v hv
    simp only [hF]
    split_ifs with h
    · have h1 : g x v ≤ 0 := by
        by_contra hc
        push_neg at hc
        exact (Finset.mem_compl.1 hv) (hclosed x hx v h hc)
      have := hanti x v h
      have h2 := hanti v x ((N.symm x v).1 h)
      linarith
    · exact le_rfl
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x hx => Finset.sum_nonneg (hnn x hx))] at hT2
  intro x hx y hy hxy
  have h1 := hT2 x hx
  rw [Finset.sum_eq_zero_iff_of_nonneg (hnn x hx)] at h1
  have h2 := h1 y (Finset.mem_compl.2 hy)
  simp only [hF, if_pos hxy] at h2
  have := hanti x y hxy
  linarith

lemma w_mem_reachSet (E : Finset (V × V)) (g : V → V → ℝ) (w : V) (k : ℕ) :
    w ∈ reachSet E g w k := by
  induction k with
  | zero => simp [reachSet]
  | succ k ih => exact reachSet_mono E g w k ih

lemma rc_anti (N : CircNetwork V) (p : V → ℝ) (x y : V) (h : (x, y) ∈ N.E) :
    reducedCost N p y x = -reducedCost N p x y := by
  have := N.cost_antisymm x y h
  have h2 := N.cost_antisymm y x ((N.symm x y).1 h)
  unfold reducedCost; linarith

lemma step_bounds (N : CircNetwork V) (ε ε' : ℝ) (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (f' : V → V → ℝ) (hf' : IsCirculation N f') (p' : V → ℝ) (hp' : IsEpsOptimalWrt N f' ε' p')
    (x y : V) (hxy : (x, y) ∈ N.E) (hlt : f x y < f' x y) :
    -ε ≤ reducedCost N p x y ∧ reducedCost N p' x y ≤ ε' := by
  have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
  constructor
  · apply hfp x y hxy
    have := hf'.1 x y hxy
    unfold resCap; linarith
  · have h1 := hf.2.1 x y hxy
    have h2 := hf'.2.1 x y hxy
    have h3 := hf.1 y x hyx
    have : 0 < resCap N f' y x := by unfold resCap; linarith
    have := hp' y x hyx this
    rw [rc_anti N p' x y hxy] at this
    linarith

lemma pos_case (N : CircNetwork V) (hvertices : 2 ≤ Fintype.card V)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (f' : V → V → ℝ) (hf' : IsCirculation N f') (p' : V → ℝ) (hp' : IsEpsOptimalWrt N f' ε' p')
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ reducedCost N p v w) :
    f v w = f' v w := by
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hvertices
  rcases lt_trichotomy (f v w) (f' v w) with hlt | heq | hgt
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card V = k + 1 := ⟨Fintype.card V - 1, by omega⟩
    have hkR : (Fintype.card V : ℝ) = k + 1 := by exact_mod_cast hk
    set g : V → V → ℝ := fun x y => f' x y - f x y with hg
    have hanti : ∀ x y, (x, y) ∈ N.E → g x y = -g y x := by
      intro x y h
      simp only [hg]
      have := hf.2.1 x y h
      have := hf'.2.1 x y h
      linarith
    have hcons : ∀ w, ∑ v ∈ Finset.univ.filter (fun v => (w, v) ∈ N.E), g v w = 0 := by
      intro w
      simp only [hg]
      rw [Finset.sum_sub_distrib, hf.2.2 w, hf'.2.2 w]; ring
    set q : V → ℝ := fun x => p x - p' x with hq
    have hD : 0 ≤ ε + ε' := by linarith
    have hstep : ∀ x y, (x, y) ∈ N.E → 0 < g x y → q y ≤ q x + (ε + ε') := by
      intro x y hxy hpos
      have hlt' : f x y < f' x y := by simp only [hg] at hpos; linarith
      obtain ⟨h1, h2⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' x y hxy hlt'
      simp only [hq]
      unfold reducedCost at h1 h2
      linarith
    have hvS : v ∈ reachSet N.E g w k := by
      rcases reachSet_dich N.E g w k with h | h
      · have : reachSet N.E g w k = Finset.univ :=
          Finset.eq_univ_of_card _ (by have := Finset.card_le_univ (reachSet N.E g w k); omega)
        rw [this]; exact Finset.mem_univ _
      · by_contra hv
        have hclosed : ∀ x ∈ reachSet N.E g w k, ∀ y, (x, y) ∈ N.E → 0 < g x y →
            y ∈ reachSet N.E g w k := by
          intro x hx y hxy hpos
          rw [h, mem_reachSet_succ]
          right; exact ⟨x, hx, hxy, hpos⟩
        have := cut_zero N g hanti hcons _ hclosed w (w_mem_reachSet _ _ _ _) v hv hwv
        have h2 := hanti w v hwv
        simp only [hg] at this h2
        linarith
    have hb := reachSet_bound N.E g w (ε + ε') q hD hstep k v hvS
    have hpos : 0 < g v w := by simp only [hg]; linarith
    obtain ⟨h1, h2⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' v w hvw hlt
    simp only [hq] at hb
    unfold reducedCost at hcost h2
    rw [hkR] at hcost
    nlinarith
  · exact heq
  · exfalso
    have hlt : f w v < f' w v := by
      have := hf.2.1 v w hvw
      have := hf'.2.1 v w hvw
      linarith
    obtain ⟨h1, _⟩ := step_bounds N ε ε' f hf p hfp f' hf' p' hp' w v hwv hlt
    rw [rc_anti N p v w hvw] at h1
    nlinarith

theorem arc_fixed_core (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ |reducedCost N p v w|) :
    ∀ f' : V → V → ℝ, IsEpsOptimal N f' ε' → f v w = f' v w := by
  intro f' ⟨hf', _, p', hp'⟩
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  rcases le_abs'.1 hcost with h | h
  · have h' : (Fintype.card V : ℝ) * (ε + ε') ≤ reducedCost N p w v := by
      rw [rc_anti N p v w hvw]; linarith
    have := pos_case N hvertices ε ε' hε hε' f hf p hfp f' hf' p' hp' w v hwv h'
    have h1 := hf.2.1 v w hvw
    have h2 := hf'.2.1 v w hvw
    linarith
  · exact pos_case N hvertices ε ε' hε hε' f hf p hfp f' hf' p' hp' v w hvw h

end CostScaling.StrongPoly

open CostScaling.StrongPoly
open CycleCanceling.MinMean
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p)
    (v w : V) (hvw : (v, w) ∈ N.E)
    (hcost : (Fintype.card V : ℝ) * (ε + ε') ≤ |reducedCost N p v w|) :
    ∀ f' : V → V → ℝ, IsEpsOptimal N f' ε' → f v w = f' v w := by
  exact arc_fixed_core N hvertices harcs ε ε' hε hε' f hf p hfp v w hvw hcost
