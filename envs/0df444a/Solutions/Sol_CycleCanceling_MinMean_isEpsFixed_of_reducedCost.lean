-- Prove2me | solution 1 for CycleCanceling.MinMean.isEpsFixed_of_reducedCost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:45:29.540706+00:00
-- url     : https://prove2.me/submissions/919b0a3c-5b10-44e8-8587-abece7058fcd

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

set_option autoImplicit false

namespace CC932da085

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Layers of vertices reachable from `w` along arcs with `h > 0`. -/
noncomputable def layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) : ℕ → Finset V
  | 0 => {w}
  | k + 1 => layer N h w k ∪
      Finset.univ.filter (fun y => ∃ x ∈ layer N h w k, (x, y) ∈ N.E ∧ 0 < h x y)

lemma layer_succ_sub (N : CircNetwork V) (h : V → V → ℝ) (w : V) (k : ℕ) :
    layer N h w k ⊆ layer N h w (k + 1) := by
  show layer N h w k ⊆ layer N h w k ∪ _
  exact Finset.subset_union_left

lemma w_mem_layer (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∀ k : ℕ, w ∈ layer N h w k := by
  intro k
  induction k with
  | zero => simp [layer]
  | succ k ih => exact layer_succ_sub N h w k ih

lemma layer_bound (N : CircNetwork V) (h : V → V → ℝ) (w : V) (q : V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε) :
    ∀ k : ℕ, ∀ x ∈ layer N h w k, q x ≤ q w + 2 * (k : ℝ) * ε := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp [layer] at hx
    subst hx
    simp
  | succ k ih =>
    intro x hx
    have hx' : x ∈ layer N h w k ∪
        Finset.univ.filter (fun y => ∃ z ∈ layer N h w k, (z, y) ∈ N.E ∧ 0 < h z y) := hx
    rcases Finset.mem_union.mp hx' with h1 | h1
    · have := ih x h1
      push_cast
      nlinarith
    · obtain ⟨z, hz, hzE, hzpos⟩ := (Finset.mem_filter.mp h1).2
      have := ih z hz
      have := hstep z x hzE hzpos
      push_cast
      nlinarith

lemma layer_stab (N : CircNetwork V) (h : V → V → ℝ) (w : V) :
    ∃ k : ℕ, k + 1 ≤ Fintype.card V ∧ layer N h w (k + 1) ⊆ layer N h w k := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, k ≤ Fintype.card V → k + 1 ≤ (layer N h w k).card := by
    intro k
    induction k with
    | zero => intro _; simp [layer]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hss : layer N h w k ⊂ layer N h w (k + 1) :=
        HasSubset.Subset.ssubset_of_not_subset (layer_succ_sub N h w k) (hcon k hk)
      have := Finset.card_lt_card hss
      omega
  have := key (Fintype.card V) le_rfl
  have := Finset.card_le_univ (layer N h w (Fintype.card V))
  omega

lemma cut_false (N : CircNetwork V) (h : V → V → ℝ) (S : Finset V)
    (hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a)
    (hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0)
    (hclosed : ∀ a ∈ S, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ S)
    (v w : V) (hw : w ∈ S) (hv : v ∉ S) (hvw : (v, w) ∈ N.E) (hpos : 0 < h v w) : False := by
  classical
  let φ : V → V → ℝ := fun x y => if (x, y) ∈ N.E then h y x else 0
  have hφanti : ∀ x y, φ x y = -φ y x := by
    intro x y
    simp only [φ]
    by_cases hxy : (x, y) ∈ N.E
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      rw [if_pos hxy, if_pos hyx]
      exact hanti y x hyx
    · have hyx : (y, x) ∉ N.E := fun h' => hxy ((N.symm y x).1 h')
      rw [if_neg hxy, if_neg hyx]
      simp
  have htot : ∑ x ∈ S, ∑ y, φ x y = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hcons x, Finset.sum_filter]
  have hA : ∑ x ∈ S, ∑ y ∈ S, φ x y = 0 := by
    have h1 : ∑ x ∈ S, ∑ y ∈ S, φ x y = ∑ y ∈ S, ∑ x ∈ S, φ x y := Finset.sum_comm
    have h2 : ∑ y ∈ S, ∑ x ∈ S, φ x y = -∑ y ∈ S, ∑ x ∈ S, φ y x := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hφanti x y
    linarith
  have hnn : ∀ x ∈ S, ∀ y ∈ Sᶜ, 0 ≤ φ x y := by
    intro x hx y hy
    simp only [φ]
    split_ifs with hxy
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      have hle : ¬ 0 < h x y := fun hp => (Finset.mem_compl.mp hy) (hclosed x hx y hxy hp)
      push_neg at hle
      rw [hanti y x hyx]
      linarith
    · exact le_rfl
  have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
  have hB : 0 < ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    have hv' : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    have e1 : φ w v ≤ ∑ y ∈ Sᶜ, φ w y :=
      Finset.single_le_sum (fun y hy => hnn w hw y hy) hv'
    have e2 : ∑ y ∈ Sᶜ, φ w y ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y :=
      Finset.single_le_sum (f := fun x => ∑ y ∈ Sᶜ, φ x y)
        (fun x hx => Finset.sum_nonneg (fun y hy => hnn x hx y hy)) hw
    have e0 : φ w v = h v w := by simp only [φ]; rw [if_pos hwv]
    linarith
  have hsplit : ∑ x ∈ S, ∑ y, φ x y =
      ∑ x ∈ S, ∑ y ∈ S, φ x y + ∑ x ∈ S, ∑ y ∈ Sᶜ, φ x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_add_sum_compl]
  linarith

lemma main (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε) (f : V → V → ℝ)
    (hf : IsCirculation N f) (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V)
    (hvw : (v, w) ∈ N.E)
    (hneg : reducedCost N p v w ≤ -(2 * (Fintype.card V : ℝ) * ε))
    (g : V → V → ℝ) (hg : IsEpsOptimal N g ε) : g v w = f v w := by
  obtain ⟨hgc, -, p', hgp⟩ := hg
  haveI : Nonempty V := ⟨v⟩
  have hn : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hfu : N.u v w ≤ f v w := by
    by_contra hlt
    push_neg at hlt
    have := hfp v w hvw (by unfold resCap; linarith)
    nlinarith
  by_contra hne
  have hlt : g v w < f v w := lt_of_le_of_ne (le_trans (hgc.1 v w hvw) hfu) hne
  let h : V → V → ℝ := fun a b => f a b - g a b
  let q : V → ℝ := fun x => p' x - p x
  have hstep : ∀ a b, (a, b) ∈ N.E → 0 < h a b → q b ≤ q a + 2 * ε := by
    intro a b hab hpos
    have hba := (N.symm a b).1 hab
    simp only [h] at hpos
    have h1 := hgp a b hab (by unfold resCap; linarith [hf.1 a b hab])
    have h2 := hfp b a hba (by
      unfold resCap
      linarith [hf.2.1 a b hab, hgc.2.1 a b hab, hgc.1 b a hba])
    have h3 := N.cost_antisymm a b hab
    unfold reducedCost at h1 h2
    simp only [q]
    linarith
  have hanti : ∀ a b, (a, b) ∈ N.E → h a b = -h b a := by
    intro a b hab
    simp only [h]
    rw [hf.2.1 a b hab, hgc.2.1 a b hab]
    ring
  have hcons : ∀ x, ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), h y x = 0 := by
    intro x
    simp only [h]
    rw [Finset.sum_sub_distrib, hf.2.2 x, hgc.2.2 x]
    ring
  obtain ⟨k, hk, hsub⟩ := layer_stab N h w
  have hclosed : ∀ a ∈ layer N h w k, ∀ b, (a, b) ∈ N.E → 0 < h a b → b ∈ layer N h w k := by
    intro a ha b hab hp
    apply hsub
    show b ∈ layer N h w k ∪ _
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, hab, hp⟩
  have hwS : w ∈ layer N h w k := w_mem_layer N h w k
  have hvS : v ∈ layer N h w k := by
    by_contra hvS
    exact cut_false N h (layer N h w k) hanti hcons hclosed v w hwS hvS hvw
      (by simp only [h]; linarith)
  have hqv := layer_bound N h w q ε hε.le hstep k v hvS
  have hg1 := hgp v w hvw (by unfold resCap; linarith [hf.1 v w hvw])
  have hkR : ((k : ℝ) + 1) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hk
  have hkε : (k : ℝ) * ε ≤ ((Fintype.card V : ℝ) - 1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  unfold reducedCost at hneg hg1
  simp only [q] at hqv
  nlinarith

end CC932da085

open CycleCanceling.MinMean in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (ε : ℝ) (hε : 0 < ε) (f : V → V → ℝ) (hf : IsCirculation N f)
    (p : V → ℝ) (hfp : IsEpsOptimalWrt N f ε p) (v w : V) (hvw : (v, w) ∈ N.E)
    (hbig : 2 * (Fintype.card V : ℝ) * ε ≤ |reducedCost N p v w|) :
    IsEpsFixed N ε v w := by
  intro g g' hg hg'
  rcases le_abs'.mp hbig with hneg | hpos
  · rw [CC932da085.main N ε hε f hf p hfp v w hvw hneg g hg,
      CC932da085.main N ε hε f hf p hfp v w hvw hneg g' hg']
  · have hwv : (w, v) ∈ N.E := (N.symm v w).1 hvw
    have hneg' : reducedCost N p w v ≤ -(2 * (Fintype.card V : ℝ) * ε) := by
      have := N.cost_antisymm v w hvw
      unfold reducedCost at hpos ⊢
      linarith
    have e1 := CC932da085.main N ε hε f hf p hfp w v hwv hneg' g hg
    have e2 := CC932da085.main N ε hε f hf p hfp w v hwv hneg' g' hg'
    rw [hg.1.2.1 v w hvw, hg'.1.2.1 v w hvw, e1, e2]
