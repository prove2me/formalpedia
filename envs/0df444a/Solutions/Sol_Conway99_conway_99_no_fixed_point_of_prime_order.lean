-- Prove2me | solution 1 for Conway99.conway_99_no_fixed_point_of_prime_order
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T18:41:43.97859+00:00
-- url     : https://prove2.me/submissions/72dd7258-4f41-4df6-9fc8-719eed660ff0

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open SimpleGraph Finset

namespace Conway99Aux

variable {V : Type*} {g : SimpleGraph V}

lemma pow_succ_apply (σ : g ≃g g) (n : ℕ) (y : V) : (σ ^ (n + 1)) y = σ ((σ ^ n) y) := by
  rw [pow_succ']
  rfl

lemma pow_add_apply (σ : g ≃g g) (m n : ℕ) (y : V) :
    (σ ^ (m + n)) y = (σ ^ m) ((σ ^ n) y) := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : k + 1 + n = (k + n) + 1 := by omega
      rw [hk, pow_succ_apply, ih, pow_succ_apply]

/-- Powers of a graph automorphism act by iterated application. -/
lemma pow_apply_eq_iterate (σ : g ≃g g) (n : ℕ) (y : V) :
    (σ ^ n) y = (fun v => σ v)^[n] y := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, Function.iterate_succ_apply']

/-- If `σ ^ p = 1` and some power `σ ^ d` with `p ∤ d` fixes `y`, then `σ` fixes `y`. -/
lemma fixed_of_pow_fixed {p : ℕ} (hp : p.Prime) (σ : g ≃g g) (hσp : σ ^ p = 1) {d : ℕ}
    (hd : ¬ p ∣ d) {y : V} (hy : (σ ^ d) y = y) : σ y = y := by
  set f : V → V := fun v => σ v with hf
  have hdp : Function.IsPeriodicPt f d y := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← pow_apply_eq_iterate]
    exact hy
  have hpp : Function.IsPeriodicPt f p y := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← pow_apply_eq_iterate, hσp]
    rfl
  have h1 : Function.minimalPeriod f y ∣ Nat.gcd p d :=
    Nat.dvd_gcd hpp.minimalPeriod_dvd hdp.minimalPeriod_dvd
  have h2 : Nat.gcd p d = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hd
  rw [h2, Nat.dvd_one] at h1
  exact Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1

lemma pow_fix (σ : g ≃g g) {x : V} (hx : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, hx]

lemma pow_adj (σ : g ≃g g) (n : ℕ) {a b : V} (hab : g.Adj a b) : g.Adj ((σ ^ n) a) ((σ ^ n) b) := by
  induction n with
  | zero => simpa using hab
  | succ k ih =>
      rw [pow_succ_apply, pow_succ_apply]
      exact (σ.map_adj_iff).2 ih

variable [Fintype V] [DecidableEq V] [DecidableRel g.Adj]

/-- With `λ = 1`, two adjacent vertices have a unique common neighbour. -/
lemma unique_common (h : g.IsSRGWith 99 14 1 2) {x y : V} (hxy : g.Adj x y) :
    ∃! z, g.Adj x z ∧ g.Adj y z := by
  have hcard := h.of_adj x y hxy
  rw [Fintype.card_eq_one_iff] at hcard
  obtain ⟨⟨z, hz⟩, hu⟩ := hcard
  rw [g.mem_commonNeighbors] at hz
  refine ⟨z, hz, fun w hw => ?_⟩
  have : (⟨w, (g.mem_commonNeighbors).2 hw⟩ : g.commonNeighbors x y) = ⟨z, _⟩ := hu _
  exact congrArg Subtype.val this

/-- The orbit of a non-fixed point under an automorphism of prime order `p` has `p` elements. -/
lemma orbit_card {p : ℕ} (hp : p.Prime) (σ : g ≃g g) (hσp : σ ^ p = 1) {y : V} (hy : σ y ≠ y) :
    ((range p).image (fun i => (σ ^ i) y)).card = p := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij0
  have hij : (σ ^ i) y = (σ ^ j) y := hij0
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  -- wlog `j < i`
  rcases Nat.lt_or_ge i j with hlt | hge
  · have happ : (σ ^ (p - j + i)) y = y := by
      have h1 : (σ ^ (p - j)) ((σ ^ i) y) = (σ ^ (p - j)) ((σ ^ j) y) := by rw [hij]
      rw [← pow_add_apply, ← pow_add_apply] at h1
      have h2 : p - j + j = p := by omega
      rw [h2, hσp] at h1
      exact h1
    have hd : ¬ p ∣ (p - j + i) := by
      intro hdvd
      have h3 : 0 < p - j + i := by omega
      have h4 : p - j + i < p := by omega
      exact absurd (Nat.le_of_dvd h3 hdvd) (by omega)
    exact hy (fixed_of_pow_fixed hp σ hσp hd happ)
  · have hlt : j < i := by omega
    have happ : (σ ^ (p - i + j)) y = y := by
      have h1 : (σ ^ (p - i)) ((σ ^ j) y) = (σ ^ (p - i)) ((σ ^ i) y) := by rw [hij]
      rw [← pow_add_apply, ← pow_add_apply] at h1
      have h2 : p - i + i = p := by omega
      rw [h2, hσp] at h1
      exact h1
    have hd : ¬ p ∣ (p - i + j) := by
      intro hdvd
      have h3 : 0 < p - i + j := by omega
      have h4 : p - i + j < p := by omega
      exact absurd (Nat.le_of_dvd h3 hdvd) (by omega)
    exact hy (fixed_of_pow_fixed hp σ hσp hd happ)

/-- If an automorphism of prime order `p > 7` of a `(99,14,1,2)` graph fixes a vertex, it fixes
all its neighbours. -/
lemma fixed_neighbor (h : g.IsSRGWith 99 14 1 2) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (σ : g ≃g g) (hσp : σ ^ p = 1) {x : V} (hx : σ x = x) {y : V} (hxy : g.Adj x y) :
    σ y = y := by
  by_contra hy
  obtain ⟨z, ⟨hxz, hyz⟩, huniq⟩ := unique_common h hxy
  -- the partner of `z` is `y`
  have huniqz : ∀ w, g.Adj x w ∧ g.Adj z w → w = y := by
    obtain ⟨w0, hw0, hu0⟩ := unique_common h hxz
    intro w hw
    exact (hu0 w hw).trans (hu0 y ⟨hxy, hyz.symm⟩).symm
  -- `σ` does not fix `z` either
  have hz : σ z ≠ z := by
    intro hcon
    have h1 : g.Adj x (σ y) := by
      rw [← hx]; exact σ.map_adj_iff.2 hxy
    have h2 : g.Adj z (σ y) := by
      have hadj := σ.map_adj_iff.2 hyz
      rw [hcon] at hadj
      exact hadj.symm
    exact hy (huniqz (σ y) ⟨h1, h2⟩)
  set O := (range p).image (fun i => (σ ^ i) y) with hO
  set Z := (range p).image (fun i => (σ ^ i) z) with hZ
  have hOsub : O ⊆ g.neighborFinset x := by
    intro w hw
    rw [hO, Finset.mem_image] at hw
    obtain ⟨i, _, rfl⟩ := hw
    rw [SimpleGraph.mem_neighborFinset, ← pow_fix σ hx i]
    exact pow_adj σ i hxy
  have hZsub : Z ⊆ g.neighborFinset x := by
    intro w hw
    rw [hZ, Finset.mem_image] at hw
    obtain ⟨i, _, rfl⟩ := hw
    rw [SimpleGraph.mem_neighborFinset, ← pow_fix σ hx i]
    exact pow_adj σ i hxz
  have hdeg : (g.neighborFinset x).card = 14 := h.regular x
  have hcardO : O.card = p := orbit_card hp σ hσp hy
  have hcardZ : Z.card = p := orbit_card hp σ hσp hz
  by_cases hdisj : Disjoint O Z
  · have : (O ∪ Z).card = 2 * p := by
      rw [Finset.card_union_of_disjoint hdisj, hcardO, hcardZ]; ring
    have hle : (O ∪ Z).card ≤ 14 := by
      rw [← hdeg]
      exact Finset.card_le_card (Finset.union_subset hOsub hZsub)
    omega
  · -- the two orbits meet, so `z` is a power of `σ` applied to `y`
    rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨w, hwO, hwZ⟩ := hdisj
    rw [hO, Finset.mem_image] at hwO
    rw [hZ, Finset.mem_image] at hwZ
    obtain ⟨i, hi, hiw⟩ := hwO
    obtain ⟨j, hj, hjw⟩ := hwZ
    rw [Finset.mem_range] at hi hj
    have hzm : z = (σ ^ (p - j + i)) y := by
      have h1 : (σ ^ (p - j)) ((σ ^ i) y) = (σ ^ (p - j)) ((σ ^ j) z) := by rw [hiw, hjw]
      rw [← pow_add_apply, ← pow_add_apply] at h1
      have h2 : p - j + j = p := by omega
      rw [h2, hσp] at h1
      exact h1.symm
    set m := p - j + i with hm
    -- the partner of `z = σ^m y` is `σ^m z`
    have hpart : (σ ^ m) z = y := by
      refine huniqz _ ⟨?_, ?_⟩
      · rw [← pow_fix σ hx m]; exact pow_adj σ m hxz
      · nth_rewrite 1 [hzm]
        exact pow_adj σ m hyz
    have hyy : (σ ^ (m + m)) y = y := by
      rw [pow_add_apply, ← hzm, hpart]
    have hdvd : p ∣ m + m := by
      by_contra hcon
      exact hy (fixed_of_pow_fixed hp σ hσp hcon hyy)
    have hpm : p ∣ m := by
      have hp2 : p ≠ 2 := by omega
      have : m + m = 2 * m := by ring
      rw [this] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | hm2
      · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
      · exact hm2
    obtain ⟨t, ht⟩ := hpm
    have : (σ ^ m) y = y := by
      rw [ht, pow_mul, hσp, one_pow]
      rfl
    rw [hzm, this] at hyz
    exact hyz.ne rfl

end Conway99Aux

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (σ : g ≃g g) (hσ : orderOf σ = p) (v : V) : σ v ≠ v := by
  classical
  intro hv
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  -- every vertex is fixed
  have hall : ∀ w : V, σ w = w := by
    intro w
    by_cases hwv : w = v
    · rw [hwv]; exact hv
    by_cases hadj : g.Adj v w
    · exact Conway99Aux.fixed_neighbor h hp hp7 σ hσp hv hadj
    · -- `v` and `w` have a common neighbour
      have hcard := h.of_not_adj (Ne.symm hwv) hadj
      have : Nonempty (g.commonNeighbors v w) := by
        rw [← Fintype.card_pos_iff, hcard]; norm_num
      obtain ⟨u, hu⟩ := this
      rw [g.mem_commonNeighbors] at hu
      have hu1 : σ u = u := Conway99Aux.fixed_neighbor h hp hp7 σ hσp hv hu.1
      exact Conway99Aux.fixed_neighbor h hp hp7 σ hσp hu1 hu.2.symm
  have hone : σ = 1 := by
    ext w
    exact hall w
  rw [hone] at hσ
  simp only [orderOf_one] at hσ
  exact absurd hσ.symm (by omega)

