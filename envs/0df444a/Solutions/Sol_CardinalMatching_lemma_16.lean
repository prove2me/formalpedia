-- Prove2me | solution 1 for CardinalMatching.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:55:11.405182+00:00
-- url     : https://prove2.me/submissions/65627eda-af08-4e3b-8371-82a4f5e2c94c

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context

namespace CardinalMatching

namespace Aux_CM

open Finset

theorem exists_delta {A G : Type} [Fintype A] [Fintype G] (s : Finset A) (N : Finset G)
    (f : A → G → ℝ) (hf : ∀ i ∈ s, ∀ j, j ∉ N → 0 < f i j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, ∀ j, j ∉ N → δ ≤ f i j := by
  classical
  by_cases hne : (s ×ˢ (univ \ N)).Nonempty
  · refine ⟨(s ×ˢ (univ \ N)).inf' hne (fun ij => f ij.1 ij.2), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      rintro ⟨i, j⟩ hij
      simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hij
      exact hf i hij.1 j hij.2
    · intro i hi j hj
      have hmem : (i, j) ∈ s ×ˢ (univ \ N) := by
        simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨hi, hj⟩
      exact Finset.inf'_le (fun ij : A × G => f ij.1 ij.2) hmem
  · refine ⟨1, one_pos, ?_⟩
    intro i hi j hj
    exfalso
    apply hne
    refine ⟨(i, j), ?_⟩
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact ⟨hi, hj⟩

theorem hall_tight {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (s : Finset A) :
    s.card ≤ (s.biUnion (fun i => univ.filter (fun j => α i * u i j = q i + p j))).card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨N, hN⟩ : ∃ N, N = s.biUnion (fun i => univ.filter (fun j => α i * u i j = q i + p j)) :=
    ⟨_, rfl⟩
  rw [← hN] at hlt
  obtain ⟨δ, hδ, hδle⟩ := exists_delta s N (fun i j => q i + p j - α i * u i j) (by
    intro i hi j hj
    have hne : α i * u i j ≠ q i + p j := by
      intro heq
      apply hj
      rw [hN, Finset.mem_biUnion]
      exact ⟨i, hi, by simp [heq]⟩
    have h1 := hfeas i j
    have h2 : α i * u i j < q i + p j := lt_of_le_of_ne h1 hne
    show 0 < q i + p j - α i * u i j
    linarith)
  have key := hopt (fun j => p j + if j ∈ N then δ else 0)
    (fun i => q i - if i ∈ s then δ else 0) (by
    intro i j
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ N
    · simp only [hi, hj, if_true]
      have := hfeas i j; linarith
    · simp only [hi, hj, if_true, if_false]
      have h2 : δ ≤ q i + p j - α i * u i j := hδle i hi j hj
      linarith
    · simp only [hi, hj, if_true, if_false]
      have := hfeas i j; linarith
    · simp only [hi, hj, if_false]
      have := hfeas i j; linarith)
  have e1 : ∑ i, (q i - if i ∈ s then δ else 0) = ∑ i, q i - s.card * δ := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ j, (p j + if j ∈ N then δ else 0) = ∑ j, p j + N.card * δ := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [e1, e2] at key
  have hc : (N.card : ℝ) < s.card := by exact_mod_cast hlt
  nlinarith

theorem row_bound {A G : Type} [Fintype G] (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j) (i : A) (z : G → ℝ)
    (hz1 : ∑ j, z j = 1) (hz0 : ∀ j, 0 ≤ z j) :
    α i * ∑ j, u i j * z j ≤ q i + ∑ j, p j * z j := by
  calc α i * ∑ j, u i j * z j = ∑ j, (α i * u i j) * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, (q i + p j) * z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hfeas i j) (hz0 j))
    _ = q i * ∑ j, z j + ∑ j, p j * z j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = q i + ∑ j, p j * z j := by rw [hz1, mul_one]

theorem strong_le {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x) :
    ∑ i, q i + ∑ j, p j ≤ weightedWelfare α u x := by
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i => univ.filter (fun j => α i * u i j = q i + p j))).mp (hall_tight α u p q hfeas hopt)
  have hcard : Fintype.card A = Fintype.card G := by
    have h1 : ∑ i, ∑ j, x i j = (Fintype.card A : ℝ) := by
      rw [Finset.sum_congr rfl (fun i _ => hx.1 i)]; simp
    have h2 : ∑ j, ∑ i, x i j = (Fintype.card G : ℝ) := by
      rw [Finset.sum_congr rfl (fun j _ => hx.2.1 j)]; simp
    rw [Finset.sum_comm] at h1
    exact_mod_cast h1.symm.trans h2
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  let y : A → G → ℝ := fun i j => if f i = j then 1 else 0
  have hy : IsFracPerfectMatching y := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [y]
    · intro j
      obtain ⟨i0, hi0⟩ := hfbij.2 j
      rw [Finset.sum_eq_single i0]
      · simp [y, hi0]
      · intro b _ hb
        simp only [y]
        rw [if_neg]
        intro h
        exact hb (hfinj (h.trans hi0.symm))
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro i j
      simp only [y]
      split_ifs <;> norm_num
  have hWy : weightedWelfare α u y = ∑ i, q i + ∑ j, p j := by
    unfold weightedWelfare
    have hrow : ∀ i, α i * ∑ j, u i j * y i j = q i + p (f i) := by
      intro i
      have hfi := hf i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfi
      have hs : ∑ j, u i j * y i j = u i (f i) := by
        simp only [y, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
      rw [hs]
      exact hfi
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib, hfbij.sum_comp p]
  have := hW y hy
  linarith

theorem budget_eq {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (i : A) :
    α i * ∑ j, u i j * x i j - q i = ∑ j, p j * x i j := by
  have hle : ∀ a ∈ (univ : Finset A), α a * ∑ j, u a j * x a j - q a ≤ ∑ j, p j * x a j := by
    intro a _
    have := row_bound α u p q hfeas a (x a) (hx.1 a) (fun j => hx.2.2 a j)
    linarith
  have hS := strong_le α u p q x hx hfeas hopt hW
  have hsum1 : ∑ a, (α a * ∑ j, u a j * x a j - q a) = weightedWelfare α u x - ∑ a, q a := by
    unfold weightedWelfare
    rw [Finset.sum_sub_distrib]
  have hsum2 : ∑ a, ∑ j, p j * x a j = ∑ j, p j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, hx.2.1 j, mul_one]
  have heq : ∑ a, (α a * ∑ j, u a j * x a j - q a) = ∑ a, ∑ j, p j * x a j := by
    apply le_antisymm (Finset.sum_le_sum hle)
    rw [hsum1, hsum2]; linarith
  exact (Finset.sum_eq_sum_iff_of_le hle).mp heq i (Finset.mem_univ i)

theorem row_bound_le {A G : Type} [Fintype G] (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j) (i : A) (z : G → ℝ) (hq : 0 ≤ q i)
    (hz1 : ∑ j, z j ≤ 1) (hz0 : ∀ j, 0 ≤ z j) :
    α i * ∑ j, u i j * z j ≤ q i + ∑ j, p j * z j := by
  calc α i * ∑ j, u i j * z j = ∑ j, (α i * u i j) * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, (q i + p j) * z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hfeas i j) (hz0 j))
    _ = q i * ∑ j, z j + ∑ j, p j * z j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ q i + ∑ j, p j * z j := by
        have := mul_le_of_le_one_right hq hz1
        linarith

theorem tight_of_pos {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (i : A) (j : G) (hj : 0 < x i j) : α i * u i j = q i + p j := by
  have hb := budget_eq α u p q x hx hfeas hopt hW i
  have hid : ∑ k, x i k * (q i + p k - α i * u i k) =
      q i * ∑ k, x i k + ∑ k, p k * x i k - α i * ∑ k, u i k * x i k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hzero : ∑ k, x i k * (q i + p k - α i * u i k) = 0 := by
    rw [hid, hx.1 i]; linarith
  have hnn : ∀ k ∈ (Finset.univ : Finset G), 0 ≤ x i k * (q i + p k - α i * u i k) := by
    intro k _
    have := hfeas i k
    exact mul_nonneg (hx.2.2 i k) (by linarith)
  have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hk with h | h
  · linarith
  · linarith

def OptB {G : Type} [Fintype G] (p u : G → ℝ) (t : ℝ) (y : G → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 ∧ ∑ j, p j * y j ≤ t ∧
    ∀ y' : G → ℝ, (∀ j, 0 ≤ y' j) → ∑ j, y' j ≤ 1 → ∑ j, p j * y' j ≤ t →
      ∑ j, u j * y' j ≤ ∑ j, u j * y j

theorem opt_own {A G : Type} [Fintype A] [Fintype G] [DecidableEq A] [DecidableEq G]
    (α : A → ℝ) (u : A → G → ℝ) (p : G → ℝ) (q : A → ℝ) (x : A → G → ℝ)
    (hx : IsFracPerfectMatching x)
    (hfeas : ∀ i j, α i * u i j ≤ q i + p j)
    (hopt : ∀ (p' : G → ℝ) (q' : A → ℝ), (∀ i j, α i * u i j ≤ q' i + p' j) →
      ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j)
    (hW : ∀ y, IsFracPerfectMatching y → weightedWelfare α u y ≤ weightedWelfare α u x)
    (hα : ∀ i, 0 < α i) (hq : ∀ i, 0 ≤ q i) (i : A) :
    OptB p (u i) (∑ j, p j * x i j) (x i) := by
  unfold OptB
  refine ⟨fun j => hx.2.2 i j, le_of_eq (hx.1 i), le_rfl, ?_⟩
  intro y' hy0 hy1 hyc
  have h1 := row_bound_le α u p q hfeas i y' (hq i) hy1 hy0
  have h2 := budget_eq α u p q x hx hfeas hopt hW i
  have h3 : α i * ∑ j, u i j * y' j ≤ α i * ∑ j, u i j * x i j := by linarith
  exact le_of_mul_le_mul_left h3 (hα i)

end Aux_CM

namespace Aux_CM

open Finset

theorem exists_ge_avg {G : Type} [Fintype G] (p z : G → ℝ) (hz0 : ∀ j, 0 ≤ z j)
    (hz1 : ∑ j, z j = 1) : ∃ j, 0 < z j ∧ ∑ i, p i * z i ≤ p j := by
  by_contra h
  push_neg at h
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ i, p i * z i := ⟨_, rfl⟩
  rw [← hA] at h
  obtain ⟨j0, hj0⟩ : ∃ j, 0 < z j := by
    by_contra h'
    push_neg at h'
    have : ∑ j, z j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (h' j) (hz0 j))
    linarith
  have hlt : ∑ j, p j * z j < ∑ j, A * z j := by
    apply Finset.sum_lt_sum
    · intro j _
      rcases (hz0 j).lt_or_eq with hpos | hzero
      · exact (mul_lt_mul_of_pos_right (h j hpos) hpos).le
      · rw [← hzero]; simp
    · exact ⟨j0, Finset.mem_univ _, mul_lt_mul_of_pos_right (h j0 hj0) hj0⟩
  rw [← Finset.mul_sum, hz1, mul_one, ← hA] at hlt
  exact lt_irrefl _ hlt

theorem exists_le_avg {G : Type} [Fintype G] (p z : G → ℝ) (hz0 : ∀ j, 0 ≤ z j)
    (hz1 : ∑ j, z j = 1) : ∃ j, 0 < z j ∧ p j ≤ ∑ i, p i * z i := by
  obtain ⟨j, hj, hle⟩ := exists_ge_avg (fun i => - p i) z hz0 hz1
  refine ⟨j, hj, ?_⟩
  have : ∑ i, (-p i) * z i = - ∑ i, p i * z i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hle' : ∑ i, (-p i) * z i ≤ -p j := hle
  linarith

theorem swap_sum {G : Type} [Fintype G] (f x : G → ℝ) (Y : G → G → ℝ) :
    ∑ g, f g * ∑ j, x j * Y j g = ∑ j, x j * ∑ g, f g * Y j g := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem swap_sum1 {G : Type} [Fintype G] (x : G → ℝ) (Y : G → G → ℝ) :
    ∑ g, ∑ j, x j * Y j g = ∑ j, x j * ∑ g, Y j g := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem avg_bundle {G : Type} [Fintype G] (p u : G → ℝ) (t : ℝ) (x : G → ℝ)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∑ j, x j = 1)
    (hall : ∀ j, 0 < x j → ∃ y, OptB p u t y ∧ 0 < y j) :
    ∃ Y, OptB p u t Y ∧ ∀ j, 0 < x j → 0 < Y j := by
  obtain ⟨js, hjs⟩ : ∃ j, 0 < x j := by
    by_contra h'
    push_neg at h'
    have : ∑ j, x j = 0 := Finset.sum_eq_zero (fun j _ => le_antisymm (h' j) (hx0 j))
    linarith
  obtain ⟨ys, hys, _⟩ := hall js hjs
  have hex : ∀ j, ∃ y, OptB p u t y ∧ (0 < x j → 0 < y j) := by
    intro j
    by_cases h : 0 < x j
    · obtain ⟨y, hy, hyj⟩ := hall j h
      exact ⟨y, hy, fun _ => hyj⟩
    · exact ⟨ys, hys, fun h' => absurd h' h⟩
  choose yf hyf using hex
  obtain ⟨Y, hYdef⟩ : ∃ Y : G → ℝ, Y = fun g => ∑ j, x j * yf j g := ⟨_, rfl⟩
  have hYg : ∀ g, Y g = ∑ j, x j * yf j g := fun g => by rw [hYdef]
  refine ⟨Y, ?_, ?_⟩
  · unfold OptB
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g
      rw [hYg]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hx0 j) ((hyf j).1.1 g))
    · simp only [hYg]
      rw [swap_sum1]
      calc ∑ j, x j * ∑ g, yf j g ≤ ∑ j, x j * 1 :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hyf j).1.2.1 (hx0 j))
        _ = 1 := by simp [hx1]
    · simp only [hYg]
      rw [swap_sum]
      calc ∑ j, x j * ∑ g, p g * yf j g ≤ ∑ j, x j * t :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hyf j).1.2.2.1 (hx0 j))
        _ = t := by rw [← Finset.sum_mul, hx1, one_mul]
    · intro y' hy0 hy1 hyc
      simp only [hYg]
      rw [swap_sum]
      calc ∑ g, u g * y' g = ∑ j, x j * ∑ g, u g * y' g := by
            rw [← Finset.sum_mul, hx1, one_mul]
        _ ≤ ∑ j, x j * ∑ g, u g * yf j g :=
            Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left ((hyf j).1.2.2.2 y' hy0 hy1 hyc) (hx0 j))
  · intro j hj
    have h1 : x j * yf j j ≤ ∑ k, x k * yf k j :=
      Finset.single_le_sum (f := fun k => x k * yf k j)
        (fun k _ => mul_nonneg (hx0 k) ((hyf k).1.1 j)) (Finset.mem_univ j)
    have h2 : 0 < x j * yf j j := mul_pos hj ((hyf j).2 hj)
    rw [hYg]
    linarith

theorem exists_eps {G : Type} [Fintype G] (x Y : G → ℝ) (hY0 : ∀ g, 0 ≤ Y g)
    (hx0 : ∀ g, 0 ≤ x g) (hs : ∀ g, 0 < x g → 0 < Y g) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g, ε * x g ≤ Y g := by
  classical
  by_cases hne : (univ.filter (fun g => 0 < x g)).Nonempty
  · refine ⟨(univ.filter (fun g => 0 < x g)).inf' hne (fun g => Y g / x g), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact div_pos (hs g hg) hg
    · intro g
      by_cases hg : 0 < x g
      · have hmem : g ∈ univ.filter (fun g => 0 < x g) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg
        have hle := Finset.inf'_le (fun g => Y g / x g) hmem
        exact (le_div_iff₀ hg).mp hle
      · have : x g = 0 := le_antisymm (not_lt.mp hg) (hx0 g)
        rw [this, mul_zero]; exact hY0 g
  · refine ⟨1, one_pos, ?_⟩
    intro g
    have hg : ¬ 0 < x g := by
      intro hg; apply hne; exact ⟨g, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hg⟩
    have : x g = 0 := le_antisymm (not_lt.mp hg) (hx0 g)
    rw [this, mul_zero]; exact hY0 g

theorem lin_sub {G : Type} [Fintype G] (f Y x : G → ℝ) (a c : ℝ) :
    ∑ g, f g * (a * Y g - c * x g) = a * ∑ g, f g * Y g - c * ∑ g, f g * x g := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun g _ => by ring)

theorem lin_sub1 {G : Type} [Fintype G] (Y x : G → ℝ) (a c : ℝ) :
    ∑ g, (a * Y g - c * x g) = a * ∑ g, Y g - c * ∑ g, x g := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem lin_add {G : Type} [Fintype G] (f Y x : G → ℝ) (a c : ℝ) :
    ∑ g, f g * (a * Y g + c * x g) = a * ∑ g, f g * Y g + c * ∑ g, f g * x g := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun g _ => by ring)

theorem lin_add1 {G : Type} [Fintype G] (Y x : G → ℝ) (a c : ℝ) :
    ∑ g, (a * Y g + c * x g) = a * ∑ g, Y g + c * ∑ g, x g := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem perturb {G : Type} [Fintype G] (p u : G → ℝ) (t : ℝ) (x Y : G → ℝ)
    (hY : OptB p u t Y) (hx0 : ∀ g, 0 ≤ x g) (hx1 : ∑ g, x g = 1)
    (hxc : ∑ g, p g * x g = t) (hs : ∀ g, 0 < x g → 0 < Y g) :
    ∑ g, u g * Y g ≤ ∑ g, u g * x g := by
  obtain ⟨hY0, hY1, hYc, hYo⟩ := hY
  obtain ⟨ε, hε, hεle⟩ := exists_eps x Y hY0 hx0 hs
  have hZ0 : ∀ g, 0 ≤ (1 + ε) * Y g - ε * x g := by
    intro g
    have h1 := hεle g
    have h2 : 0 ≤ ε * Y g := mul_nonneg hε.le (hY0 g)
    nlinarith
  have hZ1 : ∑ g, ((1 + ε) * Y g - ε * x g) ≤ 1 := by
    rw [lin_sub1, hx1]
    nlinarith
  have hZc : ∑ g, p g * ((1 + ε) * Y g - ε * x g) ≤ t := by
    rw [lin_sub, hxc]
    nlinarith
  have hv : ∑ g, u g * ((1 + ε) * Y g - ε * x g) ≤ ∑ g, u g * Y g :=
    hYo (fun g => (1 + ε) * Y g - ε * x g) hZ0 hZ1 hZc
  rw [lin_sub] at hv
  have : ε * ∑ g, u g * Y g ≤ ε * ∑ g, u g * x g := by linarith
  exact le_of_mul_le_mul_left this hε

theorem opt_at_T {G : Type} [Fintype G] (p u x : G → ℝ) (b b' T : ℝ)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∑ j, x j = 1) (hxc : ∑ j, p j * x j = b)
    (hbb : b < b') (hT : b' < T)
    (hbound : ∀ w : G → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j ≤ 1 → ∑ j, p j * w j ≤ b' →
      ∑ j, u j * w j ≤ ∑ j, u j * x j) :
    OptB p u T x := by
  unfold OptB
  refine ⟨hx0, hx1.le, by linarith, ?_⟩
  intro z hz0 hz1 hzc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (b' - b) / (T - b) := ⟨_, rfl⟩
  have hTb : 0 < T - b := by linarith
  have hs0 : 0 < s := by rw [hs]; exact div_pos (by linarith) hTb
  have hsT : s * T - s * b = b' - b := by
    rw [← mul_sub, hs, div_mul_cancel₀ _ (ne_of_gt hTb)]
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hTb]; linarith
  have hw0 : ∀ j, 0 ≤ s * z j + (1 - s) * x j := by
    intro j
    exact add_nonneg (mul_nonneg hs0.le (hz0 j)) (mul_nonneg (by linarith) (hx0 j))
  have hw1 : ∑ j, (s * z j + (1 - s) * x j) ≤ 1 := by
    rw [lin_add1, hx1]
    have := mul_le_of_le_one_right hs0.le hz1
    linarith
  have hwc : ∑ j, p j * (s * z j + (1 - s) * x j) ≤ b' := by
    rw [lin_add, hxc]
    have := mul_le_mul_of_nonneg_left hzc hs0.le
    nlinarith
  have hv : ∑ j, u j * (s * z j + (1 - s) * x j) ≤ ∑ j, u j * x j :=
    hbound (fun j => s * z j + (1 - s) * x j) hw0 hw1 hwc
  rw [lin_add] at hv
  have : s * ∑ j, u j * z j ≤ s * ∑ j, u j * x j := by
    have e : (1 - s) * ∑ j, u j * x j = ∑ j, u j * x j - s * ∑ j, u j * x j := by ring
    linarith
  exact le_of_mul_le_mul_left this hs0

theorem sum_le_sum_p {G : Type} [Fintype G] (p z : G → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hz0 : ∀ j, 0 ≤ z j) (hz1 : ∑ j, z j ≤ 1) : ∑ j, p j * z j ≤ ∑ j, p j := by
  apply Finset.sum_le_sum
  intro g _
  have : z g ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => hz0 j) (Finset.mem_univ g)
  exact mul_le_of_le_one_right (hp g) (by linarith)

theorem shift_id {G : Type} [Fintype G] [DecidableEq G] (f y : G → ℝ) (c : ℝ) (j0 j1 : G) :
    ∑ g, f g * (y g + (if g = j1 then c else 0) - (if g = j0 then c else 0)) =
      ∑ g, f g * y g + f j1 * c - f j0 * c := by
  have e : ∀ g, f g * (y g + (if g = j1 then c else 0) - (if g = j0 then c else 0)) =
      f g * y g + (if g = j1 then f g * c else 0) - (if g = j0 then f g * c else 0) := by
    intro g
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun g _ => e g), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem shift_id1 {G : Type} [Fintype G] [DecidableEq G] (y : G → ℝ) (c : ℝ) (j0 j1 : G) :
    ∑ g, (y g + (if g = j1 then c else 0) - (if g = j0 then c else 0)) = ∑ g, y g := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem shift_contra {G : Type} [Fintype G] [DecidableEq G] (p u y : G → ℝ) (T : ℝ) (j0 j1 : G)
    (hp : ∀ j, 0 ≤ p j) (hy : OptB p u T y) (hy0 : 0 < y j0) (hu : u j0 < u j1)
    (hne : j0 ≠ j1) (hT : ∑ j, p j ≤ T) : False := by
  obtain ⟨hY0, hY1, _, hYo⟩ := hy
  have hz0 : ∀ g, 0 ≤ y g + (if g = j1 then y j0 else 0) - (if g = j0 then y j0 else 0) := by
    intro g
    by_cases hg : g = j0
    · subst hg
      simp [hne]
    · rw [if_neg hg]
      have : 0 ≤ (if g = j1 then y j0 else 0) := by split_ifs <;> linarith
      linarith [hY0 g]
  have hz1 : ∑ g, (y g + (if g = j1 then y j0 else 0) - (if g = j0 then y j0 else 0)) ≤ 1 := by
    rw [shift_id1]; exact hY1
  have hzc : ∑ g, p g * (y g + (if g = j1 then y j0 else 0) - (if g = j0 then y j0 else 0)) ≤ T :=
    le_trans (sum_le_sum_p p _ hp hz0 hz1) hT
  have hv : ∑ g, u g * (y g + (if g = j1 then y j0 else 0) - (if g = j0 then y j0 else 0)) ≤
      ∑ g, u g * y g := hYo _ hz0 hz1 hzc
  rw [shift_id] at hv
  have : 0 < u j1 * y j0 - u j0 * y j0 := by
    have := mul_lt_mul_of_pos_right hu hy0
    linarith
  linarith

theorem no_lt {G : Type} [Fintype G] [DecidableEq G] (p u u' x x' : G → ℝ) (α' q' : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∑ j, x j = 1)
    (hx0' : ∀ j, 0 ≤ x' j) (hx1' : ∑ j, x' j = 1)
    (hlt : ∑ j, p j * x j < ∑ j, p j * x' j)
    (hO : OptB p u (∑ j, p j * x j) x) (hO' : OptB p u' (∑ j, p j * x' j) x')
    (hEF : ∑ j, u j * x' j ≤ ∑ j, u j * x j)
    (hθ : ∀ t, 0 ≤ t → ∀ j, (∃ y, OptB p u t y ∧ 0 < y j) ↔ (∃ y, OptB p u' t y ∧ 0 < y j))
    (hα' : 0 < α') (hfe : ∀ j, α' * u' j ≤ q' + p j)
    (htight : ∀ j, 0 < x' j → α' * u' j = q' + p j) : False := by
  obtain ⟨j1, hj1x, hj1p⟩ := exists_ge_avg p x' hx0' hx1'
  obtain ⟨j0, hj0x, hj0p⟩ := exists_le_avg p x hx0 hx1
  obtain ⟨b, hbdef⟩ : ∃ b, b = ∑ j, p j * x j := ⟨_, rfl⟩
  obtain ⟨b', hb'def⟩ : ∃ b', b' = ∑ j, p j * x' j := ⟨_, rfl⟩
  rw [← hbdef, ← hb'def] at hlt
  rw [← hb'def] at hO' hj1p
  rw [← hbdef] at hj0p
  have hb0 : 0 ≤ b := by
    rw [hbdef]; exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hx0 j))
  have hu01 : u' j0 < u' j1 := by
    have h1 := hfe j0
    have h2 := htight j1 hj1x
    have : α' * u' j0 < α' * u' j1 := by linarith
    exact lt_of_mul_lt_mul_left this hα'.le
  have hall : ∀ j, 0 < x' j → ∃ y, OptB p u b' y ∧ 0 < y j :=
    fun j hj => (hθ b' (by linarith) j).mpr ⟨x', hO', hj⟩
  obtain ⟨Y, hY, hYs⟩ := avg_bundle p u b' x' hx0' hx1' hall
  have hYx : ∑ j, u j * Y j ≤ ∑ j, u j * x' j :=
    perturb p u b' x' Y hY hx0' hx1' hb'def.symm hYs
  have hbound : ∀ w : G → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j ≤ 1 → ∑ j, p j * w j ≤ b' →
      ∑ j, u j * w j ≤ ∑ j, u j * x j := by
    intro w hw0 hw1 hwc
    have := hY.2.2.2 w hw0 hw1 hwc
    linarith
  have hsp : 0 ≤ ∑ j, p j := Finset.sum_nonneg (fun j _ => hp j)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ j, p j + b' + 1 := ⟨_, rfl⟩
  have hOT : OptB p u T x := opt_at_T p u x b b' T hx0 hx1 hbdef.symm hlt (by linarith) hbound
  obtain ⟨y', hy', hy'j0⟩ := (hθ T (by linarith) j0).mp ⟨x, hOT, hj0x⟩
  have hne : j0 ≠ j1 := by
    intro h; rw [h] at hu01; exact lt_irrefl _ hu01
  exact shift_contra p u' y' T j0 j1 hp hy' hy'j0 hu01 hne (by linarith)

end Aux_CM


end CardinalMatching

open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (hn : 2 ≤ n) :
    ∃ i, ¬ P.IsDummy i ∧ 0 < P.budget x α q i := by
  obtain ⟨hadm, hx, _, _, hα, hW, hD, hp, hq⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  obtain ⟨_, hu01, hk0, hdvd, _, _, _, _⟩ := hadm
  have hb : ∀ a, P.budget x α q a = ∑ j, p j * x a j :=
    fun a => Aux_CM.budget_eq α P.util p q x hx hfeas hopt hW a
  have htight : ∀ a j, 0 < x a j → α a * P.util a j = q a + p j :=
    fun a j hj => Aux_CM.tight_of_pos α P.util p q x hx hfeas hopt hW a j hj
  have hkn : 0 < P.k / n := Nat.div_pos (Nat.le_of_dvd hk0 hdvd) (by omega)
  let g0 : P.Good := Sum.inr ⟨0, hkn⟩
  have hpos_of : ∀ a j, 0 < x a j → 0 < p j → 0 < ∑ j', p j' * x a j' := by
    intro a j hxj hpj
    have h1 : p j * x a j ≤ ∑ j', p j' * x a j' :=
      Finset.single_le_sum (f := fun j' => p j' * x a j')
        (fun j' _ => mul_nonneg (hp j') (hx.2.2 a j')) (Finset.mem_univ j)
    have h2 : 0 < p j * x a j := mul_pos hpj hxj
    linarith
  have hreal_nd : ∀ r : Fin n × Fin P.k, ¬ P.IsDummy (Sum.inl r) := fun r h => h
  rcases (hp g0).lt_or_eq with hg0 | hg0
  · obtain ⟨a, ha⟩ : ∃ a, 0 < x a g0 := by
      by_contra h
      push_neg at h
      have : ∑ a, x a g0 = 0 := Finset.sum_eq_zero (fun a _ => le_antisymm (h a) (hx.2.2 a g0))
      rw [hx.2.1 g0] at this
      norm_num at this
    rcases a with r | (m | dmy)
    · exact ⟨Sum.inl r, hreal_nd r, by rw [hb]; exact hpos_of _ g0 ha hg0⟩
    · exact ⟨Sum.inr (Sum.inl m), fun h => h, by rw [hb]; exact hpos_of _ g0 ha hg0⟩
    · have hmin : ∀ j, p g0 ≤ p j := by
        intro j
        have h1 := htight (Sum.inr (Sum.inr dmy)) g0 ha
        have h2 := hfeas (Sum.inr (Sum.inr dmy)) j
        have e1 : P.util (Sum.inr (Sum.inr dmy)) g0 = P.d := rfl
        have e2 : P.util (Sum.inr (Sum.inr dmy)) j = P.d := rfl
        rw [e1] at h1
        rw [e2] at h2
        linarith
      let r : Fin n × Fin P.k := (⟨0, by omega⟩, ⟨0, hk0⟩)
      refine ⟨Sum.inl r, hreal_nd r, ?_⟩
      rw [hb]
      obtain ⟨j, hj, _⟩ :=
        Aux_CM.exists_ge_avg p (x (Sum.inl r)) (fun j => hx.2.2 _ j) (hx.1 _)
      exact hpos_of _ j hj (lt_of_lt_of_le hg0 (hmin j))
  · exfalso
    have hzero : ∀ r s : Fin n × Fin P.k, x (Sum.inl r) (Sum.inl s) = 0 := by
      intro r s
      by_contra hne
      have hpos : 0 < x (Sum.inl r) (Sum.inl s) := lt_of_le_of_ne (hx.2.2 _ _) (Ne.symm hne)
      have h1 := htight (Sum.inl r) (Sum.inl s) hpos
      have h2 := hfeas (Sum.inl r) g0
      have e1 : P.util (Sum.inl r) (Sum.inl s) = P.u r.1 s.1 := rfl
      have e2 : P.util (Sum.inl r) g0 = 2 := rfl
      rw [e1] at h1
      rw [e2, ← hg0] at h2
      have hu1 := (hu01 r.1 s.1).2
      have hα' := hα (Sum.inl r)
      have hps := hp (Sum.inl s)
      nlinarith
    have hrow : ∀ r : Fin n × Fin P.k, ∑ g : Fin (P.k / n), x (Sum.inl r) (Sum.inr g) = 1 := by
      intro r
      have := hx.1 (Sum.inl r)
      rw [Fintype.sum_sum_type] at this
      rw [Finset.sum_congr rfl (fun s _ => hzero r s), Finset.sum_const_zero, zero_add] at this
      exact this
    have hcol : ∀ g : Fin (P.k / n), ∑ r : Fin n × Fin P.k, x (Sum.inl r) (Sum.inr g) ≤ 1 := by
      intro g
      have := hx.2.1 (Sum.inr g)
      rw [Fintype.sum_sum_type] at this
      have hnn : 0 ≤ ∑ a : Fin P.interp.length ⊕ Fin (P.k / n - P.interp.length),
          x (Sum.inr a) (Sum.inr g) :=
        Finset.sum_nonneg (fun a _ => hx.2.2 _ _)
      linarith
    have htot : ∑ r : Fin n × Fin P.k, ∑ g : Fin (P.k / n), x (Sum.inl r) (Sum.inr g) ≤
        ∑ g : Fin (P.k / n), (1 : ℝ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun g _ => hcol g)
    rw [Finset.sum_congr rfl (fun r _ => hrow r)] at htot
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at htot
    have hnat : n * P.k ≤ P.k / n := by exact_mod_cast htot
    have h3 : P.k / n ≤ P.k := Nat.div_le_self _ _
    nlinarith
