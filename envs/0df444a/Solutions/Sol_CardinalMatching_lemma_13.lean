-- Prove2me | solution 1 for CardinalMatching.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:50:12.129232+00:00
-- url     : https://prove2.me/submissions/9ac4a8f2-9092-4cac-9cfc-bad31ed8a9f2

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_ModParams_IsStep2Context
import Definitions.Def_CardinalMatching_ModParams_theta

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


end CardinalMatching

open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (i : P.Agent) :
    0 ≤ P.budget x α q i ∧ P.IsOptBundle p i (P.budget x α q i) (x i) := by
  obtain ⟨_, hx, _, _, hα, hW, hD, hp, hq⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  have hb : P.budget x α q i = ∑ j, p j * x i j :=
    Aux_CM.budget_eq α P.util p q x hx hfeas hopt hW i
  have hO : Aux_CM.OptB p (P.util i) (∑ j, p j * x i j) (x i) :=
    Aux_CM.opt_own α P.util p q x hx hfeas hopt hW hα hq i
  rw [hb]
  exact ⟨Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (hx.2.2 i j)), hO⟩
