-- Prove2me | solution 1 for CardinalMatching.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:35:08.538183+00:00
-- url     : https://prove2.me/submissions/d90a7030-3fb0-4cfb-b7ca-8aa45664fa3a

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

end Aux_CM


end CardinalMatching

open CardinalMatching in
theorem solution {n : ℕ} (P : ModParams n) (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ)
    (p : P.Good → ℝ) (q : P.Agent → ℝ) (hC : P.IsStep2Context x α p q) (i i' : P.Agent)
    (h : P.SameAgentType i i') : P.budget x α q i = P.budget x α q i' := by
  obtain ⟨_, hx, hEF, _, _, hW, hD, _, _⟩ := hC
  obtain ⟨hfeas, hopt⟩ := hD
  have hu : P.util i = P.util i' := funext h
  have e1 := hEF i i'
  have e2 := hEF i' i
  rw [← hu] at e2
  have hU : ∑ j, P.util i j * x i j = ∑ j, P.util i j * x i' j := le_antisymm e2 e1
  have r1 := Aux_CM.row_bound α P.util p q hfeas i (x i') (hx.1 i') (fun j => hx.2.2 i' j)
  have r2 := Aux_CM.row_bound α P.util p q hfeas i' (x i) (hx.1 i) (fun j => hx.2.2 i j)
  have c1 := Aux_CM.budget_eq α P.util p q x hx hfeas hopt hW i
  have c2 := Aux_CM.budget_eq α P.util p q x hx hfeas hopt hW i'
  rw [← hu] at r2 c2
  rw [hU] at c1 r2
  show α i * ∑ j, P.util i j * x i j - q i = α i' * ∑ j, P.util i' j * x i' j - q i'
  rw [← hu, hU]
  linarith
