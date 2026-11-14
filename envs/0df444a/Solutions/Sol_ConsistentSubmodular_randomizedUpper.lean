-- Prove2me | solution 1 for ConsistentSubmodular.randomizedUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:15.443013+00:00
-- url     : https://prove2.me/submissions/7843a39a-aacb-4d00-b0dd-0dce833c0b67

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Constants
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_eq_uOne
import Theorems.Thm_ConsistentSubmodular_HardInstance_abs_weightedValue_sub_le
import Theorems.Thm_ConsistentSubmodular_HardInstance_lp_bound
import Theorems.Thm_ConsistentSubmodular_HardInstance_weighted_main
import Theorems.Thm_ConsistentSubmodular_HardInstance_upper_large

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

/-- `ξ⋆ = 1 / (1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. -/
theorem xiStar_eq_uOne : xiStar = 1 / (1 + uOne ^ 3 * (1 + uOne)) := by
  rw [xiStar_eq_qStar, qStar_eq_uOne]

/-- The constants of the hard instance in Section 2.1 and Appendix A.2: `u₁ ∈ (0, 1)` is
a root of `Φ`, and `ξ⋆ = 1/(1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. -/
theorem exists_hardConstants : ∃ u₁ : ℝ, 0 < u₁ ∧ u₁ < 1 ∧ phi u₁ = 0 ∧
    xiStar = 1 / (1 + u₁ ^ 3 * (1 + u₁)) :=
  ⟨uOne, uOne_pos, uOne_lt_one, phi_uOne, xiStar_eq_uOne⟩

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

theorem card_cellSet {k W₀ : ℕ} {w : Fin 3 → ℕ} (hw : ∀ g, w g ≤ W₀)
    (B : Finset (Fin 3 × Fin k)) : (cellSet k W₀ w B).card = ∑ c ∈ B, w c.1 := by
  rw [cellSet, card_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hinner (g : Fin 3) (b : Fin k) :
      (∑ r : Fin W₀, if (g, b) ∈ B ∧ r.val < w g then 1 else 0) =
        if (g, b) ∈ B then w g else 0 := by
    by_cases hB : (g, b) ∈ B
    · simp only [hB, true_and, if_true]
      rw [← card_filter, Fin.card_filter_val_lt, min_eq_right (hw g)]
    · simp [hB]
  simp_rw [hinner]
  rw [← Fintype.sum_prod_type (fun c : Fin 3 × Fin k => if c ∈ B then w c.1 else 0),
    ← sum_filter]
  simp

theorem biUnion_cellSet {k W₀ : ℕ} {w : Fin 3 → ℕ} {ι : Type*} (S : Finset ι)
    (cells : ι → Finset (Fin 3 × Fin k)) :
    S.biUnion (fun e => cellSet k W₀ w (cells e)) = cellSet k W₀ w (S.biUnion cells) := by
  ext x
  simp only [cellSet, mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hx, hr⟩
    exact ⟨⟨e, he, hx⟩, hr⟩
  · rintro ⟨⟨e, he, hx⟩, hr⟩
    exact ⟨e, he, hx, hr⟩

theorem sum_weight_eq_fibers {k : ℕ} (w : Fin 3 → ℕ) (C : Finset (Fin 3 × Fin k)) :
    ∑ c ∈ C, w c.1 = ∑ g, w g * (fiber C g).card := by
  rw [← Finset.sum_fiberwise C Prod.fst]
  refine sum_congr rfl fun g _ => ?_
  rw [fiber, sum_congr rfl (fun c hc => by rw [(mem_filter.mp hc).2]), sum_const, smul_eq_mul,
    mul_comm]

/-- Unit-weight copies realize natural weights: the coverage of a family is its
weighted coverage with the weights `w g`. -/
theorem coverage_streamCover {k W₀ : ℕ} {w : Fin 3 → ℕ} (hw : ∀ g, w g ≤ W₀)
    (S : Finset (Fin (3 * k + 2))) :
    coverageValue (streamCover k W₀ w) S = weightedValue k (fun g => (w g : ℝ)) S := by
  have h : S.biUnion (streamCover k W₀ w) =
      (cellSet k W₀ w (S.biUnion (elementCells k))).map (Fintype.equivFin _).toEmbedding := by
    have hdef : streamCover k W₀ w =
        fun e => (cellSet k W₀ w (elementCells k e)).map (Fintype.equivFin _).toEmbedding := rfl
    rw [hdef, ← biUnion_cellSet]
    simp only [map_eq_image]
    rw [biUnion_image]
  rw [coverageValue, h, card_map, card_cellSet hw, sum_weight_eq_fibers]
  push_cast
  rfl

section Bounds

variable {k : ℕ} {u : Fin 3 → ℝ}

/-- A family covering at least `n_g` cells of every group `g` has weighted
coverage at least `Σ_g u_g n_g`. -/
theorem le_weightedValue (hu : ∀ g, 0 ≤ u g) (T : Finset (Fin (3 * k + 2))) {n₀ n₁ n₂ : ℝ}
    (h₀ : n₀ ≤ (fiber (T.biUnion (elementCells k)) 0).card)
    (h₁ : n₁ ≤ (fiber (T.biUnion (elementCells k)) 1).card)
    (h₂ : n₂ ≤ (fiber (T.biUnion (elementCells k)) 2).card) :
    u 0 * n₀ + u 1 * n₁ + u 2 * n₂ ≤ weightedValue k u T := by
  rw [weightedValue, Fin.sum_univ_three]
  have := mul_le_mul_of_nonneg_left h₀ (hu 0)
  have := mul_le_mul_of_nonneg_left h₁ (hu 1)
  have := mul_le_mul_of_nonneg_left h₂ (hu 2)
  linarith

end Bounds

end ConsistentSubmodular.HardInstance

end

end

section

noncomputable section

namespace ConsistentSubmodular.HardInstance

/-- `u₁ (1 + u₁) < 1` for the root `u₁` of `Φ` in `(0, 1)`: by
`Φ(x) = (x² + x - 1)(x² - 1) + 1 - 2x`. -/
theorem root_sum_lt_one {u₁ : ℝ} (h0 : 0 < u₁) (h1 : u₁ < 1) (hphi : phi u₁ = 0) :
    u₁ * (1 + u₁) < 1 := by
  unfold phi at hphi
  by_contra h
  have hs : 1 ≤ u₁ * (1 + u₁) := le_of_not_gt h
  have hkey : (u₁ * (1 + u₁) - 1) * (u₁ ^ 2 - 1) = 2 * u₁ - 1 := by linear_combination hphi
  have hneg : (u₁ * (1 + u₁) - 1) * (u₁ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  have hhalf : u₁ ≤ 1 / 2 := by linarith
  nlinarith

end ConsistentSubmodular.HardInstance

end

end

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- Expectations keep a pointwise bound up to an additive constant. -/
theorem expectation_le_add {n : ℕ} (μ : RandomTrajectory n) {g h : Finset (Fin n) → ℝ} {c : ℝ}
    (hgh : ∀ T, g T ≤ h T + c) (t : Fin (n + 1)) :
    μ.expectation g t ≤ μ.expectation h t + c := by
  unfold RandomTrajectory.expectation
  calc ∑ S, μ.prob S * g (S t) ≤ ∑ S, μ.prob S * (h (S t) + c) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hgh _) (μ.prob_nonneg S)
    _ = ∑ S, μ.prob S * h (S t) + c := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, μ.prob_sum, one_mul]

/-- `⌊v D⌋ / D` is within `1/D` of `v ≥ 0`. -/
theorem abs_floor_div_sub_le {v : ℝ} {D : ℕ} (hv : 0 ≤ v) (hD : 0 < (D : ℝ)) :
    |(⌊v * D⌋₊ : ℝ) / D - v| ≤ 1 / D := by
  have h1 : (⌊v * D⌋₊ : ℝ) ≤ v * D := Nat.floor_le (by positivity)
  have h2 : v * D < ⌊v * D⌋₊ + 1 := Nat.lt_floor_add_one _
  have hD' : (D : ℝ) ≠ 0 := hD.ne'
  have heq : (⌊v * D⌋₊ : ℝ) / D - v = ((⌊v * D⌋₊ : ℝ) - v * D) / D := by
    field_simp
  rw [heq, abs_div, abs_of_pos hD]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [abs_le]
  constructor <;> linarith

/-- **Theorem 1** from the constants of the hard instance: with `K = 16`, every
`ε ∈ [1/k, 1]` has an unweighted coverage stream on which every randomized
`εk`-consistent algorithm has expected value at most `(ξ⋆ + 16 ε)` times a
competitor's at some time. -/
theorem randomizedUpper_of {u₁ : ℝ} (h0 : 0 < u₁) (h1 : u₁ < 1) (hphi : phi u₁ = 0)
    (hxi : xiStar = 1 / (1 + u₁ ^ 3 * (1 + u₁))) : RandomizedUpperGoal := by
  have hξ0 : 0 ≤ xiStar := by rw [hxi]; positivity
  refine ⟨16, fun k ε hk hεk hε1 => ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hεk' : 1 ≤ ε * k := by rwa [div_le_iff₀ hkR] at hεk
  have hε0 : 0 < ε := by nlinarith
  by_cases hsmall : xiStar + 16 * ε < 1
  swap
  · exact upper_large hk (by linarith)
  have hε6 : ε ≤ 1 / 6 := by linarith
  have hs := root_sum_lt_one h0 h1 hphi
  have hk2 : 2 ≤ k := by
    have : (16 : ℝ) < k := by nlinarith
    exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  -- Bounding the approximation ratio at the exact weights `1, u₁, u₂`.
  have hC0 : (0 : ℝ) ≤ (⌊ε * k⌋₊ : ℕ) := Nat.cast_nonneg _
  have hC : ((⌊ε * k⌋₊ : ℕ) : ℝ) ≤ ε * k := Nat.floor_le (by positivity)
  have hlp := lp_bound h0 hs.le hphi hε0 hε6 hkR hεk' hC0 hC
  rw [← hxi] at hlp
  -- Removing the weights: `ũ_i = ⌊u_i D⌋ / D` with `D = ⌈1/ε⌉`, in unit-weight copies.
  set D : ℕ := ⌈1 / ε⌉₊ with hD
  have hDε : 1 / ε ≤ D := Nat.le_ceil _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hDε
  have hDne : (D : ℝ) ≠ 0 := hD0.ne'
  have h1D : 1 / (D : ℝ) ≤ ε := by
    rw [div_le_iff₀ hD0]
    rw [div_le_iff₀ hε0] at hDε
    linarith
  have hy0 : 0 ≤ lpThird u₁ := by unfold lpThird; positivity
  have hy1 : lpThird u₁ ≤ 1 := by unfold lpThird; nlinarith
  let w : Fin 3 → ℕ := ![D, ⌊u₁ * D⌋₊, ⌊lpThird u₁ * D⌋₊]
  have hw0 : w 0 = D := rfl
  have hw1 : w 1 = ⌊u₁ * D⌋₊ := rfl
  have hw2 : w 2 = ⌊lpThird u₁ * D⌋₊ := rfl
  have hfloor {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : ⌊v * D⌋₊ ≤ D := by
    have : ((⌊v * D⌋₊ : ℕ) : ℝ) ≤ D :=
      (Nat.floor_le (by positivity)).trans (by nlinarith)
    exact_mod_cast this
  have hw : ∀ g, w g ≤ D := by
    intro g
    fin_cases g
    · exact le_of_eq hw0
    · exact hfloor h0.le h1.le
    · exact hfloor hy0 hy1
  let v : Fin 3 → ℝ := fun g => (w g : ℝ) / D
  have hv0 : v 0 = lpWeights u₁ 0 := by
    change ((w 0 : ℕ) : ℝ) / D = lpWeights u₁ 0
    rw [hw0, lpWeights_zero, div_self hDne]
  have hv1 : |v 1 - lpWeights u₁ 1| ≤ ε := by
    change |((w 1 : ℕ) : ℝ) / D - lpWeights u₁ 1| ≤ ε
    rw [hw1, lpWeights_one]
    exact (abs_floor_div_sub_le h0.le hD0).trans h1D
  have hv2 : |v 2 - lpWeights u₁ 2| ≤ ε := by
    change |((w 2 : ℕ) : ℝ) / D - lpWeights u₁ 2| ≤ ε
    rw [hw2, lpWeights_two]
    exact (abs_floor_div_sub_le hy0 hD0).trans h1D
  have hvnn : ∀ g, 0 ≤ v g := fun g => div_nonneg (Nat.cast_nonneg _) hD0.le
  have hcov : ∀ T, coverageValue (streamCover k D w) T = D * weightedValue k v T := by
    intro T
    rw [coverage_streamCover hw, weightedValue, weightedValue, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    change (w g : ℝ) * _ = (D : ℝ) * ((w g : ℝ) / D * _)
    field_simp
  refine ⟨3 * k + 2, Fintype.card (Fin 3 × Fin k × Fin D), streamCover k D w, fun μ hμ => ?_⟩
  obtain ⟨t, A, hA, hcard, hfib, hE⟩ := weighted_main hk2 h0 hs.le (by linarith) hlp μ hμ
  -- The competitor is worth at least `k`, and every value moves by at most `2 ε k`.
  have hAk : (k : ℝ) ≤ weightedValue k v A := by
    have h := le_weightedValue hvnn A (n₀ := k) (n₁ := 0) (n₂ := 0) hfib (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
    rw [hv0, lpWeights_zero] at h
    linarith
  have hpert : ∀ T : Finset (Fin (3 * k + 2)),
      |weightedValue k v T - weightedValue k (lpWeights u₁) T| ≤ 2 * ε * k :=
    abs_weightedValue_sub_le hv0 hv1 hv2
  have hEv : μ.expectation (weightedValue k v) t ≤
      μ.expectation (weightedValue k (lpWeights u₁)) t + 2 * ε * k :=
    expectation_le_add μ (fun T => by linarith [(abs_le.mp (hpert T)).2]) t
  have hAu : weightedValue k (lpWeights u₁) A ≤ weightedValue k v A + 2 * ε * k := by
    linarith [(abs_le.mp (hpert A)).1]
  -- The ratio moves from `ξ⋆ + 12 ε ≤ 1` by at most `4 ε`.
  have hρ0 : 0 ≤ xiStar + 12 * ε := by linarith
  have hρ1 : xiStar + 12 * ε ≤ 1 := by linarith
  have hfinal : μ.expectation (weightedValue k v) t ≤ (xiStar + 16 * ε) * weightedValue k v A := by
    have g₁ := mul_le_mul_of_nonneg_left hAu hρ0
    have g₂ : (xiStar + 12 * ε) * (2 * ε * k) ≤ 2 * ε * k :=
      mul_le_of_le_one_left (by positivity) hρ1
    have g₃ := mul_le_mul_of_nonneg_left hAk (show 0 ≤ 4 * ε by linarith)
    nlinarith
  have hEcov : μ.expectation (coverageValue (streamCover k D w)) t =
      D * μ.expectation (weightedValue k v) t := by
    unfold RandomTrajectory.expectation
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [hcov]; ring
  refine ⟨t, A, hA, hcard, ?_, ?_⟩
  · rw [hcov]
    exact mul_pos hD0 (lt_of_lt_of_le hkR hAk)
  · rw [hEcov, hcov A]
    have := mul_le_mul_of_nonneg_left hfinal hD0.le
    linarith

end ConsistentSubmodular.HardInstance

end

end

section

open ConsistentSubmodular

theorem solution : RandomizedUpperGoal := by
  obtain ⟨u₁, h0, h1, hphi, hxi⟩ := Chains.exists_hardConstants
  exact HardInstance.randomizedUpper_of h0 h1 hphi hxi

end
