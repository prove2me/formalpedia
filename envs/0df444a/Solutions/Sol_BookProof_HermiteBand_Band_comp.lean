-- Prove2me | solution 1 for BookProof.HermiteBand.Band.comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:15.847665+00:00
-- url     : https://prove2.me/submissions/59c6a1f5-8bd0-47c7-aaf6-4b0e6daeff47

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.Band.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_g1_nonneg
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {M₁ M₂ : ℕ}
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hU : Band U 1 M₂ C₂ g1) (hT : Band T 1 M₁ C₁ g1) :
    Band (U ∘ₗ T) 2 (M₁ * M₂) (2 * M₁ * C₁ * C₂) g2 := by

  classical
  intro α
  obtain ⟨f, hrep, hcard, hband, hcoef⟩ := hT α
  choose G hGrep hGcard hGband hGcoef using hU
  refine ⟨f.sum fun γ c => c • G γ, ?_, ?_, ?_, ?_⟩
  · have h1 : (U ∘ₗ T) (hpsi α) = U (hcomb f) := by rw [LinearMap.comp_apply, hrep]
    rw [h1, hcomb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, hcomb,
      show (f.sum fun γ c => c • G γ) = ∑ γ ∈ f.support, f γ • G γ from rfl, map_sum]
    exact Finset.sum_congr rfl fun γ _ => by rw [map_smul, hGrep γ, map_smul]
  · have hsub : (f.sum fun γ c => c • G γ).support ⊆ f.support.biUnion fun γ => (G γ).support := by
      refine (Finsupp.support_sum).trans ?_
      intro β hβ
      simp only [Finset.mem_biUnion] at hβ ⊢
      obtain ⟨γ, hγ, hβγ⟩ := hβ
      exact ⟨γ, hγ, Finsupp.support_smul hβγ⟩
    calc (f.sum fun γ c => c • G γ).support.card
        ≤ (f.support.biUnion fun γ => (G γ).support).card := Finset.card_le_card hsub
      _ ≤ ∑ γ ∈ f.support, (G γ).support.card := Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ f.support, M₂ := Finset.sum_le_sum fun γ _ => hGcard γ
      _ = f.support.card * M₂ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ M₁ * M₂ := Nat.mul_le_mul_right _ hcard
  · intro β hβ
    have hmem : β ∈ f.support.biUnion fun γ => (G γ).support := by
      refine (Finsupp.support_sum).trans (by
        intro β' hβ'
        simp only [Finset.mem_biUnion] at hβ' ⊢
        obtain ⟨γ, hγ, hβγ⟩ := hβ'
        exact ⟨γ, hγ, Finsupp.support_smul hβγ⟩) hβ
    simp only [Finset.mem_biUnion] at hmem
    obtain ⟨γ, hγ, hβγ⟩ := hmem
    have h1 := hGband γ β hβγ
    have h2 := hband γ hγ
    omega
  · intro β
    have happ : (f.sum fun γ c => c • G γ) β = ∑ γ ∈ f.support, f γ * (G γ) β := by
      simp only [Finsupp.sum, Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [happ]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ γ ∈ f.support, ‖f γ * (G γ) β‖ ≤ 2 * C₁ * C₂ * g2 α.degree := by
      intro γ hγ
      have hγdeg : ((γ.degree : ℤ) - (α.degree : ℤ)).natAbs ≤ 1 := hband γ hγ
      have hle : (γ.degree : ℝ) ≤ (α.degree : ℝ) + 1 := by
        have : (γ.degree : ℤ) ≤ (α.degree : ℤ) + 1 := by omega
        exact_mod_cast this
      have h1 : ‖f γ‖ ≤ C₁ * g1 α.degree := hcoef γ
      have h2 : ‖(G γ) β‖ ≤ C₂ * g1 γ.degree := hGcoef γ β
      have hg1a : g1 α.degree = Real.sqrt ((α.degree : ℝ) + 1) := rfl
      have hg1g : g1 γ.degree = Real.sqrt ((γ.degree : ℝ) + 1) := rfl
      have hsa : Real.sqrt ((α.degree : ℝ) + 1) ^ 2 = (α.degree : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hsg : Real.sqrt ((γ.degree : ℝ) + 1) ^ 2 = (γ.degree : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hprod : g1 α.degree * g1 γ.degree ≤ 2 * g2 α.degree := by
        rw [hg1a, hg1g, g2]
        nlinarith [Real.sqrt_nonneg ((α.degree : ℝ) + 1), Real.sqrt_nonneg ((γ.degree : ℝ) + 1),
          sq_nonneg (Real.sqrt ((α.degree : ℝ) + 1) - Real.sqrt ((γ.degree : ℝ) + 1)),
          Nat.cast_nonneg (α := ℝ) α.degree]
      calc ‖f γ * (G γ) β‖ = ‖f γ‖ * ‖(G γ) β‖ := norm_mul _ _
        _ ≤ (C₁ * g1 α.degree) * (C₂ * g1 γ.degree) := by
            exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC₁ (g1_nonneg _))
        _ = C₁ * C₂ * (g1 α.degree * g1 γ.degree) := by ring
        _ ≤ C₁ * C₂ * (2 * g2 α.degree) := by
            refine mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 * C₁ * C₂ * g2 α.degree := by ring
    calc ∑ γ ∈ f.support, ‖f γ * (G γ) β‖
        ≤ ∑ _γ ∈ f.support, 2 * C₁ * C₂ * g2 α.degree := Finset.sum_le_sum hterm
      _ = f.support.card * (2 * C₁ * C₂ * g2 α.degree) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M₁ * (2 * C₁ * C₂ * g2 α.degree) := by
          have hg2 : (0:ℝ) ≤ g2 α.degree := by
            simp only [g2]
            positivity
          have hnn : (0:ℝ) ≤ 2 * C₁ * C₂ * g2 α.degree :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁) hC₂) hg2
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
      _ = 2 * M₁ * C₁ * C₂ * g2 α.degree := by ring
