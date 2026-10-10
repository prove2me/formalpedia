-- Prove2me | solution 1 for BookProof.HermiteBandHigher.Band.compGen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:47:20.578979+00:00
-- url     : https://prove2.me/submissions/3b26a5e1-366f-4b25-a30d-d6856d7a4997

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.Band.compGen
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_gpow_nonneg
import Theorems.Thm_BookProof_HermiteBandHigher_gpow_add
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBand

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    {r₁ r₂ M₁ M₂ m₁ m₂ : ℕ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hT : Band T r₁ M₁ C₁ (gpow m₁)) (hU : Band U r₂ M₂ C₂ (gpow m₂)) :
    Band (U ∘ₗ T) (r₁ + r₂) (M₁ * M₂)
      (M₁ * C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂) (gpow (m₁ + m₂)) := by

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
    have hterm : ∀ γ ∈ f.support,
        ‖f γ * (G γ) β‖ ≤ C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree := by
      intro γ hγ
      have hγdeg : ((γ.degree : ℤ) - (α.degree : ℤ)).natAbs ≤ r₁ := hband γ hγ
      have hle : (γ.degree : ℝ) + 1 ≤ ((r₁ : ℝ) + 1) * ((α.degree : ℝ) + 1) := by
        have hz : (γ.degree : ℤ) ≤ (α.degree : ℤ) + (r₁ : ℤ) := by omega
        have hr : (γ.degree : ℝ) ≤ (α.degree : ℝ) + (r₁ : ℝ) := by exact_mod_cast hz
        nlinarith [Nat.cast_nonneg (α := ℝ) α.degree, Nat.cast_nonneg (α := ℝ) r₁]
      have hsqrt : Real.sqrt ((γ.degree : ℝ) + 1)
          ≤ Real.sqrt ((r₁ : ℝ) + 1) * Real.sqrt ((α.degree : ℝ) + 1) := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt hle
      have hpow : gpow m₂ γ.degree
          ≤ Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow m₂ α.degree := by
        simp only [gpow, ← mul_pow]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt m₂
      have h1 : ‖f γ‖ ≤ C₁ * gpow m₁ α.degree := hcoef γ
      have h2 : ‖(G γ) β‖ ≤ C₂ * gpow m₂ γ.degree := hGcoef γ β
      calc ‖f γ * (G γ) β‖ = ‖f γ‖ * ‖(G γ) β‖ := norm_mul _ _
        _ ≤ (C₁ * gpow m₁ α.degree) * (C₂ * gpow m₂ γ.degree) :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC₁ (gpow_nonneg _ _))
        _ ≤ (C₁ * gpow m₁ α.degree)
              * (C₂ * (Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow m₂ α.degree)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC₁ (gpow_nonneg _ _))
            exact mul_le_mul_of_nonneg_left hpow hC₂
        _ = C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * (gpow m₁ α.degree * gpow m₂ α.degree) := by
            ring
        _ = C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree := by
            rw [gpow_add]
    calc ∑ γ ∈ f.support, ‖f γ * (G γ) β‖
        ≤ ∑ _γ ∈ f.support,
            C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree :=
          Finset.sum_le_sum hterm
      _ = f.support.card
            * (C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M₁ * (C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree) := by
          have hnn : (0:ℝ) ≤ C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree := by
            have : (0:ℝ) ≤ Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ := by positivity
            exact mul_nonneg (mul_nonneg (mul_nonneg hC₁ hC₂) this) (gpow_nonneg _ _)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
      _ = M₁ * C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ * gpow (m₁ + m₂) α.degree := by ring
