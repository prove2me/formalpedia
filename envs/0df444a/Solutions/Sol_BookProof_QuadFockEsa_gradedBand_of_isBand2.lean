-- Prove2me | solution 1 for BookProof.QuadFockEsa.gradedBand_of_isBand2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:09:48.624423+00:00
-- url     : https://prove2.me/submissions/f1ef5861-98b8-403c-a7f5-809561a85a1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQuadraticFockEsa.lean — solution of BookProof.QuadFockEsa.gradedBand_of_isBand2
import Mathlib
import Definitions.Def_ChapterQuadraticFockEsa
import Theorems.Thm_BookProof_QuadFockEsa_hermCol_eq_coef
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterGradedBandSchurEsa
import Definitions.Def_ChapterGradedBandSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.QuadFockEsa




open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.GradedBandSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow
open BookProof.HermiteGalerkin BookProof.FarisLavine
open BookProof.YangMillsHermite BookProof.FullQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBand

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin d →₀ ℕ))
    {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (h : IsBand2 T) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      (∀ k, (hermCol e T k).support.card ≤ M) ∧
      (∀ k, ∀ j ∈ (hermCol e T k).support,
        (((e j).degree : ℤ) - ((e k).degree : ℤ)).natAbs ≤ 2) ∧
      (∀ k j, ‖hermCol e T k j‖ ≤ C * (((e k).degree : ℝ) + 1)) := by

  classical
  obtain ⟨M, C, hC, hB⟩ := h
  choose F hFrep hFcard hFband hFcoef using fun α => hB α
  refine ⟨M, C, hC, ?_, ?_, ?_⟩
  · intro k
    have hsub : ∀ j ∈ (hermCol e T k).support, e j ∈ (F (e k)).support := by
      intro j hj
      have hne : hermCol e T k j ≠ 0 := Finsupp.mem_support_iff.mp hj
      rw [hermCol_eq_coef e (hFrep (e k)) j] at hne
      exact Finsupp.mem_support_iff.mpr hne
    refine le_trans (Finset.card_le_card_of_injOn e hsub ?_) (hFcard (e k))
    exact fun a _ b _ hab => e.injective hab
  · intro k j hj
    have hne : hermCol e T k j ≠ 0 := Finsupp.mem_support_iff.mp hj
    rw [hermCol_eq_coef e (hFrep (e k)) j] at hne
    exact hFband (e k) (e j) (Finsupp.mem_support_iff.mpr hne)
  · intro k j
    rw [hermCol_eq_coef e (hFrep (e k)) j]
    exact hFcoef (e k) (e j)
