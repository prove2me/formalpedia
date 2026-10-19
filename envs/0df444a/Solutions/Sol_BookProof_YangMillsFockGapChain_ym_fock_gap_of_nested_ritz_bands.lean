-- Prove2me | solution 1 for BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:53:30.57498+00:00
-- url     : https://prove2.me/submissions/561347b5-d950-4f23-8029-e324bd98d6b7

import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm_nonneg
import Theorems.Thm_BookProof_BandEnclosure_friedrichs_form_gap_of_nested_ritz_bands
import Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_gap_of_one_particle_form_gap
-- Generated from ChapterYangMillsFockGapChain.lean — theorem BookProof.YangMillsFockGapChain.ym_fock_gap_of_nested_ritz_bands
open BookProof.BandEnclosure
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.YangMillsFockGapChain


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockFieldPerturbation
open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.BandEnclosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)


theorem solution {mu : ℝ} (hmu : 0 ≤ mu)
    {lo hi : ℕ → ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc)
      (galerkinSpan (coreBasis e) (m + 1)) ∈ Set.Icc (lo m) (hi m))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    (∀ m, ritzInf (ymHamiltonian (coreRepBasis e) fabc)
        (finiteModeDomain (coreBasis e)) ∈ Set.Icc (lo m) (hi m)) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by
  obtain ⟨h1, _, Dom, A, S, hA, _, _, hgapA⟩ :=
    BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands (coreBasis e)
      (ymHamiltonian (coreRepBasis e) fabc)
      (BookProof.YangMillsHermite.ymHamiltonian_symmetricOn _ fabc)
      (BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg _ fabc) hnest hritz hlo
  refine ⟨h1, ?_⟩
  apply BookProof.YangMillsFockGapChain.ym_fock_gap_of_one_particle_form_gap e fabc hmu
  intro x
  obtain ⟨hx, hAx⟩ := hA.1 x
  have := hgapA ⟨(x : L2d 99), hx⟩
  unfold quadForm at this ⊢
  rw [hAx] at this
  exact this

