-- Prove2me | solution 1 for BookProof.TruncationGapLift.ym_fock_gap_of_band_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:20.187117+00:00
-- url     : https://prove2.me/submissions/a1422193-ad4f-4d4c-9a01-df2deb469eee

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.ym_fock_gap_of_band_and_tail
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Theorems.Thm_BookProof_TruncationGapLift_quadForm_ge_of_le_ritzInf_on
import Theorems.Thm_BookProof_TruncationGapLift_ym_fock_gap_of_truncated_gap_and_tail
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.TruncationGapLift



noncomputable section


open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.BandEnclosure
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {mu eps lo hi : ℝ}
    (heps : 0 ≤ eps) (hmueps : 0 ≤ mu - eps)
    (hband : ritzInf (ymHamiltonian (coreRepBasis e) fabc) (galerkinSpan (coreBasis e) m)
      ∈ Set.Icc lo hi)
    (hlo : mu ≤ lo)
    (htail : ∀ w : finiteModeDomain (coreBasis e), (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      mu * ‖(w : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) w)
    (hcoup : ∀ x w : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      |(inner ℂ (x : L2d 99) (ymHamiltonian (coreRepBasis e) fabc w) : ℂ).re|
        ≤ eps * ‖(x : L2d 99)‖ * ‖(w : L2d 99)‖) :
    dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (mu - eps) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by

  have hritz : mu ≤ ritzInf (ymHamiltonian (coreRepBasis e) fabc)
      (galerkinSpan (coreBasis e) m) := hlo.trans hband.1
  exact ym_fock_gap_of_truncated_gap_and_tail e fabc heps hmueps
    (fun x hx => quadForm_ge_of_le_ritzInf_on (ymHamiltonian (coreRepBasis e) fabc)
      (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc) hritz x hx)
    htail hcoup
