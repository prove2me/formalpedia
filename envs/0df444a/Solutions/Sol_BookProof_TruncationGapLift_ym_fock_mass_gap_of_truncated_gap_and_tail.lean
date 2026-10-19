-- Prove2me | solution 1 for BookProof.TruncationGapLift.ym_fock_mass_gap_of_truncated_gap_and_tail
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:19.055165+00:00
-- url     : https://prove2.me/submissions/e15fcf83-9d55-47f6-956b-bcb29763a19c

-- Generated from ChapterTruncationGapLift.lean — solution of BookProof.TruncationGapLift.ym_fock_mass_gap_of_truncated_gap_and_tail
import Mathlib
import Definitions.Def_ChapterTruncationGapLift
import Theorems.Thm_BookProof_TruncationGapLift_gap_of_level_gap_and_tail
import Theorems.Thm_BookProof_YangMillsFockGapChain_ym_fock_mass_gap_of_one_particle_form_gap
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterYangMillsFriedrichs
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
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {mu eps : ℝ}
    (heps : 0 ≤ eps) (hmueps : eps < mu)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e), (x : L2d 99) ∈ galerkinSpan (coreBasis e) m →
      mu * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (htail : ∀ w : finiteModeDomain (coreBasis e), (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      mu * ‖(w : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) w)
    (hcoup : ∀ x w : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) m → (w : L2d 99) ∈ tailSpan (coreBasis e) m →
      |(inner ℂ (x : L2d 99) (ymHamiltonian (coreRepBasis e) fabc w) : ℂ).re|
        ≤ eps * ‖(x : L2d 99)‖ * ‖(w : L2d 99)‖) :
    (∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
        IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A) ∧
      dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 → u ≠ 0 →
        0 < (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re :=
  ym_fock_mass_gap_of_one_particle_form_gap e fabc (by linarith)
      (gap_of_level_gap_and_tail (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc)
        (ymHamiltonian_symmetricOn (coreRepBasis e) fabc) heps htrunc htail hcoup)
