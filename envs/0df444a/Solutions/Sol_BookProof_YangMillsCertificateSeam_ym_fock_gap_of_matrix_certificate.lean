-- Prove2me | solution 1 for BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T13:26:46.952921+00:00
-- url     : https://prove2.me/submissions/4757977d-86bb-4c14-a82f-cb2ce3ed09ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterYangMillsCertificateSeam.lean — solution of BookProof.YangMillsCertificateSeam.ym_fock_gap_of_matrix_certificate
import Mathlib
import Definitions.Def_ChapterYangMillsCertificateSeam
import Theorems.Thm_BookProof_YangMillsCertificateSeam_valid_of_checkBounds
import Theorems.Thm_BookProof_SchurGershgorin_ym_fock_gap_of_truncated_gap_and_matrix_bounds
import Definitions.Def_ChapterSirkCertificateReader
import Definitions.Def_ChapterSchurGershgorinGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTruncationGapLift
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFockGapChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsCertificateSeam



noncomputable section


open BookProof.SirkCertificateReader
open BookProof.SchurGershgorin
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

variable (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (c : MatrixBoundRecord)
    (hchk : c.checkBounds = true)
    (htrunc : ∀ x : finiteModeDomain (coreBasis e),
      (x : L2d 99) ∈ galerkinSpan (coreBasis e) c.m →
      ((c.muQ : ℚ) : ℝ) * ‖(x : L2d 99)‖ ^ 2 ≤ quadForm (ymHamiltonian (coreRepBasis e) fabc) x)
    (hdiag : ∀ i, c.m ≤ i →
      ((c.dminQ : ℚ) : ℝ) ≤ (entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i i).re)
    (hrow : ∀ i, c.m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.rmaxQ : ℚ) : ℝ))
    (hblockrow : ∀ i, i < c.m → ∀ S : Finset ℕ, (∀ j ∈ S, c.m ≤ j) →
      ∑ j ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.epsQ : ℚ) : ℝ))
    (hblockcol : ∀ j, c.m ≤ j → ∀ S : Finset ℕ, (∀ i ∈ S, i < c.m) →
      ∑ i ∈ S, ‖entry (coreBasis e) (ymHamiltonian (coreRepBasis e) fabc) i j‖
        ≤ ((c.epsQ : ℚ) : ℝ)) :
    dGamma (ymFockCol e fabc) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        ((c.lowerQ : ℚ) : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (ymFockCol e fabc) u)) : ℂ).re := by

  obtain ⟨heps, hlt, hdom⟩ := valid_of_checkBounds hchk
  have hepsR : (0 : ℝ) ≤ ((c.epsQ : ℚ) : ℝ) := by exact_mod_cast heps
  have hltR : ((c.epsQ : ℚ) : ℝ) < ((c.muQ : ℚ) : ℝ) := by exact_mod_cast hlt
  have hdomR : ((c.muQ : ℚ) : ℝ) ≤ ((c.dminQ : ℚ) : ℝ) - ((c.rmaxQ : ℚ) : ℝ) := by
    have : ((c.muQ : ℚ) : ℝ) ≤ (((c.dminQ - c.rmaxQ : ℚ)) : ℝ) := by exact_mod_cast hdom
    simpa using this
  have hlow : ((c.lowerQ : ℚ) : ℝ) = ((c.muQ : ℚ) : ℝ) - ((c.epsQ : ℚ) : ℝ) := by
    rw [MatrixBoundRecord.lowerQ]
    push_cast
    ring
  rw [hlow]
  exact ym_fock_gap_of_truncated_gap_and_matrix_bounds e fabc hepsR (by linarith)
    (fun _ => ((c.dminQ : ℚ) : ℝ)) (fun _ => ((c.rmaxQ : ℚ) : ℝ))
    htrunc (fun i hi => hdiag i hi) (fun i hi => hrow i hi)
    (fun _ _ => hdomR) hblockrow hblockcol
