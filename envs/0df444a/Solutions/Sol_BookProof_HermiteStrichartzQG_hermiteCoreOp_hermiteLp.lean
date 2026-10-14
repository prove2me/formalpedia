-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:20.212372+00:00
-- url     : https://prove2.me/submissions/2ec53568-1efc-441d-82bb-bc6220e6357e

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteCoreOp_hermiteLp
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
import Theorems.Thm_BookProof_QuantumGravityDensitized_mulHamiltonian_mulBasis
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) (n : ℕ) :
    hermiteCoreOp lam ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
      = ((lam n : ℂ)) • hermiteLp n := by

  have hsub : hermiteDiagRestrict lam ⟨hermiteLp n, hermiteLp_mem_hermiteDiagDomain lam n⟩
      = mulBasis lam n := by
    apply Subtype.ext
    simp [hermiteDiagRestrict, mulBasis]
  have hsmul : (lp.single 2 n ((lam n : ℂ)) : L2Nat)
      = ((lam n : ℂ)) • (lp.single 2 n (1 : ℂ) : L2Nat) := by
    rw [← lp.single_smul]
    simp
  simp only [hermiteCoreOp, LinearMap.comp_apply, Submodule.inclusion_apply, hermiteDiagOp,
    hsub, mulHamiltonian_mulBasis, hsmul]
  simp
  all_goals first
  | exact rfl
  | trace_state
