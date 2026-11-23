-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums.mulVecLin_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.145713+00:00
-- url     : https://prove2.me/submissions/85b2853c-21a7-4999-8961-433df6f487d9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_AffineFibreCountComparison
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_InvariantKernelTraceVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedLatticeOperators Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
open Module Finset Matrix
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n R) (hu : u.det ≠ 0) :
    Function.Injective u.mulVecLin := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply] at hxy
  have h2 : u.adjugate *ᵥ (u *ᵥ x) = u.adjugate *ᵥ (u *ᵥ y) := by rw [hxy]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  exact smul_right_injective _ hu h2
end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
