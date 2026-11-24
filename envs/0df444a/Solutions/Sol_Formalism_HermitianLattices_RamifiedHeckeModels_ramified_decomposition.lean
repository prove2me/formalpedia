-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.ramified_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:32.027865+00:00
-- url     : https://prove2.me/submissions/552ce872-bc65-4b7d-9ef5-d0902f51149c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : HeckeKernelPreservesRamified := by
  intro q _ n n' w ph hph fW
  simp only [kerK, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp_rw [Matrix.smul_vecMul]
  rw [← Finset.mul_sum, hph, mul_zero]
end Formalism.HermitianLattices.RamifiedHeckeModels
