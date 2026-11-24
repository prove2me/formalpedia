-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.coprime_case_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:30.981686+00:00
-- url     : https://prove2.me/submissions/e9b05503-7d39-4f6a-889c-2a88d3ddaed3

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
theorem _root_.solution : ConjRatioPowUnitModulus := by
  intro z g hz
  have hc : conj z ≠ 0 := (map_ne_zero _).2 hz
  refine ⟨by rw [norm_pow, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hz), one_pow], ?_⟩
  rw [← mul_pow, pow_mul, Complex.normSq_eq_conj_mul_self]
  congr 1
  field_simp
end Formalism.HermitianLattices.RamifiedHeckeModels
