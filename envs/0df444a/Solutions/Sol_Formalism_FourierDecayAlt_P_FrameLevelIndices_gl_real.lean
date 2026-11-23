-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.gl_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:52.441234+00:00
-- url     : https://prove2.me/submissions/16620caf-b48f-4916-9182-9313a436886f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
theorem _root_.solution (q n : ℕ) (hq : 1 ≤ q) :
    ((∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) : ℕ) : ℝ) = (q : ℝ) ^ (n * n) * ∏ x ∈ range n, fac q x := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hpow : (q : ℝ) ^ (n * n) = ∏ _x ∈ range n, (q : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_range, pow_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n, ← Finset.prod_range_reflect, Nat.cast_prod,
    hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega)), fac]
  have e : n = (n - 1 - j) + (j + 1) := by omega
  push_cast
  conv_lhs => rw [e]
  conv_rhs => rw [e]
  have e' : n - 1 - j + (j + 1) - 1 - j = n - 1 - j := by omega
  rw [e', pow_add]
  field_simp
end Formalism.FourierDecayAlt.P.FrameLevelIndices
