-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.majorant_cauchy_schwarz_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:23.200712+00:00
-- url     : https://prove2.me/submissions/7083fb1c-170a-44ef-a074-9c39f895adb8

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MomentPointwiseBound := by
  intro V ι _ _ _ c x P d ka la la1 hla hd hP hc
  have h1 : ‖d‖ * ‖P‖ ≤ ∑ i, ‖c i‖ * ‖x i‖ := by
    rw [← norm_smul, hP]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_smul _ _).le)
  have h2 : (∑ i, ‖c i‖ * ‖x i‖) ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖x i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : (‖d‖ * ‖P‖) ^ 2 ≤ (∑ i, ‖c i‖ * ‖x i‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h4 : (‖d‖ * ‖P‖) ^ 2 ≤ 4 * la ^ 2 * ∑ i, ‖x i‖ ^ 2 :=
    h3.trans (h2.trans (mul_le_mul_of_nonneg_right hc hX))
  rw [hd] at h4
  have e : (ka * la1 / la) ^ 2 * ‖P‖ ^ 2 = (2 * ka * la1 * ‖P‖) ^ 2 / (4 * la ^ 2) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith
end Formalism.HermitianLatticeCounting.P
