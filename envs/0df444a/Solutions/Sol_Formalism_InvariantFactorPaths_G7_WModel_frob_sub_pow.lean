-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.frob_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:23.237532+00:00
-- url     : https://prove2.me/submissions/63c3dcd5-1be1-445c-97e8-061e74b543d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution (w : WW p) : ∃ y : WW p, WittVector.frobenius w - w ^ p = (p : WW p) * y := by
  have h : WittVector.frobenius w - w ^ p ∈ Ideal.span {(p : WW p)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    show WittVector.constantCoeff (WittVector.frobenius w - w ^ p) = 0
    rw [map_sub, map_pow]
    show (WittVector.frobenius w).coeff 0 - (w.coeff 0) ^ p = 0
    rw [WittVector.coeff_frobenius_charP, sub_self]
  exact Ideal.mem_span_singleton.1 h
end Formalism.InvariantFactorPaths.G7.WModel
