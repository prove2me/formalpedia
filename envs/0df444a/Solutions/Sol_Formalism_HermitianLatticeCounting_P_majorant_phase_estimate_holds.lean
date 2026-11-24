-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.majorant_phase_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:37.138872+00:00
-- url     : https://prove2.me/submissions/918aa21a-2cc9-4b35-8980-43af346d8a20

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gb_norm_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantPhaseChoice := by
  intro V _ _ θ hθ u y1 S hu hS hy1
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hn : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hθv : θ ((Complex.I / (‖u‖ : ℂ)) • θ u) = (Complex.I / (‖u‖ : ℂ)) • u := by
    rw [map_smul, hθ.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul, gb_norm_theta hθ, norm_div, Complex.norm_I, Complex.norm_of_nonneg (norm_nonneg u),
      one_div, inv_mul_cancel₀ hu0]
  · intro w hw
    unfold majorantHermitianForm
    rw [hθv, inner_smul_left, hS w hw, mul_zero]
  · unfold majorantHermitianForm
    rw [hθv, inner_smul_left, hy1, map_div₀, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
    field_simp <;> ring
end Formalism.HermitianLatticeCounting.P
