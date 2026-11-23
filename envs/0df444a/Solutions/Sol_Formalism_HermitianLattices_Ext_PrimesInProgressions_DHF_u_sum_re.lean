-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:19.795809+00:00
-- url     : https://prove2.me/submissions/7f38775b-20e2-4ae4-aeeb-44c78784b66f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
