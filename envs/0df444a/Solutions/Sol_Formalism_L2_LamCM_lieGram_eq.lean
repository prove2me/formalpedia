-- Prove2me | solution 1 for Formalism.L2.LamCM.lieGram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:11.345198+00:00
-- url     : https://prove2.me/submissions/4fbc990d-f0e2-423d-96cf-6ed72cdbe77d

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    lieGram Hm W = (Real.pi : ℂ) • (W * Hm * W.conjTranspose).transpose := by
  ext i j
  simp only [lieGram, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end Formalism.L2.LamCM
