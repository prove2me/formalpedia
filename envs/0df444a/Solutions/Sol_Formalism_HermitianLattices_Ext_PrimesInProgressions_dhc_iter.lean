-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhc_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:41.022553+00:00
-- url     : https://prove2.me/submissions/edcc501c-a47a-4084-8c06-d35829807a0f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c ρ : ℂ) (k : ℕ) (s : ℂ) :
    iteratedDeriv k (fun z => c / (z - ρ)) s =
      c * ((-1) ^ k * (k.factorial : ℂ)) * ((s - ρ) ^ (k + 1))⁻¹ := by
  have h : (fun z : ℂ => c / (z - ρ)) = fun z => c * (fun z : ℂ => (1 * z - ρ)⁻¹) z := by
    ext z
    simp [div_eq_mul_inv]
  have hk : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, mul_one, one_mul]
  rw [hk, zpow_neg, zpow_natCast]
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
