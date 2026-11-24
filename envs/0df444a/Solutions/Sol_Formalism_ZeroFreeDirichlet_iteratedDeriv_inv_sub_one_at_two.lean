-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.iteratedDeriv_inv_sub_one_at_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:08.019801+00:00
-- url     : https://prove2.me/submissions/b9fd25dd-41f9-4e83-9685-6e52647cd270

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (m : ℕ) :
    iteratedDeriv m (fun s : ℂ => (s - 1)⁻¹) 2 = (-1) ^ m * (m ! : ℂ) := by
  have h : (fun s : ℂ => (s - 1)⁻¹) = fun x => (1 * x - 1)⁻¹ := by simp
  rw [iteratedDeriv_eq_iterate, h, iter_deriv_inv_linear_sub]
  norm_num
end Formalism.ZeroFreeDirichlet
