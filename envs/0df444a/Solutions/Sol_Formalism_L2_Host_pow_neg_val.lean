-- Prove2me | solution 1 for Formalism.L2.Host.pow_neg_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:31.963825+00:00
-- url     : https://prove2.me/submissions/0b6988c8-ec18-49a5-a961-1b207ad5c9a4

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution {N : ℕ} [NeZero N] {z : Qb} (hz : z ^ N = 1) (u : ZMod N) :
    z ^ (-u).val = z⁻¹ ^ u.val := by
  have hdvd : N ∣ (-u).val + u.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod N) N]
    simp
  obtain ⟨c, hc⟩ := hdvd
  have h1 : z ^ (-u).val * z ^ u.val = 1 := by rw [← pow_add, hc, pow_mul, hz, one_pow]
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1
end Formalism.L2.Host
