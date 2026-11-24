-- Prove2me | solution 1 for Formalism.L2.Host.CharEx.norm_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:11.208942+00:00
-- url     : https://prove2.me/submissions/6c66b507-90a3-4cae-b6d6-79ce6c52d93a

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.L2.Host.CharEx
variable (L : Type) [Field L] [NumberField L]
variable {L}
namespace Formalism.L2.Host.CharEx
theorem _root_.solution {z : ℂˣ} {h : ℕ} (hh : 0 < h) (hz : ‖((z ^ h : ℂˣ) : ℂ)‖ = 1) : ‖(z : ℂ)‖ = 1 := by
  rw [Units.val_pow_eq_pow_val, norm_pow] at hz
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').mp hz
end Formalism.L2.Host.CharEx
