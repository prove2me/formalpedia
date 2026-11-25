-- Prove2me | solution 1 for Formalism.L2.Host.CharEx.isUnitary_of_unitIdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:05:51.977909+00:00
-- url     : https://prove2.me/submissions/d2276c27-0385-4fef-8cea-1a303d811b15

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen
import Theorems.Thm_Formalism_L2_Host_CharEx_classExp
import Theorems.Thm_Formalism_L2_Host_CharEx_norm_pow_eq_one

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
theorem _root_.solution (χ : HChar L) (h : ∀ u ∈ unitIdeles L, ‖((χ.1 u : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  obtain ⟨n, hn, hx⟩ := classExp L
  intro x
  obtain ⟨k, hk⟩ := hx x
  apply norm_pow_eq_one hn
  have h2 := h _ hk
  rwa [map_mul, χ.2.2 k, mul_one, map_pow] at h2
end Formalism.L2.Host.CharEx
