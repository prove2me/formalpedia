-- Prove2me | solution 1 for Formalism.UG.P.conv_biInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:15.178304+00:00
-- url     : https://prove2.me/submissions/3b9c73d4-9dab-44c0-9787-f3b8a03d30bf

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Theorems.Thm_Formalism_UG_P_conv_mul_right
import Theorems.Thm_Formalism_UG_P_conv_mul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]
end Formalism.UG.P
