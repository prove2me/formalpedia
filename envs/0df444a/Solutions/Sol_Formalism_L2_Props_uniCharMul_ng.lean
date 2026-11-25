-- Prove2me | solution 1 for Formalism.L2.Props.uniCharMul_ng
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:19.012083+00:00
-- url     : https://prove2.me/submissions/362e7277-7464-4fb3-bf38-e2e2e310b803

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLevel
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Theorems.Thm_Formalism_L2_Props_uniR_of_uniRT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Props
open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}
namespace Formalism.L2.Props
theorem _root_.solution (H : UniCharMul) : UniCharMulNG L n := by
  unfold UniCharMul at H
  intro s r ψ₀ ξ hψ hξ g h ug uh ugh hg hh hug huh hugh
  exact @H (s.v.adicCompletion L⁺) _ _ n r ψ₀ ξ hψ.1 hξ g h ug uh ugh (uniR_of_uniRT hg)
    (uniR_of_uniRT hh) hug huh hugh
end Formalism.L2.Props
