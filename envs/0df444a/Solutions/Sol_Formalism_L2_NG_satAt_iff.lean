-- Prove2me | solution 1 for Formalism.L2.NG.satAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:09.246095+00:00
-- url     : https://prove2.me/submissions/4e9f9761-14ca-4db7-94c4-ce555ffefa46

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAutLoc
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsRowLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
open Formalism Formalism.L2 Formalism.L2.NG
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {L n}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
namespace Formalism.L2.NG
theorem _root_.solution (π : AutRep L n) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (α : Fin (n / 2) → ℂ) : SatAt π Dv α ↔ SatAtS π.S Dv α := Iff.rfl
end Formalism.L2.NG
