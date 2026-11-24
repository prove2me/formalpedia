-- Prove2me | solution 1 for Formalism.L2.Host.mem_integers_of_isUnitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:38.193867+00:00
-- url     : https://prove2.me/submissions/6321e507-df68-4c9c-b96a-6c16061b45d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf

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
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Host
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hx.le
end Formalism.L2.Host
