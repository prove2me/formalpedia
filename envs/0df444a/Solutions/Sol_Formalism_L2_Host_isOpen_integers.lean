-- Prove2me | solution 1 for Formalism.L2.Host.isOpen_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:35.586457+00:00
-- url     : https://prove2.me/submissions/8b287eda-e32a-475f-9b9a-9fe807928370

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : IsOpen ((v.adicCompletionIntegers L : Set (v.adicCompletion L))) :=
  Valued.isOpen_valuationSubring _
end Formalism.L2.Host
