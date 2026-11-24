-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:57.069517+00:00
-- url     : https://prove2.me/submissions/7e2b713b-86ce-4e4b-80b1-e5ccabf36800

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (ϖ : v.adicCompletion F) (hϖ : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  unfold IsUnifV at hϖ
  rw [h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ
end Formalism.UG.P
