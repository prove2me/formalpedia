-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.inL_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:35.833747+00:00
-- url     : https://prove2.me/submissions/1875672a-727c-4d0d-b00a-62f7985aa614

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow_of_not_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    InL l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) :=
  fun m hm => coeff_subst_X_pow_of_not_dvd hl f m hm
end Formalism.L2.FormalSeriesBounds
