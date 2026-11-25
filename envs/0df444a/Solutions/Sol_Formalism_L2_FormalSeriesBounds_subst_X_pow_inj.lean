-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_X_pow_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:27.368504+00:00
-- url     : https://prove2.me/submissions/30a8345e-6bc8-4d67-bfbb-b49d676335ec

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow


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
theorem _root_.solution {l : ℕ} (hl : 0 < l) {f g : PowerSeries C}
    (h : PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) g) : f = g := by
  ext n
  have e := congrArg (PowerSeries.coeff (l * n)) h
  rwa [coeff_subst_X_pow hl, coeff_subst_X_pow hl] at e
end Formalism.L2.FormalSeriesBounds
