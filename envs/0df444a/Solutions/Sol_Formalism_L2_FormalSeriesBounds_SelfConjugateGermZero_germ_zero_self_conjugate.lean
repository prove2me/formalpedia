-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.germ_zero_self_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:39.856112+00:00
-- url     : https://prove2.me/submissions/e6183f74-467c-42cf-8733-e3d9f815f855

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lawS_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lawS_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lgS_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lgS_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_exS_lg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_sat_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_general_germ_zero


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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution : GermZeroSelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact GeneralGermZero.general_germ_zero (Y.rawSelf p) (lawS Y) (fun x => lawS_const Y x) (fun x => lawS_int Y x) (lgS_add Y p)
    (fun x μ hμ => lgS_lin Y p x μ hμ) (fun x => exS_lg Y p x) (sat_self Y p) H
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
