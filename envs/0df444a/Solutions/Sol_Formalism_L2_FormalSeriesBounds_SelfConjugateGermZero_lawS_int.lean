-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.lawS_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:00.363808+00:00
-- url     : https://prove2.me/submissions/dadab293-ebd2-4976-9d33-aa29922e26ca

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_intS_iff_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_intS_X


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
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (x : Fin 2 × Fin dd) : IntS V (lawS Y x) := by
  unfold lawS
  rw [AbstractGermZero.intS_iff_alt]
  exact AltInv.intS_subst (v := V.v) (fun _ => by simp)
    (fun q => (AbstractGermZero.intS_iff_alt V _).mp (FormalGermZero.intS_X _)) ((AbstractGermZero.intS_iff_alt V _).mp (Y.intF x.2))
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
