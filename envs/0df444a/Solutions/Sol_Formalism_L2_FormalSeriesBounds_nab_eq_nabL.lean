-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.nab_eq_nabL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:53.793051+00:00
-- url     : https://prove2.me/submissions/b933696c-208b-4c4d-8767-83768bb44546

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (g : PS C n dd) (P : MvPolynomial (Ls.ι n) C) :
    Y.nab Ls n g P = DescP.nabL (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (gofY Y n) g :=
  rfl
end Formalism.L2.FormalSeriesBounds
