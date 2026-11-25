-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.addOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:00.254318+00:00
-- url     : https://prove2.me/submissions/e3516cac-af9c-4bf0-87c5-98e59da5c721

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (a b : Pt C n dd) : addOf (Y.B.FK C) a b = addAt Y a b := by
  funext i
  show MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![a, b] : Fin 2 → Pt C n dd) p.1 p.2)
      (MvPowerSeries.map (algebraMap C C) (Y.B.G.F i)) = MvPowerSeries.subst (P2 a b) (Y.B.G.F i)
  have hm : MvPowerSeries.map (algebraMap C C) (Y.B.G.F i) = Y.B.G.F i := by
    ext n
    simp [MvPowerSeries.coeff_map]
  rw [hm]
  congr 1
  funext q
  rcases q with ⟨j, l⟩
  fin_cases j <;> first | rfl | simp [P2]
end Formalism.L2.FormalSeriesBounds.VP
