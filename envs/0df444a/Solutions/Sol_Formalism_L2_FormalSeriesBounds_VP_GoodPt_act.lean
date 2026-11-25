-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.GoodPt.act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:56.887121+00:00
-- url     : https://prove2.me/submissions/b024769d-c1a5-4baf-aa60-9fc7f61e98bc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_actAt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
section Three
variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
include ha hb hc
end Three
private theorem intS_subst_of_intS {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  first
    | exact IntS.subst ha0 ha hf
    | exact PartialDerivEval.intS_subst ha0 ha hf
    | exact AltInv.intS_subst ha0 ha hf
end VP
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
namespace GoodPt
theorem _root_.solution (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) : GoodPt V (actAt Y x a) := by
  refine ⟨fun i => cc_actAt Y x ha.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i))
  exact intS_subst_of_intS (a := fun q : Fin 1 × Fin dd => a q.2) (fun q => ha.1 q.2) (fun q => ha.2 q.2)
    (Y.intAct x i)
end GoodPt
end Formalism.L2.FormalSeriesBounds.VP
