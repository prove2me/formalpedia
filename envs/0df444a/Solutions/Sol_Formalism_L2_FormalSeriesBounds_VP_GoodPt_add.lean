-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.GoodPt.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:03.670901+00:00
-- url     : https://prove2.me/submissions/6324b958-e125-4eae-b543-a6d1d48c404a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_addAt
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
theorem _root_.solution {a b : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) (hb : GoodPt V b) : GoodPt V (addAt Y a b) := by
  have h0 : ∀ q, MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
    intro q
    unfold P2
    split_ifs
    · exact ha.1 _
    · exact hb.1 _
  have hI : ∀ q, IntS V (P2 a b q) := by
    intro q
    unfold P2
    split_ifs
    · exact ha.2 _
    · exact hb.2 _
  refine ⟨fun i => cc_addAt Y ha.1 hb.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (P2 a b) (Y.B.G.F i))
  exact intS_subst_of_intS h0 hI (Y.intF i)
end GoodPt
end Formalism.L2.FormalSeriesBounds.VP
