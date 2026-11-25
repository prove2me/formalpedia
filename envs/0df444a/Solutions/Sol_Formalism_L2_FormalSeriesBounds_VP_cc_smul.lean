-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:02.656573+00:00
-- url     : https://prove2.me/submissions/4118a355-819d-43af-9671-3964c9d8213e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]
end Formalism.L2.FormalSeriesBounds.VP
