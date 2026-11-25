-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.IntS_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:56.100375+00:00
-- url     : https://prove2.me/submissions/40c7834b-66f8-4e8e-902a-57b88f80b9da

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {C : Type} [Field C] {V : VF C} {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]
end Formalism.L2.FormalSeriesBounds.VP
