-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.IsIU.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:47.209862+00:00
-- url     : https://prove2.me/submissions/d95d0e96-6b2b-49a6-96ef-aa4e3f94c648

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds
namespace IsIU
theorem _root_.solution {σ : Type} {U U' : MvPowerSeries σ C} (h : IsIU V U) (h' : IsIU V U') : IsIU V (U * U') :=
  ⟨IntS.mul h.1 h'.1, by rw [map_mul, AddValuation.map_mul, h.2, h'.2, add_zero]⟩
end IsIU
end Formalism.L2.FormalSeriesBounds
