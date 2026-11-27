-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.mem_tySet_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:08.770693+00:00
-- url     : https://prove2.me/submissions/ea58db86-68a4-4adf-91db-52684df830ec

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds
namespace RawChart
theorem _root_.solution (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ ∃ γ lam, X.TyWit V g x γ lam := Iff.rfl
end RawChart
end Formalism.L2.FormalSeriesBounds
