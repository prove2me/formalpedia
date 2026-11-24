-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.van_hRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:07.259223+00:00
-- url     : https://prove2.me/submissions/9e447c52-8a2b-4a97-a4e3-97791cabf21b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_van_expPt
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) :
    Van {w : WV I | w.1 = g} X.hRow := by
  unfold hRow
  apply Van.smul
  refine Van.subst {s : Fin 2 × κ | s.1 = g} (fun s => (X.van_expPt hex s.1 s.2).const) ?_ hh
  rintro ⟨g', x⟩ hs
  have hg : g' = g := hs
  subst hg
  exact X.van_expPt hex g' x
end Formalism.L2.FormalSeriesBounds.RawChart
