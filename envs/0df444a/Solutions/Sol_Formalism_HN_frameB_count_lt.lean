-- Prove2me | solution 1 for Formalism.HN.frameB_count_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:29.767054+00:00
-- url     : https://prove2.me/submissions/5d07465d-76ef-4af5-a49f-0c304dae5f83

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrame
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNExtreme
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Theorems.Thm_Formalism_HN_polygon_slopes_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {R V E : Type} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    (L : Submodule R V) (hL : IsLat ρ L) (θ : ℝ) :
    ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) =
      (rk ρ L : ℝ) - rk ρ (hnStep ρ L θ) := by
  have h2 := (polygon_slopes_characterization R V E ρ L hL).2.1 θ
  have h3 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (rk ρ L))))
    (fun j => θ ≤ slopeList ρ L j)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at h3
  have h4 : ((univ.filter (fun j => θ ≤ slopeList ρ L j)).card : ℝ) +
      ((univ.filter (fun j => slopeList ρ L j < θ)).card : ℝ) = (rk ρ L : ℝ) := by
    exact_mod_cast h3
  rw [h2] at h4
  linarith
end Formalism.HN
