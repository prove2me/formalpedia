-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.u_function_le_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:21.946648+00:00
-- url     : https://prove2.me/submissions/a37e4b46-fee4-4d2d-a1f1-95414d618548

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_Vvar_bound5
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_sub_wmean_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.uF u0 ≤ D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) := by
  have hd := hS.2.2.2.2.2.2.2.2.2.1
  have hs : ∀ u, (D.muMaxN u0 u - D.h u0 u - D.K3 C) - wmean (D.d u0) (Lo5 D C Xpp u0)
      ≤ D.s u0 := by
    intro u
    unfold Data.s
    refine sub_wmean_le (hd u0) _ (fun u' => ?_)
    have h1 := (hSN u0 u).1
    have h2 := (hSN u0 u').2
    have h3 := (hSl u0 u).2
    have h4 := (hSl u0 u').1
    have h5 := Vvar_bound5 D C hS hE hH hCount u0 u u'
    unfold Data.K3
    try dsimp only
    linarith
  unfold Data.uF
  have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W u0))
    (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)
    (a := D.s u0 + (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0)))
    (fun u _ => by have := hs u; linarith)
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
