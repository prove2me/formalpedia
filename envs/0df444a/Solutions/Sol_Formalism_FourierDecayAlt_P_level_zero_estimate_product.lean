-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.level_zero_estimate_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:04.416771+00:00
-- url     : https://prove2.me/submissions/1f1375d5-538f-4fcb-b4ad-3f35ce4534bc

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Theorems.Thm_Formalism_FourierDecayAlt_P_words_pos_of_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.EstEOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S jv hG hE Kr hK0 Th e w _
  have hgram : ∀ ε, (S.mkData Kr hK0 Th e).gram ε 0 w [] [] = ∏ v, (S.pd v).RR ε 0 (w.1 v) [] [] := by
    intro ε
    show S.gram ε 0 w.1 [] [] = _
    simp [HidaSetting.gram, HidaSetting.gramLoc, loc, nLoc, nAux]
  have hsize : (S.mkData Kr hK0 Th e).wt w = ∏ v, S.sizeAt v (w.1 v) := rfl
  have hpos : 0 < ∏ v, S.sizeAt v (w.1 v) := by
    rw [← hsize]
    exact words_pos_of_parts E Wp Wq S hG Kr hK0 Th e w
  have hlim : Tendsto (fun ε => ∏ v, (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) :=
    tendsto_finsetProd _ (fun v _ => hE w v)
  have hre := ((Complex.continuous_re.tendsto _).comp hlim).div_const (∏ v, S.sizeAt v (w.1 v))
  have key : (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ)).re /
      (∏ v, S.sizeAt v (w.1 v)) = ∏ v, jv v := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
      mul_div_cancel_left₀ _ hpos.ne']
  rw [key] at hre
  simp_rw [hgram, hsize]
  exact hre
end Formalism.FourierDecayAlt.P
