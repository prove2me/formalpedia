-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.depth_of_linkage_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:29.458172+00:00
-- url     : https://prove2.me/submissions/c7e736b8-4b93-4409-9c3f-e9b178677530

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_kappa_floor_holds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_depth_nat_le_holds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_ShortWeightBounds_weight_nonneg__27470cb891f0
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_one_le_h
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_rank_pos_of_hyp
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_linkage_depth_eq_sum_difference
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_image_univ_eq_image_range
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_paramsLargePrime_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_orientation_lattice_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_weight_letters_holds
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_weight_reflection_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : DepthOfLink := by
  intro P hH hL ι W hW l hl hlJ τ w hlink
  obtain ⟨E, _, σ, _, O', F, L', _, _, _, _, _, _, I, _, Wl, u, c, D, cst, ep, J, botJ, kap, ζ, em, jj, inc,
    hRefl, hLinked, hCar, hNI, hU, hbot, hσ, hU', hsum⟩ := hlink
  have hd := paramsLargePrime_holds P hH hL l hlJ
  have hl2 : l ≠ 2 := by
    have h1 := hd.2.2.2.2.2.1
    have h2 := rank_pos_of_hyp P hH
    omega
  have hkap := kappa_floor_holds P l hl.one_le
  have ht : P.t + 2 * (h0 P / (l - 1)) < l := by
    rw [← hkap]
    exact hd.2.2.2.1
  have hrows := hW.what₂ τ
  have hshape : WorkedExample.ShapeAt (kc P) (W.j τ) P.t (W.q τ) D (inc τ) := by
    refine ⟨fun a => ?_, hsum, fun a h1 h2 => ?_⟩
    · rw [hU]
      exact weight_nonneg' P W τ a (by have := a.2; omega)
    · rw [hU, hbot]
      exact weight_on_block_eq_bot_add P hH W hW τ a h1 h2
  have hDB := WorkedExample.orientation_lattice_holds E σ (kc P) (W.j τ) P.t (W.q τ) l (h0 P) O' F L' I Wl u c D cst ep
    J botJ kap (inc τ) ζ em jj hl2 ht hRefl hLinked hCar hNI hshape
  unfold WorkedExample.DepthBound at hDB
  have hmw : ∀ τ', D.mw l P.t (h0 P / (l - 1)) (inc τ') = W.mw P τ' l := by
    intro τ'
    unfold WorkedExample.Labels.mw Wts.mw Wts.Uset
    rw [hbot, hkap, image_univ_eq_image_range P.Nr _ hrows (W.U P τ') (D.U (inc τ')) (hU τ')]
  have hmwF : D.mw l P.t (h0 P / (l - 1)) (σ (inc τ)) = W.mwF P τ l := by
    rw [hσ]
    unfold Wts.mwF Wts.botF Wts.UsetF
    by_cases hc : W.cj l τ = true
    · rw [if_pos hc, if_pos hc, if_pos hc, WorkedExample.weight_letters_holds E _ D σ (h0 P) P.t hRefl, hmw]
      have e : (h0 P : ℤ) - W.top P (W.fr l τ) = (h0 P : ℤ) - (W.bot P (W.fr l τ) + (P.t : ℤ) - 1) := by
        rw [top_eq_bot_add_t_sub_one P hH W hW]
      rw [e, WorkedExample.weight_reflection_holds]
      rfl
    · rw [if_neg hc, if_neg hc, if_neg hc, hmw]
      rfl
  rw [hmw, hmwF, ← linkage_depth_eq_sum_difference P.Nr (kc P) (W.j τ) P.t (W.q τ) hrows (W.lam τ) w (D.U (inc τ))
    (D.U' (inc τ)) (hU τ) hU'] at hDB
  have hle := depth_nat_le_holds P ι W l τ (by linarith [one_le_h P hH]) hl.one_le
  have hle' : ((W.q τ * h0 P + (l * W.mwF P τ l + W.mw P τ l) * (P.t + 2 * (h0 P / (l - 1))) : ℕ) : ℤ) ≤
      (W.iW P l τ : ℤ) := by exact_mod_cast hle
  refine le_trans ?_ hle'
  unfold depthAt
  push_cast
  exact hDB
end Formalism.CohomologicalDescent.ShortWeightBounds
