-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.coarse_le_c_w_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:49.058282+00:00
-- url     : https://prove2.me/submissions/38002b3f-c1ca-48d6-8dc7-e499461d5c2b

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_indexIntegral_nonneg_of_params
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_floor_height_le_height
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_kc_cast_le_k
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_sizeData_depth_nonneg
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_correction_weight_eq_formula
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : CoarseLeCW := by
  intro P hH hL ι W hW J τ hτ l hl
  have hdep0 := sizeData_depth_nonneg W P hH J τ l
  have hdep : (W.iW P l τ : ℝ) ≤ (W.sizeData₂ P J).depth P τ l :=
    Nat.floor_le (sizeData_depth_nonneg W P hH (fun _ => 0) τ l)
  have hi0 : (0 : ℝ) ≤ (W.iW P l τ : ℝ) := Nat.cast_nonneg _
  rw [correction_weight_eq_formula]
  unfold cCoarse
  obtain ⟨dep, hd⟩ : ∃ d, d = (W.sizeData₂ P J).depth P τ l := ⟨_, rfl⟩
  rw [← hd] at hdep hdep0 ⊢
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by linarith
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by linarith
  have hh0 := floor_height_le_height P hH
  have hk := kc_cast_le_k P
  have hw := hW.window τ
  have t1 : ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * (((h0 P : ℝ) + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6) ≤
      ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := div_le_div_of_nonneg_right (show (h0 P : ℝ) + (P.Nr : ℝ) ≤ P.h + (P.Nr : ℝ) by linarith) hl1
    linarith
  have hS : ((W.xp τ - W.xm τ : ℤ) : ℝ) ≤ P.S := by
    push_cast
    linarith [hw.1, hw.2.2]
  have hS0 : (0 : ℝ) ≤ ((W.xp τ - W.xm τ : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hw.2.1
  have hIl := indexIntegral_nonneg_of_params l (W.xm τ) (W.xp τ) (W.top P τ)
  have t3 : (kc P : ℝ) * (((W.xp τ - W.xm τ : ℤ) : ℝ) / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ)) ≤
      (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ)) :=
    mul_le_mul hk (by linarith [div_le_div_of_nonneg_right hS hl0])
      (add_nonneg (div_nonneg hS0 hl0) hIl) (Nat.cast_nonneg _)
  have t4 : (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
        min (min (kc P : ℝ) (P.t : ℝ)) ((W.iW P l τ : ℝ) / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0) ≤
      (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
        min (min (P.k : ℝ) (P.t : ℝ)) (dep / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0) := by
    split_ifs
    · exact min_le_min (min_le_min hk le_rfl) (div_le_div_of_nonneg_right hdep (Nat.cast_nonneg _))
    · exact le_rfl
  have t5 : ((W.iW P l τ : ℝ) / (l : ℝ)) * (1 + Real.posLog ((h0 P : ℝ) / (l : ℝ))) ≤
      (dep / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by
    have hp : Real.posLog ((h0 P : ℝ) / (l : ℝ)) ≤ max 0 (Real.log (P.h / (l : ℝ))) :=
      Real.posLog_le_posLog (div_nonneg (Nat.cast_nonneg _) hl0) (div_le_div_of_nonneg_right hh0 hl0)
    exact mul_le_mul (div_le_div_of_nonneg_right hdep hl0) (by linarith)
      (add_nonneg zero_le_one Real.posLog_nonneg) (div_nonneg hdep0 hl0)
  by_cases hc : ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ
  · simp only [if_pos hc] at t4 ⊢
    linarith
  · simp only [if_neg hc] at t4 ⊢
    linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
