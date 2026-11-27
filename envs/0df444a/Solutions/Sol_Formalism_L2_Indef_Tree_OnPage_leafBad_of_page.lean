-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.OnPage.leafBad_of_page
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:41.44903+00:00
-- url     : https://prove2.me/submissions/3448838b-86ac-4500-91ae-4a0ed8db892b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_one_le_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_wt_bound
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_Se_le_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_b
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_c
import Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_bad_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
namespace Formalism.L2.Indef.Tree.OnPage
theorem _root_.solution (O : OnObj S P c)
    (hC : 0 ≤ c.C) (hCb1 : 14 ≤ c.Cb1) (hCb2 : 66 * c.C + 4 ≤ c.Cb2) (hx : 3 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h21 : RankAndLengthLowerBounds O) (h1 : LeafSZ1 O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h121 : LogPrimeProductBound O) (h1232 : ProductWithRatioBound O) (h75 : ConductorCongruentPrimePair O) (h19 : SquaredTimeBound O) (h18 : PowerTwelveBound O)
    (tVd : TieVd O) : LeafBad O := by
  have hx0 : 0 ≤ O.x := by linarith
  have hb := one_le_b O hx0
  have hf : 8 ≤ O.f := by
    have h4 : 4 ≤ O.f / 2 := hN4
    linarith
  have hm : 44 ≤ O.m := h1246.1
  have hSe := Se_le_b O hx0 h14
  have hfS : O.f * O.Se ≤ O.f * O.b := mul_le_mul_of_nonneg_left hSe (by linarith)
  refine ⟨show 0 ≤ c.Cb1 by linarith, show 0 ≤ c.Cb2 by linarith, fun j => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨_, hw1⟩ := wt_bound O hW j
    have hfk : O.f * O.k * O.bp ≤ O.f * O.b := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1232 (by linarith)
    exact bad_b (O.wt j) (O.f * O.Se) O.T (O.f * O.k * O.bp) (Real.log ((O.q1 * O.dd : ℕ) : ℝ)) O.f O.m O.b
      c.Cb1 hw1 hfS h1.2 hfk (Real.log_natCast_nonneg _) h121 hf hm hb hCb1
  · obtain ⟨hw0, hw1⟩ := wt_bound O hW j
    by_cases hS0 : 0 ≤ O.wt j + O.f * O.Se
    · exact bad_c c.C O.m O.vd (O.wt j) (O.f * O.Se) O.T O.f O.b _ O.L c.Cb2 hC tVd.1
        (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p) tVd.2.1 hS0 hw1 hfS h1.2 hf hm hb hCb2
    · have h0 := bad_c c.C O.m O.vd 0 0 O.T O.f O.b _ O.L c.Cb2 hC tVd.1
        (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p) tVd.2.1 (by norm_num) (by nlinarith) (by nlinarith) h1.2 hf hm hb hCb2
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p)) h0
      have hcm : 0 ≤ c.C * O.m * (2 + O.vd) := mul_nonneg (mul_nonneg hC (by linarith)) (by linarith [tVd.1])
      have := mul_nonpos_of_nonneg_of_nonpos hcm (le_of_lt (not_le.1 hS0))
      show 2 * (c.C * O.m * (2 + O.vd) * (O.wt j + O.f * O.Se)) + 2 * O.T + 2 ≤ _
      linarith
  · obtain ⟨hp1, hp2, hg1, hg2, -⟩ := h75
    obtain ⟨PP, hPP, hPPT⟩ := h19
    have hlogb : Real.log O.b = O.L := rfl
    have hg1p : (0 : ℝ) < (O.g1 : ℝ) := by exact_mod_cast hp1.pos
    have hg2p : (0 : ℝ) < (O.g2 : ℝ) := by exact_mod_cast hp2.pos
    have hlg1 : Real.log (O.g1 : ℝ) ≤ 9 * O.L := by
      calc Real.log (O.g1 : ℝ) ≤ Real.log (O.b ^ 9) := Real.log_le_log hg1p hg1
        _ = 9 * O.L := by rw [Real.log_pow, hlogb]; norm_num
    have hlg2 : Real.log (O.g2 : ℝ) ≤ 9 * O.L := by
      calc Real.log (O.g2 : ℝ) ≤ Real.log (O.b ^ 9) := Real.log_le_log hg2p hg2
        _ = 9 * O.L := by rw [Real.log_pow, hlogb]; norm_num
    have hlg : Real.log ((O.g1 * O.g2 : ℕ) : ℝ) = Real.log (O.g1 : ℝ) + Real.log (O.g2 : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hg1p.ne' hg2p.ne']
    have hl1 : 0 ≤ Real.log (O.g1 : ℝ) := Real.log_natCast_nonneg _
    have hl2 : 0 ≤ Real.log (O.g2 : ℝ) := Real.log_natCast_nonneg _
    have hT2 : O.T ^ 2 ≤ O.b := by
      have h3 : 1 ≤ PP ^ 3 := one_le_pow₀ hPP
      have : 1 * O.T ^ 2 ≤ PP ^ 3 * O.T ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      linarith
    exact bad_d O.T O.f O.rr O.L O.b _ h1.1 hT2 hf h21.1 h21.2 h18 (by rw [hlg]; linarith)
      (by rw [hlg]; linarith)
end Formalism.L2.Indef.Tree.OnPage
