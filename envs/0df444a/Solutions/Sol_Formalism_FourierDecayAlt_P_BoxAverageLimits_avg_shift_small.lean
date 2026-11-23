-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_shift_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:01.458996+00:00
-- url     : https://prove2.me/submissions/ed02ffd8-c90b-4506-aeed-52269c171fe9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_bpt_add_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_shift_sum_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B) (j : ι) (n : ℕ) :
    ‖avg e c (fun x => g (x + e j)) n - avg e c g n‖ ≤ 2 * B / (n + 1) := by
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  unfold avg
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs : ∑ m ∈ box ι (n + 1), g (bpt e (c n) m + e j) =
      ∑ m ∈ box ι (n + 1), (fun m => g (bpt e (c n) m)) (m + Pi.single j 1) := by
    refine Finset.sum_congr rfl (fun m _ => ?_); rw [bpt_add_single]
  rw [hs]
  have h := shift_sum_bound (n + 1) j (fun m => g (bpt e (c n) m)) B (fun m => hB _)
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hpow : ((n + 1 : ℕ) : ℝ) ^ Fintype.card ι = (n + 1 : ℝ) * (n + 1 : ℝ) ^ (Fintype.card ι - 1) := by
    push_cast
    rw [← pow_succ']; congr 1; omega
  calc (1 / ((n + 1 : ℝ) ^ Fintype.card ι)) * ‖_‖
      ≤ (1 / ((n + 1 : ℝ) ^ Fintype.card ι)) * (2 * B * ((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι - 1)) := by
        gcongr
    _ = 2 * B / (n + 1) := by
        have : ((n + 1 : ℕ) : ℝ) ^ Fintype.card ι = (n + 1 : ℝ) ^ Fintype.card ι := by push_cast; rfl
        rw [← this, hpow]
        push_cast
        field_simp
end Formalism.FourierDecayAlt.P.BoxAverageLimits
