-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.avg_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:18.707081+00:00
-- url     : https://prove2.me/submissions/986b9a33-138a-4ec2-a207-00011482d99e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_card_box

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B) (n : ℕ) :
    ‖avg e c g n‖ ≤ B := by
  have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
  unfold avg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ (box ι (n + 1)).card * B := by
    calc ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ ∑ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m ∈ box ι (n + 1), B := Finset.sum_le_sum (fun m _ => hB _)
      _ = (box ι (n + 1)).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [card_box] at h1
  push_cast at h1
  rw [one_div, inv_mul_le_iff₀ hpos]
  linarith
end Formalism.FourierDecayAlt.P.BoxAverageLimits
