-- Prove2me | solution 1 for ClassicalComplexWPT.hasFPowerSeriesOnBall_sumTsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:22.5541+00:00
-- url     : https://prove2.me/submissions/cd315f52-38d0-4d81-94b8-7f541763885b

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Definitions.Def_ClassicalComplexWPT_NormalSum
import Theorems.Thm_ClassicalComplexWPT_norm_seriesTsum_le

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
open ClassicalComplexWPT
variable {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
namespace ClassicalComplexWPT
theorem _root_.solution
    (p : I → FormalMultilinearSeries 𝕜 E F) (r : ℝ≥0) (hr : 0 < r)
    (hcoeff : ∀ n, Summable (fun i ↦ ‖p i n‖))
    (hmajor : Summable (fun n ↦ (∑' i, ‖p i n‖) * (r : ℝ) ^ n)) :
    HasFPowerSeriesOnBall (sumTsum p) (seriesTsum p) 0 r := by
  have hrad : (r : ℝ≥0∞) ≤ (seriesTsum p).radius := by
    apply (seriesTsum p).le_radius_of_summable
    refine hmajor.of_nonneg_of_le (fun _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _))
      (fun n ↦ ?_)
    exact mul_le_mul_of_nonneg_right (norm_seriesTsum_le p hcoeff n)
      (pow_nonneg r.2 n)
  refine ⟨hrad, by exact_mod_cast hr, ?_⟩
  intro y hy
  simp only [zero_add]
  have hyrNN : ‖y‖₊ < r := by
    exact_mod_cast (mem_eball_zero_iff.mp hy)
  have hyr : ‖y‖ < (r : ℝ) := by exact_mod_cast hyrNN
  let a : ℕ → I → F := fun n i ↦ p i n (fun _ ↦ y)
  have hrowNorm (n : ℕ) : Summable (fun i ↦ ‖a n i‖) := by
    have hs : Summable (fun i ↦ ‖p i n‖ * ‖y‖ ^ n) := (hcoeff n).mul_right _
    refine hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    simpa [a] using (p i n).le_opNorm (fun _ ↦ y)
  have hrowBound (n : ℕ) :
      (∑' i, ‖a n i‖) ≤ (∑' i, ‖p i n‖) * ‖y‖ ^ n := by
    have hs : Summable (fun i ↦ ‖p i n‖ * ‖y‖ ^ n) := (hcoeff n).mul_right _
    calc
      (∑' i, ‖a n i‖) ≤ ∑' i, ‖p i n‖ * ‖y‖ ^ n := by
        apply (hrowNorm n).tsum_le_tsum
        · intro i
          simpa [a] using (p i n).le_opNorm (fun _ ↦ y)
        · exact hs
      _ = (∑' i, ‖p i n‖) * ‖y‖ ^ n := tsum_mul_right
  have hrow : Summable (fun n ↦ ∑' i, ‖a n i‖) := by
    refine hmajor.of_nonneg_of_le (fun _ ↦ tsum_nonneg (fun _ ↦ norm_nonneg _)) (fun n ↦ ?_)
    exact (hrowBound n).trans <| mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg y) hyr.le n) (tsum_nonneg fun _ ↦ norm_nonneg _)
  have hpairNorm : Summable (fun z : ℕ × I ↦ ‖a z.1 z.2‖) := by
    rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
    exact ⟨hrowNorm, hrow⟩
  have hpair : Summable (Function.uncurry a) := Summable.of_norm hpairNorm
  have houterNorm : Summable (fun n ↦ ‖∑' i, a n i‖) := by
    refine hrow.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    exact norm_tsum_le_tsum_norm (hrowNorm n)
  have houter : Summable (fun n ↦ ∑' i, a n i) := Summable.of_norm houterNorm
  have htarget : (∑' n, ∑' i, a n i) = sumTsum p y := by
    calc
      (∑' n, ∑' i, a n i) = ∑' i, ∑' n, a n i := hpair.tsum_comm.symm
      _ = sumTsum p y := by rfl
  have hqeval (n : ℕ) : seriesTsum p n (fun _ ↦ y) = ∑' i, a n i := by
    exact ContinuousMultilinearMap.tsum_eval (Summable.of_norm (hcoeff n)) _
  rw [← htarget]
  exact houter.hasSum.congr_fun (fun n ↦ hqeval n)
end ClassicalComplexWPT
