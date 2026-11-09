-- Prove2me | solution 1 for BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T20:03:08.033047+00:00
-- url     : https://prove2.me/submissions/da730d86-bd44-4c48-ab93-a3062d6d9a71

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.strongResAt_of_abs_sub_lt
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_res_sub_res
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterStoneResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

set_option maxHeartbeats 1000000 in
theorem solution {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (hlt : |m - l| < |l|) (h : StrongResAt T S l) : StrongResAt T S m := by

  intro y
  have hlabs : 0 < |l| := abs_pos.mpr hl
  set c : ℂ := ((m - l : ℝ) : ℂ) * Complex.I with hc
  have hcabs : ‖c‖ = |m - l| := by
    rw [hc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hid : ∀ (A : UnboundedSelfAdjoint E) (z : E),
      A.resCLM m z = A.resCLM l z + c • A.resCLM l (A.resCLM m z) := by
    intro A z
    have key := res_sub_res A hl hm z
    have hcc : (((l - m : ℝ)) : ℂ) * Complex.I = -c := by rw [hc]; push_cast; ring
    rw [hcc, neg_smul] at key
    have h3 : c • ((A.res l (((A.res m z : A.domain) : E)) : A.domain) : E)
        = -(((A.res l z : A.domain) : E) - ((A.res m z : A.domain) : E)) := by
      rw [key, neg_neg]
    simp only [UnboundedSelfAdjoint.resCLM_apply]
    rw [h3]
    abel
  have hdiff : ∀ n, (S n).resCLM m y - T.resCLM m y
      = ((S n).resCLM l y - T.resCLM l y)
        + (c • ((S n).resCLM l ((S n).resCLM m y - T.resCLM m y))
          + c • ((S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y))) := by
    intro n
    have e1 := hid (S n) y
    have e2 := hid T y
    have e3 : (S n).resCLM l ((S n).resCLM m y - T.resCLM m y)
        = (S n).resCLM l ((S n).resCLM m y) - (S n).resCLM l (T.resCLM m y) := map_sub _ _ _
    rw [e3]
    linear_combination (norm := module) e1 - e2
  have hstep : ∀ n, ‖(S n).resCLM m y - T.resCLM m y‖ * (1 - |m - l| / |l|)
      ≤ ‖(S n).resCLM l y - T.resCLM l y‖
        + |m - l| * ‖(S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)‖ := by
    intro n
    have h1 : ‖c • ((S n).resCLM l ((S n).resCLM m y - T.resCLM m y))‖
        ≤ |m - l| * ((1 / |l|) * ‖(S n).resCLM m y - T.resCLM m y‖) := by
      rw [norm_smul, hcabs]
      have := (S n).norm_resCLM_apply_le l ((S n).resCLM m y - T.resCLM m y)
      have habs : (0:ℝ) ≤ |m - l| := abs_nonneg _
      exact mul_le_mul_of_nonneg_left this habs
    have h2 : ‖c • ((S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y))‖
        = |m - l| * ‖(S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)‖ := by
      rw [norm_smul, hcabs]
    have hA := norm_add_le ((S n).resCLM l y - T.resCLM l y)
      (c • ((S n).resCLM l ((S n).resCLM m y - T.resCLM m y))
        + c • ((S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)))
    have hB := norm_add_le (c • ((S n).resCLM l ((S n).resCLM m y - T.resCLM m y)))
      (c • ((S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)))
    rw [← hdiff n] at hA
    have hprod : |m - l| * ((1 / |l|) * ‖(S n).resCLM m y - T.resCLM m y‖)
        = (|m - l| / |l|) * ‖(S n).resCLM m y - T.resCLM m y‖ := by
      field_simp
    nlinarith [hA, hB, h1, h2, hprod]
  have ha : Tendsto (fun n => ‖(S n).resCLM l y - T.resCLM l y‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (h y)
  have hb : Tendsto
      (fun n => ‖(S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (h (T.resCLM m y))
  have hk1 : 0 < 1 - |m - l| / |l| := by
    have : |m - l| / |l| < 1 := (div_lt_one hlabs).mpr hlt
    linarith
  have hlim : Tendsto (fun n => (‖(S n).resCLM l y - T.resCLM l y‖
      + |m - l| * ‖(S n).resCLM l (T.resCLM m y) - T.resCLM l (T.resCLM m y)‖)
      / (1 - |m - l| / |l|)) atTop (𝓝 0) := by
    have := (ha.add (hb.const_mul |m - l|)).div_const (1 - |m - l| / |l|)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [le_div_iff₀ hk1]
  exact hstep n
