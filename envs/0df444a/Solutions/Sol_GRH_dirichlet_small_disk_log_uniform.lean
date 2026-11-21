-- Prove2me | solution 1 for GRH.dirichlet_small_disk_log_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:29:14.590101+00:00
-- url     : https://prove2.me/submissions/4fd1285a-8561-4753-846f-eeddb200bdbe

import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_exists_holomorphic_log_normalized
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_borel_caratheodory_closedBall
import Theorems.Thm_Helfgott_LFunction_contour_growth_inputs
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Complex Set Metric
namespace GRHSubpower

noncomputable def K₀ : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

lemma summable_K₀ : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

lemma norm_term_le (z : ℂ) (hz : 3 / 2 ≤ z.re) (n : ℕ) :
    ‖1 / (n : ℂ) ^ z‖ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    simp [Complex.zero_cpow hz0]
  · rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn, one_div]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hz)

lemma right_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : 3 / 2 ≤ z.re) : ‖χ.LFunction z‖ ≤ K₀ := by
  rw [χ.LFunction_eq_LSeries (by linarith)]
  have hterm (n : ℕ) : ‖LSeries.term (fun n : ℕ => χ n) z n‖ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term, if_neg hn.ne', norm_div]
      exact (div_le_div_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans
        (by simpa only [norm_div, norm_one] using norm_term_le z hz n)
  have hsum := Summable.of_nonneg_of_le
    (fun n => norm_nonneg (LSeries.term (fun n : ℕ => χ n) z n)) hterm summable_K₀
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hterm summable_K₀)

lemma abs_log_le (x : ℝ) (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at this
    have : 0 < x := hx
    linarith
  · have := Real.log_le_sub_one_of_pos hx
    have : 0 < x⁻¹ := inv_pos.mpr hx
    linarith

lemma norm_log_le (w : ℂ) (hw : w ≠ 0) : ‖Complex.log w‖ ≤ ‖w‖ + ‖w‖⁻¹ + Real.pi := by
  have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_le ‖w‖ (norm_pos_iff.mpr hw)
  have h3 : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
  linarith

noncomputable def Mre : ℝ := |Real.log K₀| + 1
noncomputable def Ac : ℝ := |K₀| + 2 + Real.pi
noncomputable def A₁ : ℝ :=
  max (2 * Mre * (49 / 100) / (1 / 2 - 49 / 100) + Ac * (1 / 2 + 49 / 100) / (1 / 2 - 49 / 100)) 1

lemma Mre_pos : 0 < Mre := by unfold Mre; positivity

lemma Ac_nonneg : 0 ≤ Ac := by unfold Ac; positivity

lemma re_sub_le {z c : ℂ} {r : ℝ} (hz : z ∈ ball c r) : |z.re - c.re| < r := by
  rw [mem_ball, dist_eq_norm] at hz
  have := Complex.abs_re_le_norm (z - c)
  rw [sub_re] at this
  linarith

lemma exists_log_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (c : ℂ) (hc : c.re = 2) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball c (1 / 2)) ∧
      EqOn (Complex.exp ∘ E) χ.LFunction (ball c (1 / 2)) ∧
      ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A₁ := by
  have hre : ∀ z ∈ ball c (1 / 2), 3 / 2 < z.re := by
    intro z hz; have h := re_sub_le hz; rw [hc] at h; linarith [(abs_lt.mp h).1]
  have hdiff : DifferentiableOn ℂ χ.LFunction (ball c (1 / 2)) := fun z hz =>
    (χ.differentiableAt_LFunction z (Or.inl (by rintro rfl; have h := hre 1 hz; norm_num at h))).differentiableWithinAt
  have hnz : ∀ z ∈ ball c (1 / 2), χ.LFunction z ≠ 0 := by
    intro z hz
    have hz1 : 1 < z.re := by linarith [hre z hz]
    rw [χ.LFunction_eq_LSeries hz1]
    exact χ.LSeries_ne_zero_of_one_lt_re hz1
  have hc0 : χ.LFunction c ≠ 0 := hnz c (mem_ball_self (by norm_num))
  obtain ⟨E, hEd, hEeq, hEc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized (by norm_num) hdiff hnz
      (Complex.exp_log hc0)
  refine ⟨E, hEd, hEeq, ?_⟩
  intro z hz
  have hRe : ∀ w ∈ ball c (1 / 2), (E w).re ≤ Mre := by
    intro w hw
    have h1 : Complex.exp (E w) = χ.LFunction w := hEeq hw
    have h2 : Real.exp (E w).re = ‖χ.LFunction w‖ := by rw [← Complex.norm_exp, h1]
    have h3 : (E w).re = Real.log ‖χ.LFunction w‖ := by rw [← h2, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖χ.LFunction w‖ := norm_pos_iff.mpr (hnz w hw)
    have hle := right_bound χ (le_of_lt (hre w hw))
    have h4 : Real.log ‖χ.LFunction w‖ ≤ Real.log K₀ := Real.log_le_log hpos hle
    unfold Mre
    linarith [le_abs_self (Real.log K₀)]
  have hcA : ‖E c‖ ≤ Ac := by
    rw [hEc]
    refine (norm_log_le _ hc0).trans ?_
    have hge := (Helfgott.LFunction_contour_growth_inputs q χ 0 2).1 c (le_of_eq hc.symm)
    have hle := right_bound χ (z := c) (by rw [hc]; norm_num)
    have hinv : ‖χ.LFunction c‖⁻¹ ≤ (1/2:ℝ)⁻¹ := inv_anti₀ (by norm_num) hge
    norm_num at hinv
    unfold Ac
    linarith [le_abs_self K₀]
  have hbc := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
    (g := E) (c := c) (r := 49 / 100) (R := 1 / 2) (M := Mre) (A := Ac)
    (by norm_num) (by norm_num) Mre_pos Ac_nonneg hEd hRe hcA hz
  exact hbc.trans (le_max_left _ _)

end GRHSubpower
theorem solution :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℂ), c.re = 2 →
      ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball c (1 / 2)) ∧
        EqOn (Complex.exp ∘ E) χ.LFunction (ball c (1 / 2)) ∧
        ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A := by
  exact ⟨GRHSubpower.A₁, le_max_right _ _,
    fun _ _ χ c hc => GRHSubpower.exists_log_small χ c hc⟩
