-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernelDeriv_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/0190fe11-931f-4087-85b2-98bbeae3c5e1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripSchwarzAngle_mem_Ioo
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernelDeriv_pos
import Theorems.Thm_CohnElkies_norm_stripRegularizedHolomorphicPoissonKernelDeriv_neg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ∃ S ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ S, ∀ y : ℝ,
        ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          C * Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  let a : ℝ := Real.pi / (2 * ℓ)
  let A : ℂ → ℝ :=
    fun w => Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ))
  let sin0 : ℝ := A z
  let D : ℝ := 4 * ℓ ^ 2 * (sin0 / 2) ^ 2
  let Cpos : ℝ := Real.pi * Real.exp (a * (z.re + 1)) / D
  let Cneg : ℝ := Real.pi * Real.exp (-a * (z.re - 1)) / D
  have ha : 0 < a := by
    try dsimp [a]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  have hsin0 : 0 < sin0 := by
    try dsimp [sin0, A]
    exact Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hD : 0 < D := by
    try dsimp [D]
    positivity
  have hA : Continuous A := by
    try dsimp [A]
    fun_prop
  have hstrip :
      Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z := by
    have him : Continuous (fun w : ℂ => w.im) := by
      fun_prop
    exact (isOpen_Ioo.preimage him).mem_nhds hz
  have hsinset : A ⁻¹' Ioi (sin0 / 2) ∈ 𝓝 z := by
    apply (isOpen_Ioi.preimage hA).mem_nhds
    change sin0 / 2 < sin0
    linarith
  have hCpos : 0 ≤ Cpos := by
    try dsimp [Cpos]
    positivity
  have hCneg : 0 ≤ Cneg := by
    try dsimp [Cneg]
    positivity
  refine ⟨Metric.ball z 1 ∩
      (Complex.im ⁻¹' Ioo (-ℓ) ℓ) ∩
      (A ⁻¹' Ioi (sin0 / 2)),
    inter_mem (inter_mem (Metric.ball_mem_nhds z (by norm_num))
      hstrip) hsinset,
    Cpos + Cneg, add_nonneg hCpos hCneg, ?_⟩
  intro w hw y
  obtain ⟨⟨hwball, hwstrip⟩, hwsin⟩ := hw
  have hdist : ‖w - z‖ < (1 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using! hwball
  have hreabs := Complex.abs_re_le_norm (w - z)
  simp only [Complex.sub_re] at hreabs
  have hreupper : w.re ≤ z.re + 1 := by
    linarith [le_abs_self (w.re - z.re)]
  have hrelower : z.re - 1 ≤ w.re := by
    linarith [neg_le_abs (w.re - z.re)]
  have hsinw : sin0 / 2 <
      Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) := by
    exact hwsin
  have hden :
      D ≤ 4 * ℓ ^ 2 *
        Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2 := by
    try dsimp [D]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact
      (sq_le_sq₀ (by positivity) (le_trans
        (by positivity : 0 ≤ sin0 / 2) hsinw.le)).2 hsinw.le
  rcases le_total 0 y with hy | hy
  · have hnum :
        Real.pi * Real.exp (Real.pi * (w.re - y) / (2 * ℓ)) ≤
          Real.pi * Real.exp (a * (z.re + 1 - y)) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply Real.exp_le_exp.mpr
      calc
        Real.pi * (w.re - y) / (2 * ℓ) =
            a * (w.re - y) := by
          try dsimp [a]
          ring
        _ ≤ a * (z.re + 1 - y) :=
          mul_le_mul_of_nonneg_left (by linarith) ha.le
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          Real.pi * Real.exp (Real.pi * (w.re - y) / (2 * ℓ)) /
            (4 * ℓ ^ 2 *
              Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2) :=
        norm_stripRegularizedHolomorphicPoissonKernelDeriv_pos
          hℓ hwstrip y
      _ ≤ Real.pi * Real.exp (a * (z.re + 1 - y)) / D := by
        exact div_le_div₀
          (by positivity) hnum hD hden
      _ = Cpos * Real.exp ((-a) * y) := by
        have hsplit :
            Real.exp (a * (z.re + 1 - y)) =
              Real.exp (a * (z.re + 1)) * Real.exp ((-a) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsplit]
        try dsimp [Cpos]
        ring
      _ ≤ (Cpos + Cneg) *
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
        rw [abs_of_nonneg hy]
        change
          Cpos * Real.exp ((-a) * y) ≤
            (Cpos + Cneg) * Real.exp ((-a) * y)
        exact mul_le_mul_of_nonneg_right
          (by linarith) (Real.exp_pos _).le
  · have hnum :
        Real.pi * Real.exp (-(Real.pi * (w.re - y) / (2 * ℓ))) ≤
          Real.pi * Real.exp (-a * (z.re - 1 - y)) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply Real.exp_le_exp.mpr
      calc
        -(Real.pi * (w.re - y) / (2 * ℓ)) =
            -(a * (w.re - y)) := by
          try dsimp [a]
          ring
        _ ≤ -(a * (z.re - 1 - y)) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_left (by linarith) ha.le
        _ = -a * (z.re - 1 - y) := by ring
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          Real.pi *
            Real.exp (-(Real.pi * (w.re - y) / (2 * ℓ))) /
            (4 * ℓ ^ 2 *
              Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2) :=
        norm_stripRegularizedHolomorphicPoissonKernelDeriv_neg
          hℓ hwstrip y
      _ ≤ Real.pi * Real.exp (-a * (z.re - 1 - y)) / D := by
        exact div_le_div₀
          (by positivity) hnum hD hden
      _ = Cneg * Real.exp (a * y) := by
        have hsplit :
            Real.exp (-a * (z.re - 1 - y)) =
              Real.exp (-a * (z.re - 1)) * Real.exp (a * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsplit]
        try dsimp [Cneg]
        ring
      _ ≤ (Cpos + Cneg) *
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
        rw [abs_of_nonpos hy]
        change
          Cneg * Real.exp (a * y) ≤
            (Cpos + Cneg) * Real.exp ((-a) * (-y))
        have hexp : Real.exp ((-a) * (-y)) = Real.exp (a * y) := by
          congr 1
          ring
        rw [hexp]
        exact mul_le_mul_of_nonneg_right
          (by linarith) (Real.exp_pos _).le
end CohnElkies
