-- Prove2me | solution 1 for GRH.logDeriv_nonprincipal_nine_tenths
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:21:22.339059+00:00
-- url     : https://prove2.me/submissions/9f223de6-966d-497d-a5d1-5d175e8b0eb8

import Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_partial_fraction
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Complex Metric Set

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      (9 / 10 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        C * Real.log ((q : ℝ) * (|s.im| + 2)) := by
  obtain ⟨A,hA,hmain⟩ := SWPort.Davenport.logDeriv_LFunction_partial_fraction
  refine ⟨51*A, by positivity, ?_⟩
  intro q inst χ hχ s hs hs'
  obtain ⟨Z,hZ,hcount,hlocal⟩ := hmain q χ hχ s.im
  have hzfree (w : ℂ) (hw : (0.8749570698 : ℝ) < w.re) :
      DirichletCharacter.LFunction χ w ≠ 0 :=
    TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ hw (fun h => hχ h.1)
  have hmem : s ∈ closedBall (2+(s.im:ℂ)*I) (7/5) := by
    rw [mem_closedBall, dist_eq_norm]
    have eq : s-(2+(s.im:ℂ)*I) = ((s.re - 2:ℝ):ℂ) := by
      apply Complex.ext <;> simp
    rw [eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hs')]
    linarith
  have hloc := hlocal s hmem (hzfree s (by linarith))
  let m (w : ℂ) := analyticOrderNatAt (DirichletCharacter.LFunction χ) w
  have hterm (w : ℂ) (hw : w ∈ Z) : ‖(m w : ℂ) / (s-w)‖ ≤ 50 * (m w : ℝ) := by
    have hw' : w ∈ (Z : Set ℂ) := hw
    rw [hZ] at hw'
    have hwre : w.re ≤ (0.8749570698 : ℝ) := by
      by_contra! he
      exact hzfree w he hw'.2
    have sep : 1 / 50 ≤ ‖s-w‖ := by
      have hre := (le_abs_self (s-w).re).trans (Complex.abs_re_le_norm (s-w))
      rw [Complex.sub_re] at hre
      linarith
    have pos : 0 < ‖s-w‖ := by linarith
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ pos]
    have h1 : 1 ≤ 50*‖s-w‖ := by linarith
    calc
      _ ≤ (m w : ℝ) * (50*‖s-w‖) := by
        simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (m w) (α := ℝ))
      _ = _ := by ring
  have hsum : ‖∑ w ∈ Z, (m w : ℂ) / (s-w)‖ ≤
      50 * (A * Real.log ((q:ℝ) * (|s.im|+2))) := by
    calc
      _ ≤ ∑ w ∈ Z, ‖(m w : ℂ) / (s-w)‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ Z, 50 * (m w : ℝ) := Finset.sum_le_sum hterm
      _ = 50 * ∑ w ∈ Z, (m w : ℝ) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by norm_num)
  have triangle' := norm_add_le
      (logDeriv (DirichletCharacter.LFunction χ) s - ∑ w ∈ Z, (m w : ℂ) / (s-w))
      (∑ w ∈ Z, (m w : ℂ) / (s-w))
  rw [sub_add_cancel] at triangle'
  change ‖logDeriv (DirichletCharacter.LFunction χ) s - ∑ w ∈ Z, (m w : ℂ)/(s-w)‖ ≤ _ at hloc
  linarith only [triangle', hloc, hsum]
