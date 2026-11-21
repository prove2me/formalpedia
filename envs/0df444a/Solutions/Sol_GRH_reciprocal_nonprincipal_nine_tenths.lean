-- Prove2me | solution 1 for GRH.reciprocal_nonprincipal_nine_tenths
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:23:04.575189+00:00
-- url     : https://prove2.me/submissions/cf6b857b-ff3c-4ada-97f7-1691ca6d95c4

import Theorems.Thm_GRH_logDeriv_nonprincipal_nine_tenths
import Theorems.Thm_Helfgott_LFunction_contour_growth_inputs
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Complex Set

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ s : ℂ, (9/10:ℝ) ≤ s.re → s.re ≤ 2 →
      ‖(χ.LFunction s)⁻¹‖ ≤ C * (1+|s.im|)^M := by
  obtain ⟨A,hA,hlog⟩ := GRH.logDeriv_nonprincipal_nine_tenths
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨2 * (2*(q:ℝ))^(2*A), 2*A, by positivity, by positivity, ?_⟩
  intro s hs hs'
  let center : ℂ := 2 + (s.im : ℂ) * I
  let point (x : ℝ) : ℂ := center - x
  let f (x : ℝ) : ℂ := (χ.LFunction (point x))⁻¹
  let df (x : ℝ) := logDeriv χ.LFunction (point x) * f x
  let b := 2 - s.re
  let H := (q : ℝ) * (|s.im|+2)
  let K := A * Real.log H
  have hH : 1 ≤ H := by dsimp [H]; nlinarith [abs_nonneg s.im, mul_nonneg (show 0 ≤ (q:ℝ)-1 by linarith) (abs_nonneg s.im)]
  have hHpos := zero_lt_one.trans_le hH
  have hK : 0 ≤ K := mul_nonneg hA.le (Real.log_nonneg hH)
  have hb : 0 ≤ b := sub_nonneg.mpr hs'
  have re (x : ℝ) : (point x).re = 2-x := by simp [point,center]
  have im (x : ℝ) : (point x).im = s.im := by simp [point,center]
  have inStrip {x : ℝ} (hx : x ∈ Icc 0 b) : (9/10:ℝ) ≤ (point x).re ∧ (point x).re ≤ 2 := by
    rw [re]; dsimp [b] at hx; obtain ⟨hx,hx'⟩ := hx; constructor <;> linarith
  have hnz {x : ℝ} (hx : x ∈ Icc 0 b) : χ.LFunction (point x) ≠ 0 :=
    TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ (by linarith [(inStrip hx).1]) (fun h => hχ h.1)
  have deriv_f {x : ℝ} (hx : x ∈ Icc 0 b) : HasDerivAt f (df x) x := by
    have hl := (χ.differentiableAt_LFunction (point x) (Or.inr hχ)).hasDerivAt
    have hp : HasDerivAt (fun y : ℂ => center-y) (-1) (x:ℂ) := by
      simpa using (hasDerivAt_id (x:ℂ)).const_sub center
    have hx' := ((hl.inv (hnz hx)).comp (x:ℂ) hp).comp_ofReal
    change HasDerivAt (fun y : ℝ => (χ.LFunction (point y))⁻¹)
      (deriv χ.LFunction (point x) / χ.LFunction (point x) * (χ.LFunction (point x))⁻¹) x
    convert hx' using 1
    · funext y; rfl
    · field_simp [hnz hx]
  have hinit : ‖f 0‖ ≤ 2 := by
    have key := (Helfgott.LFunction_contour_growth_inputs q χ 0 2).1 center (by simp [center])
    change ‖(χ.LFunction (center - (0:ℝ)))⁻¹‖ ≤ 2
    simp only [ofReal_zero, sub_zero, norm_inv]
    exact (inv_le_iff_one_le_mul₀ (by linarith : 0 < ‖χ.LFunction center‖)).mpr (by linarith)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := df)
    (δ := 2) (K := K) (ε := 0) (a := 0) (b := b)
    (fun x hx => (deriv_f hx).continuousAt.continuousWithinAt)
    (fun x hx => (deriv_f ⟨hx.1,hx.2.le⟩).hasDerivWithinAt) hinit
    (fun x hx => by
      rw [add_zero]; dsimp only [df]; rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      obtain ⟨hsx,hsx'⟩ := inStrip ⟨hx.1,hx.2.le⟩
      simpa only [im] using hlog q χ hχ (point x) hsx hsx')
    b ⟨hb,le_rfl⟩
  have hpoint : point b = s := by
    apply Complex.ext <;> simp [point,b,center]
  simp only [f,hpoint,sub_zero,gronwallBound_ε0] at hgr
  have hpow : Real.exp (K*b) ≤ H^(2*A) := by
    rw [Real.rpow_def_of_pos hHpos]
    apply Real.exp_le_exp.mpr
    have hb2 : b ≤ 2 := by dsimp [b]; linarith
    calc
      K * b ≤ K*2 := by gcongr
      _ = _ := by dsimp [K]; ring
  have hsH : H ≤ 2*(q:ℝ)*(1+|s.im|) := by
    dsimp [H]; nlinarith [mul_nonneg (Nat.cast_nonneg q (α := ℝ)) (abs_nonneg s.im)]
  calc
    _ ≤ 2 * H^(2*A) := hgr.trans (by gcongr)
    _ ≤ 2 * (2*(q:ℝ)*(1+|s.im|))^(2*A) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hHpos.le hsH (by positivity)) zero_le_two
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
