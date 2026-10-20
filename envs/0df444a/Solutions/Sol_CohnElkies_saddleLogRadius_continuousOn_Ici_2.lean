-- Prove2me | solution 2 for CohnElkies.saddleLogRadius_continuousOn_Ici
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:39:48.062311+00:00
-- url     : https://prove2.me/submissions/b4496cca-26ed-450f-94b8-e828f00b8eb5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
theorem h47_sdg_cont : ContinuousOn CohnElkies.saddleDigamma (Set.Ioi (0 : ℝ)) := by
  open CohnElkies Set in
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -m := by
    intro z hz m h; rw [h] at hz; simp at hz <;> linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hEq : EqOn saddleDigamma (fun x : ℝ => (deriv Complex.Gamma (x:ℂ)).re / Real.Gamma x) (Ioi 0) := by
    intro x hx
    have hx' : (0:ℝ) < (x:ℂ).re := by simpa using hx
    have h1 := (Complex.differentiableAt_Gamma _ (hne _ hx')).hasDerivAt.real_of_complex
    have h2 : HasDerivAt Real.Gamma (deriv Complex.Gamma (x:ℂ)).re x := by
      convert h1 using 1; funext y; rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    have h3 := h2.log (Real.Gamma_pos_of_pos hx).ne'
    unfold saddleDigamma
    exact h3.deriv
  refine ContinuousOn.congr ?_ hEq
  refine ContinuousOn.div ?_ Real.differentiableOn_Gamma_Ioi.continuousOn
    (fun x hx => (Real.Gamma_pos_of_pos hx).ne')
  refine Complex.continuous_re.comp_continuousOn
    ((hd.deriv hU).continuousOn.comp Complex.continuous_ofReal.continuousOn ?_)
  intro x hx; simpa using hx

theorem h47_slr_cont {ε : ℝ} (hε : 0 < ε)
    (horder : CohnElkies.shortCutoff ε ≤ CohnElkies.shortEndpoint ε)
    {d : ℕ} (hd : 0 < d) {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ContinuousOn (CohnElkies.saddleLogRadius ε d) (Set.Ici u₀) := by
  open CohnElkies in
  have hc : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  set c := shortCutoff ε
  set E := shortEndpoint ε
  have hdens : Continuous (fun a : ℝ => shortShellDensity ε (max a c)) := by
    unfold shortShellDensity shortMargin
    have hm : Continuous (fun a : ℝ => max a c) := continuous_id.max continuous_const
    refine Continuous.neg (Continuous.div ?_ ?_ ?_)
    · exact (continuous_const.sub (continuous_const.mul (continuous_const.add hm))).mul
        (Real.continuous_exp.comp (continuous_const.mul hm))
    · exact (continuous_const.mul (hm.pow 2)).mul (Real.continuous_cosh.comp hm)
    · intro a
      have h1 : 0 < max a c := lt_of_lt_of_le hc (le_max_right _ _)
      have := Real.cosh_pos (max a c)
      positivity
  have hI1 : Continuous (fun u : ℝ => ∫ a in c..E, shortShellDensity ε a * a * Real.sinh (u * a)) := by
    have hcont : Continuous (fun u : ℝ => ∫ a in c..E,
        shortShellDensity ε (max a c) * (max a c) * Real.sinh (u * max a c)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact ((hdens.comp continuous_snd).mul (continuous_snd.max continuous_const)).mul
        (Real.continuous_sinh.comp (continuous_fst.mul (continuous_snd.max continuous_const)))
    refine hcont.congr fun u => ?_
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le horder] at ha
    simp only [max_eq_left ha.1]
  have hpd : Continuous (fun a : ℝ => positiveShellDensity ε a) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have hI2 : Continuous (fun u : ℝ => ∫ a in shellLocation ε..shellLocation ε + 1,
      positiveShellDensity ε a * a * Real.sinh (u * a)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((hpd.comp continuous_snd).mul continuous_snd).mul
      (Real.continuous_sinh.comp (continuous_fst.mul continuous_snd))
  have hdg : ContinuousOn (fun u : ℝ => saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2)) (Set.Ici u₀) := by
    refine h47_sdg_cont.comp (by fun_prop : Continuous fun u : ℝ => ((d : ℝ) / 2) * (1 + u) / 2).continuousOn ?_
    intro u hu
    simp only [Set.mem_Ici] at hu
    simp only [Set.mem_Ioi]
    have : (0:ℝ) < d := by exact_mod_cast hd
    have : 0 < 1 + u := by linarith
    positivity
  unfold saddleLogRadius
  exact ((continuousOn_const.add (hdg.div_const 2)).add hI1.continuousOn).add hI2.continuousOn

theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ContinuousOn (saddleLogRadius ε d) (Ici u₀) := by
  exact h47_slr_cont hε horder hd hu₀

