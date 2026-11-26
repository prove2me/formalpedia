-- Prove2me | solution 1 for CurrentContinuousF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:50.163874+00:00
-- url     : https://prove2.me/submissions/3d870854-02f2-40b8-8afc-a370d0ec1996

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_CurrentContinuousF

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : MetricCurrent1 E)
    (f : E → ℝ) (bF : ℝ≥0) (hbF : ∀ x, |f x| ≤ (bF : ℝ)) (LF : ℝ≥0) (hLF : LipschitzWith LF f)
    (pi : E → ℝ) (Lpi : ℝ≥0) (hLpi : LipschitzWith Lpi pi)
    (fs : ℕ → E → ℝ) (bs : ℕ → ℝ≥0) (hbs : ∀ n x, |fs n x| ≤ (bs n : ℝ))
    (Ls : ℕ → ℝ≥0) (hLs : ∀ n, LipschitzWith (Ls n) (fs n))
    (b0 : ℝ≥0) (hbound : ∀ n, bs n ≤ b0)
    (hconv : ∀ x, Tendsto (fun n => fs n x) atTop (nhds (f x))) :
    Tendsto (fun n => T.toFun ⟨fs n, bs n, hbs n, Ls n, hLs n, pi, Lpi, hLpi⟩) atTop
      (nhds (T.toFun ⟨f, bF, hbF, LF, hLF, pi, Lpi, hLpi⟩)) := by
-- BODY
  have hne : Nonempty { μ : Measure E // IsAdmissible T.toFun μ } := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    exact T.finiteMass (by simp [massOfFunctional])
  obtain ⟨μ, hfin, hdom⟩ := hne.some
  have : IsFiniteMeasure μ := hfin
  set D : ℕ → Form1 E := fun n =>
    { f := fun x => fs n x - f x
      fBound := bs n + bF
      f_bounded := fun x => (abs_sub _ _).trans (by push_cast; exact add_le_add (hbs n x) (hbF x))
      fLip := Ls n + LF
      f_lipschitz := (hLs n).sub hLF
      pi := pi, piLip := Lpi, pi_lipschitz := hLpi } with hD
  have hsplit : ∀ n, T.toFun ⟨fs n, bs n, hbs n, Ls n, hLs n, pi, Lpi, hLpi⟩
      = T.toFun (D n) + T.toFun ⟨f, bF, hbF, LF, hLF, pi, Lpi, hLpi⟩ := by
    intro n
    exact T.add_f (D n) ⟨f, bF, hbF, LF, hLF, pi, Lpi, hLpi⟩
      ⟨fs n, bs n, hbs n, Ls n, hLs n, pi, Lpi, hLpi⟩ rfl rfl (fun x => by simp [hD])
  have hmeas : ∀ n, Measurable (fun x => ENNReal.ofReal |(D n).f x|) := by
    intro n
    have hc : Continuous fun x => fs n x - f x := (hLs n).continuous.sub hLF.continuous
    exact (hc.abs).measurable.ennreal_ofReal
  have hlim0 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |(D n).f x| ∂μ) atTop (nhds 0) := by
    have key := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n x => ENNReal.ofReal |(D n).f x|)
      (f := fun _ : E => (0 : ℝ≥0∞))
      (bound := fun _ : E => ENNReal.ofReal ((b0 : ℝ) + bF))
      (fun n => hmeas n)
      (by
        intro n
        filter_upwards with x
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : |(D n).f x| ≤ (bs n : ℝ) + bF := by
          show |fs n x - f x| ≤ _
          exact (abs_sub _ _).trans (add_le_add (hbs n x) (hbF x))
        have h2 : (bs n : ℝ) ≤ (b0 : ℝ) := by exact_mod_cast hbound n
        linarith)
      (by
        have hcst : ∫⁻ _ : E, ENNReal.ofReal ((b0 : ℝ) + bF) ∂μ
            = ENNReal.ofReal ((b0 : ℝ) + bF) * μ Set.univ := by
          simp [lintegral_const]
        rw [hcst]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))
      (by
        filter_upwards with x
        have h1 : Tendsto (fun n => |(D n).f x|) atTop (nhds 0) := by
          have h0 : Tendsto (fun n => fs n x - f x) atTop (nhds 0) := by
            simpa using (hconv x).sub (tendsto_const_nhds (x := f x))
          simpa using h0.abs
        have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
        simpa [Function.comp_def] using h2)
    simpa using key
  have hupper : Tendsto (fun n => (Lpi : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal |(D n).f x| ∂μ)
      atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (a := (Lpi : ℝ≥0∞)) hlim0 (Or.inr ENNReal.coe_ne_top)
    simpa using this
  have hsq : Tendsto (fun n => ENNReal.ofReal |T.toFun (D n)|) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => bot_le) (fun n => hdom (D n))
  have habs : Tendsto (fun n => |T.toFun (D n)|) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hsq
    simpa [Function.comp_def, ENNReal.toReal_ofReal, abs_nonneg] using h
  have hTD : Tendsto (fun n => T.toFun (D n)) atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)
  simp only [hsplit]
  simpa using hTD.add (tendsto_const_nhds
    (x := T.toFun ⟨f, bF, hbF, LF, hLF, pi, Lpi, hLpi⟩))
