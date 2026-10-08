-- Prove2me | solution 1 for AvramDividend.Classical.atomless_positive_tail_measure_of_antitone_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:23:54.084507+00:00
-- url     : https://prove2.me/submissions/e9240df8-546b-4e9e-9080-4a4a547e6a7d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_of_antitone_continuous_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    (g : ℝ → ℝ)
    (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → μ.real (Ici x) = g x) := by
  let f : ℝ → ℝ := fun t => g (Real.exp t)
  have hfcont : Continuous f := by
    exact hcont.comp_continuous Real.continuous_exp
      (fun t => Real.exp_pos t)
  have hfanti : Antitone f := by
    intro x y hxy
    exact hanti (Real.exp_pos x) (Real.exp_pos y)
      (Real.exp_le_exp.mpr hxy)
  have hfn : ∀ t : ℝ, 0 ≤ f t :=
    fun t => hnonneg _ (Real.exp_pos t)
  have hflim : Tendsto f atTop (𝓝 (0 : ℝ)) := by
    exact hlim.comp Real.tendsto_exp_atTop
  obtain ⟨ν, hnull, hfinite, htail⟩ :=
    atomless_stieltjes_measure_of_antitone_continuous_tail
      f hfcont hfanti hfn hflim
  letI : NullSingletonClass ν := hnull
  let μ : Measure ℝ := ν.map Real.exp
  have hmeas : Measurable Real.exp := Real.continuous_exp.measurable
  have hsingle (x : ℝ) : μ {x} = 0 := by
    change ν.map Real.exp {x} = 0
    rw [Measure.map_apply hmeas (measurableSet_singleton x)]
    have hsub : (Real.exp ⁻¹' ({x} : Set ℝ)).Subsingleton := by
      intro u hu v hv
      apply Real.exp_injective
      have hu' : Real.exp u = x := by simpa using hu
      have hv' : Real.exp v = x := by simpa using hv
      exact hu'.trans hv'.symm
    exact hsub.measure_zero ν
  have hnullμ : NullSingletonClass μ := ⟨hsingle⟩
  have htailmap (x : ℝ) (hx : 0 < x) :
      μ (Ici x) = ν (Ici (Real.log x)) := by
    change ν.map Real.exp (Ici x) = _
    rw [Measure.map_apply hmeas measurableSet_Ici]
    congr 1
    ext y
    simpa only [mem_preimage, mem_Ici] using
      (Real.log_le_iff_le_exp hx).symm
  refine ⟨μ, hnullμ, ?_, ?_⟩
  · intro x hx
    rw [htailmap x hx]
    exact hfinite (Real.log x)
  · intro x hx
    change (μ (Ici x)).toReal = g x
    rw [htailmap x hx]
    simpa only [Measure.real_def, f, Real.exp_log hx] using htail (Real.log x)
