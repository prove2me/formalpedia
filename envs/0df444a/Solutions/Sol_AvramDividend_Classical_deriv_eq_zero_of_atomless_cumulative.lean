-- Prove2me | solution 1 for AvramDividend.Classical.deriv_eq_zero_of_atomless_cumulative
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-23T09:39:34.600954+00:00
-- url     : https://prove2.me/submissions/2c41b36d-7445-4cc8-81c6-a10967aaa922

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem solution :
    ¬ (∀ (mu : Measure ℝ) [NullSingletonClass mu]
      (g : ℝ → ℝ)
      (hfin : ∀ x : ℝ, 0 < x → mu (Ici x) ≠ ⊤)
      (hcont : ContinuousOn g (Ioi (0 : ℝ)))
      (hcum : ∀ x : ℝ, 0 < x → mu.real (Ici x) = g x),
      ∀ x : ℝ, 0 < x → deriv g x = 0) := by
  intro H
  let mu : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  letI : NullSingletonClass mu := inferInstance
  have hmass : mu univ = 1 := by
    simp [mu, Measure.restrict_apply, Real.volume_Icc]
  have hfin : ∀ x : ℝ, 0 < x → mu (Ici x) ≠ ⊤ := by
    intro x _
    have hle : mu (Ici x) ≤ (1 : ENNReal) := by
      calc
        mu (Ici x) ≤ mu univ := measure_mono (subset_univ _)
        _ = 1 := hmass
    exact (lt_of_le_of_lt hle (by norm_num : (1 : ENNReal) < ⊤)).ne
  let g : ℝ → ℝ := fun x => mu.real (Ici x)
  have hcont : ContinuousOn g (Ioi (0 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := hx
    let a : ℝ := x / 2
    have ha : 0 < a := by
      dsimp [a]
      linarith
    have hax : a < x := by
      dsimp [a]
      linarith
    have hμlt : mu (Ici a) < ⊤ :=
      lt_top_iff_ne_top.mpr (hfin a ha)
    have hint :
        IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici a) mu := by
      exact (integrableOn_const_iff).2 (Or.inr hμlt)
    have hc :
        ContinuousOn
          (fun b : ℝ => ∫ _ in Ici b, (1 : ℝ) ∂mu) (Ici a) :=
      hint.continuousOn_Ici_primitive_Ici
    have hcat :
        ContinuousAt
          (fun b : ℝ => ∫ _ in Ici b, (1 : ℝ) ∂mu) x :=
      hc.continuousAt (Ici_mem_nhds hax)
    have htail :
        ContinuousAt (fun b : ℝ => mu.real (Ici b)) x := by
      simpa only [setIntegral_one_eq_measureReal] using hcat
    exact htail.continuousWithinAt
  have hcum : ∀ x : ℝ, 0 < x → mu.real (Ici x) = g x :=
    fun _ _ => rfl
  have hnear : g =ᶠ[𝓝 (1 / 2 : ℝ)] (fun y : ℝ => 1 - y) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)] with y hy
    have hset : Ici y ∩ Icc (0 : ℝ) 1 = Icc y 1 := by
      ext z
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨hyz, ⟨_, hz1⟩⟩
        exact ⟨hyz, hz1⟩
      · rintro ⟨hyz, hz1⟩
        exact ⟨hyz, ⟨le_trans hy.1.le hyz, hz1⟩⟩
    have hm : mu (Ici y) = ENNReal.ofReal (1 - y) := by
      change (volume.restrict (Icc (0 : ℝ) 1)) (Ici y) = _
      rw [Measure.restrict_apply measurableSet_Ici, hset, Real.volume_Icc]
    change mu.real (Ici y) = 1 - y
    change (mu (Ici y)).toReal = 1 - y
    rw [hm, ENNReal.toReal_ofReal (sub_nonneg.mpr hy.2.le)]
  have hd : deriv g (1 / 2 : ℝ) = -1 := by
    rw [hnear.deriv_eq]
    exact deriv_const_sub_id (1 : ℝ)
  have hz : deriv g (1 / 2 : ℝ) = 0 :=
    H mu g hfin hcont hcum _ (by norm_num)
  rw [hd] at hz
  norm_num at hz
