-- Prove2me | solution 1 for AvramDividend.Classical.atomless_stieltjes_measure_above_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:18:07.623976+00:00
-- url     : https://prove2.me/submissions/97cf37ce-9052-48c9-83d3-119e23557861

import Mathlib
import Theorems.Thm_AvramDividend_Classical_atomless_stieltjes_measure_of_antitone_continuous_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    (g : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, a ≤ x → μ.real (Ici x) = g x) := by
  let G : ℝ → ℝ := fun x => g (max x a)
  have hmax : Continuous (fun x : ℝ => max x a) :=
    continuous_id.max continuous_const
  have hGcont : Continuous G := by
    exact hcont.comp_continuous hmax (fun x =>
      lt_of_lt_of_le ha (le_max_right x a))
  have hGanti : Antitone G := by
    intro x y hxy
    exact hanti
      (lt_of_lt_of_le ha (le_max_right x a))
      (lt_of_lt_of_le ha (le_max_right y a))
      (max_le_max hxy le_rfl)
  have hGnonneg : ∀ x : ℝ, 0 ≤ G x := by
    intro x
    exact hnonneg _ (lt_of_lt_of_le ha (le_max_right x a))
  have hevent : G =ᶠ[atTop] g := by
    filter_upwards [eventually_ge_atTop a] with x hx
    simp [G, max_eq_left hx]
  have hGlim : Tendsto G atTop (𝓝 (0 : ℝ)) :=
    hlim.congr' hevent.symm
  obtain ⟨μ, hnull, hfinite, htail⟩ :=
    atomless_stieltjes_measure_of_antitone_continuous_tail
      G hGcont hGanti hGnonneg hGlim
  refine ⟨μ, hnull, hfinite, ?_⟩
  intro x hx
  simpa only [G, max_eq_left hx] using htail x
