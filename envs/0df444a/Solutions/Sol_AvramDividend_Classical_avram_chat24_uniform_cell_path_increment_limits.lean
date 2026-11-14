-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_cell_path_increment_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:10:19.951207+00:00
-- url     : https://prove2.me/submissions/28bbb8a9-0818-4041-ac85-89721c51c0f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_approach_left
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_mesh_cell_geometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem solution
    (f P : ℝ≥0 → ℝ) (d y : ℝ) (B t : ℝ≥0)
    (hB : 0 < B) (ht : 0 < t) (k : ℕ → ℕ)
    (hk : ∀ n, k n ∈ Finset.range (n + 1))
    (hcell : ∀ n,
      B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((k n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))
    (hfr : ContinuousWithinAt f (Ici t) t)
    (hfl : ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hP : Tendsto P (𝓝[<] t) (nhds y)) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    Tendsto (fun n => u n (k n + 1)) atTop (𝓝[≥] t) ∧
      Tendsto h atTop (nhds 0) ∧
      Tendsto (fun n => P (u n (k n))) atTop (nhds y) ∧
      Tendsto (fun n => d * h n - (f (u n (k n + 1)) - f (u n (k n))))
        atTop (nhds (Function.leftLim f t - f t)) := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
  change Tendsto (fun n => u n (k n + 1)) atTop (𝓝[≥] t) ∧
    Tendsto h atTop (nhds 0) ∧
    Tendsto (fun n => P (u n (k n))) atTop (nhds y) ∧
    Tendsto (fun n => d * h n - (f (u n (k n + 1)) - f (u n (k n))))
      atTop (nhds (Function.leftLim f t - f t))
  have hl := AvramDividend.Classical.avram_chat24_uniform_cell_approach_left B t k hcell
  have hh : Tendsto h atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ => (B : ℝ)) atTop (nhds (B : ℝ)) :=
      tendsto_const_nhds
    simpa [h, div_eq_mul_inv] using hc.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hlr : Tendsto (fun n => (u n (k n) : ℝ)) atTop (nhds (t : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hl.mono_right nhdsWithin_le_nhds)
  have heq : (fun n => (u n (k n) : ℝ) + h n) =
      (fun n => (u n (k n + 1) : ℝ)) := by
    funext n
    have hg := (AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry B hB).2.2
      n (k n) (hk n)
    change u n (k n) ≤ B ∧ u n (k n + 1) ≤ B ∧
      (u n (k n + 1) : ℝ) - (u n (k n) : ℝ) = h n at hg
    linarith [hg.2.2]
  have hr : Tendsto (fun n => (u n (k n + 1) : ℝ)) atTop (nhds (t : ℝ)) := by
    rw [← heq]
    simpa only [add_zero] using hlr.add hh
  have hu : Tendsto (fun n => u n (k n + 1)) atTop (𝓝[≥] t) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_subtype_rng.2 hr, Filter.Eventually.of_forall (fun n => (hcell n).2)⟩
  refine ⟨hu, hh, hP.comp hl, ?_⟩
  have hlf := (tendsto_leftLim_of_tendsto hfl).comp hl
  have hrf := hfr.tendsto.comp hu
  have hd : Tendsto (fun _ : ℕ => d) atTop (nhds d) := tendsto_const_nhds
  have hvalue : d * (0 : ℝ) - (f t - Function.leftLim f t) =
      Function.leftLim f t - f t := by ring
  rw [← hvalue]
  exact (hd.mul hh).sub (hrf.sub hlf)
