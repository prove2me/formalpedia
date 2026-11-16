-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInfty_mono
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-15T16:10:10.846196+00:00
-- url     : https://prove2.me/submissions/db4a5e05-4440-44d7-8ace-69dd48a3e4d2

import Definitions.Def_FiniteEnergyPlane_Asymptotics



/-!
# Two facts on `ExpDecayCInfty`

Standalone copies of `nf_expDecay_congr` / `nf_expDecay_mono` (`Scratch/NF_D.lean`).
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

lemma expDecayCInfty_congr_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ × ℝ → F} {b s₀ : ℝ} (hf : ExpDecayCInfty f b)
    (h : ∀ s > s₀, ∀ t, g (s, t) = f (s, t)) : ExpDecayCInfty g b := by
  have hO : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hev : ∀ p ∈ Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ), g =ᶠ[𝓝 p] f := by
    intro p hp
    filter_upwards [hO.mem_nhds hp] with q hq
    obtain ⟨s, t⟩ := q
    exact h s hq.1 t
  obtain ⟨⟨s₁, hs₁⟩, hb⟩ := hf
  refine ⟨⟨max s₀ s₁, ?_⟩, fun m => ?_⟩
  · refine (hs₁.mono ?_).congr fun p hp => ?_
    · exact Set.prod_mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
    · obtain ⟨s, t⟩ := p
      exact h s (lt_of_le_of_lt (le_max_left _ _) hp.1) t
  · obtain ⟨C, s₂, hC⟩ := hb m
    refine ⟨C, max s₂ (s₀ + 1), fun s hs t => ?_⟩
    have hs0 : s₀ < s := by linarith [le_max_right s₂ (s₀ + 1)]
    rw [((hev (s, t) ⟨hs0, Set.mem_univ _⟩).iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hC s (le_trans (le_max_left _ _) hs) t

lemma expDecayCInfty_mono_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {b b' : ℝ} (hf : ExpDecayCInfty f b) (hbb : b' ≤ b) :
    ExpDecayCInfty f b' := by
  refine ⟨hf.1, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hf.2 m
  refine ⟨|C|, max s₁ 0, fun s hs t => ?_⟩
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  calc _ ≤ C * Real.exp (-(b * s)) := hC s (le_trans (le_max_left _ _) hs) t
    _ ≤ |C| * Real.exp (-(b * s)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (-(b' * s)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      exact Real.exp_le_exp.2 (by nlinarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {b b' : ℝ} (hf : ExpDecayCInfty f b) (hbb : b' ≤ b) :
    ExpDecayCInfty f b' :=
  expDecayCInfty_mono_aux hf hbb
