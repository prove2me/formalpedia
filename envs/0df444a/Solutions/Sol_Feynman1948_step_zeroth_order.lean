-- Prove2me | solution 1 for Feynman1948.step_zeroth_order
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T21:20:07.865024+00:00
-- url     : https://prove2.me/submissions/05fd7493-dc26-4733-8537-11c84148070b

import Definitions.Def_Feynman1948_WaveEquation
import Theorems.Thm_Feynman1948_schroedinger_equation

open Complex Filter Topology SchwartzMap Feynman1948

theorem solution (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => stepEvolution ħ m V ε ψ x) (𝓝[>] 0) (𝓝 (ψ x)) := by
  have hq := schroedinger_equation ħ m hħ hm V ψ x
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).ofReal
  have ht := (hq.mul hε).add_const (ψ x)
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  field_simp [hε0]
  ring
