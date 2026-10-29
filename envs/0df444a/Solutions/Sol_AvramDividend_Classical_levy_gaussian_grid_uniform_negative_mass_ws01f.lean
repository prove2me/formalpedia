-- Prove2me | solution 1 for AvramDividend.Classical.levy_gaussian_grid_uniform_negative_mass_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:17:03.806561+00:00
-- url     : https://prove2.me/submissions/ec91125b-81cd-4db9-8b54-256ca3770a57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_gaussian_grid_exponential_moment_tendsto_ws01f
import Theorems.Thm_AvramDividend_Classical_three_mgf_limits_force_uniform_negative_tail_ws01f

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (hm : 0 < m) (C : ℝ)
    (t : ℕ → ℝ≥0)
    (ht : ∀ n : ℕ,
      (t n : ℝ) = 1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2))
    (hgap :
      (m : ℝ) ^ 2 *
          (Real.exp ((X.σ ^ 2 / 2) / ((m : ℝ) ^ 2)) - 1) +
        (Real.exp (4 * (X.σ ^ 2 / 2)) - 1) / (m : ℝ) <
          Real.exp (X.σ ^ 2 / 2) - 1) :
    ∃ p : ℝ, 0 < p ∧ ∃ N : ℕ, ∀ n ≥ N,
      p ≤ P.real {ω | X.X (t n) ω < C * (t n : ℝ)} := by
  haveI := X.isProbability
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set Y : ℕ → Ω → ℝ := fun n ω => ((m : ℕ) : ℝ) * ((n : ℝ) + 1) * (X.X (t n) ω - C * (t n : ℝ)) with hYdef
  have hXm : ∀ s, Measurable (X.X s) := fun s =>
    (X.adapted s).mono (𝓕.le s) le_rfl
  -- integrability of exp (a * (X - C t)) for a ≥ 0
  have hint : ∀ (n : ℕ) (a : ℝ), 0 ≤ a →
      Integrable (fun ω => Real.exp (a * (X.X (t n) ω - C * (t n : ℝ)))) P := by
    intro n a ha
    have := ((X.laplace (t n) a ha).1).mul_const (Real.exp (-(a * (C * (t n : ℝ)))))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  have hpos : ∀ n : ℕ, (0:ℝ) ≤ (m : ℝ) * ((n : ℝ) + 1) := fun n => by positivity
  have hY : ∀ n, Measurable (Y n) := fun n =>
    measurable_const.mul ((hXm _).sub measurable_const)
  have h1 : ∀ n, Integrable (fun ω => Real.exp (Y n ω)) P := fun n => hint n _ (hpos n)
  have eY1 : ∀ n ω, Y n ω / (m : ℝ) = ((1 : ℕ) : ℝ) * ((n : ℝ) + 1) * (X.X (t n) ω - C * (t n : ℝ)) := by
    intro n ω; simp only [hYdef]; field_simp; push_cast; ring
  have eY2 : ∀ n ω, 2 * Y n ω = ((2 * m : ℕ) : ℝ) * ((n : ℝ) + 1) * (X.X (t n) ω - C * (t n : ℝ)) := by
    intro n ω; simp only [hYdef]; push_cast; ring
  have hs : ∀ n, Integrable (fun ω => Real.exp (Y n ω / (m : ℝ))) P := fun n => by
    simp_rw [eY1]; exact hint n _ (by positivity)
  have h2 : ∀ n, Integrable (fun ω => Real.exp (2 * Y n ω)) P := fun n => by
    simp_rw [eY2]; exact hint n _ (by positivity)
  have hsub : ∀ (f : Ω → ℝ), Integrable f P → ∫ ω, (f ω - 1) ∂P = ∫ ω, f ω ∂P - 1 := by
    intro f hf
    rw [integral_sub hf (integrable_const _)]; simp
  have L := fun k (hk : 0 < k) =>
    AvramDividend.Classical.levy_gaussian_grid_exponential_moment_tendsto_ws01f X m k hm hk C t ht
  have ha : Tendsto (fun n : ℕ => ∫ ω, (Real.exp (Y n ω) - 1) ∂P) atTop
      (nhds (Real.exp (X.σ ^ 2 / 2) - 1)) := by
    simp_rw [fun n => hsub _ (h1 n)]
    have := (L m hm).sub_const 1
    rwa [div_self hm'.ne', one_pow, mul_one] at this
  have hb : Tendsto (fun n : ℕ => ∫ ω, (Real.exp (Y n ω / (m : ℝ)) - 1) ∂P) atTop
      (nhds (Real.exp ((X.σ ^ 2 / 2) / ((m : ℝ) ^ 2)) - 1)) := by
    simp_rw [fun n => hsub _ (hs n), eY1]
    have := (L 1 one_pos).sub_const 1
    convert this using 3
    push_cast; field_simp
  have hc : Tendsto (fun n : ℕ => ∫ ω, (Real.exp (2 * Y n ω) - 1) ∂P) atTop
      (nhds (Real.exp (4 * (X.σ ^ 2 / 2)) - 1)) := by
    simp_rw [fun n => hsub _ (h2 n), eY2]
    have := (L (2 * m) (by omega)).sub_const 1
    convert this using 3
    push_cast; field_simp; ring_nf
  obtain ⟨p, hp, N, hN⟩ :=
    AvramDividend.Classical.three_mgf_limits_force_uniform_negative_tail_ws01f Y (m : ℝ)
      (by exact_mod_cast hm) hY h1 hs h2 _ _ _ ha hb hc hgap
  refine ⟨p, hp, N, fun n hn => ?_⟩
  convert hN n hn using 2
  ext ω
  simp only [mem_setOf_eq, hYdef]
  have hc : (0:ℝ) < (m : ℝ) * ((n : ℝ) + 1) := by positivity
  constructor
  · intro h; exact mul_neg_of_pos_of_neg hc (by linarith)
  · intro h
    by_contra h'
    push_neg at h'
    nlinarith [mul_nonneg hc.le (sub_nonneg.2 h')]
