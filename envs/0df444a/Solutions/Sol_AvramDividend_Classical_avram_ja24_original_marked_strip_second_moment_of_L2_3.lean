-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja24_original_marked_strip_second_moment_of_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:20:58.396908+00:00
-- url     : https://prove2.me/submissions/83600ef4-2545-4e1b-bcd5-9e6ff272d84a

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_borel_mark_simple_energy_certificate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by
  intro n m hnm t
  let S : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let C : Ω → ℝ := fun ω =>
    (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
      (t : ℝ) * (∫ z in S, z ∂X.ν)
  let e : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  change Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) = e
  intro _
  obtain ⟨K, B, c, g, hSets, hDisj, hMeas, hG, hDom, hLim, hE, hEt⟩ :=
    (avram_ja28_original_borel_mark_simple_energy_certificate
      X hX hFinite n m hnm t)
  let F : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range (K k),
      c k i * ((NX ω (Ioc 0 t ×ˢ B k i)).toReal -
        (((t : ℝ≥0∞) * X.ν (B k i)).toReal))
  let E : ℕ → ℝ := fun k =>
    ∑ i ∈ Finset.range (K k),
      (c k i) ^ 2 * (((t : ℝ≥0∞) * X.ν (B k i)).toReal)
  have hConv : Tendsto
      (fun k => ∫ ω, (F k ω) ^ 2 ∂P)
      atTop (𝓝 (∫ ω, (C ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_dominated_convergence g
    · simpa only [F] using hMeas
    · exact hG
    · simpa only [F] using hDom
    · simpa only [F, C] using hLim
  have hEnergy : (fun k => ∫ ω, (F k ω) ^ 2 ∂P) = E := by
    funext k
    simpa only [F, E] using hE k
  rw [hEnergy] at hConv
  exact tendsto_nhds_unique hConv (by simpa only [E, e] using hEt)
