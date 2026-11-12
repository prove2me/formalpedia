-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja24_original_marked_strip_second_moment_of_L2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:52:30.106949+00:00
-- url     : https://prove2.me/submissions/46cadd39-c9b7-410d-8158-05f8585092b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja27_original_bounded_mark_strip_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The literal real jump mark has absolute value at most one on the cutoff strip. -/
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
  dsimp
  intro hInt
  have hDen : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hLow : -(1 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ hDen).2 (by linarith)
    linarith
  have hUp : -(1 / ((m : ℝ) + 1)) ≤ (0 : ℝ) := by
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hd : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) :=
      div_nonneg (by norm_num) hm.le
    linarith
  have hBound :
      ∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |z| ≤ 1 := by
    intro z hz
    apply abs_le.mpr
    constructor
    · exact le_trans hLow (le_of_lt hz.1)
    · linarith [hz.2]
  exact
    (avram_ja27_original_bounded_mark_strip_isometry
      X hX hFinite n m hnm (fun z : ℝ => z)
      measurable_id hBound t) hInt
