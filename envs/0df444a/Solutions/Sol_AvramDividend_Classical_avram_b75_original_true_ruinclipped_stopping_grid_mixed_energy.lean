-- Prove2me | solution 1 for AvramDividend.Classical.avram_b75_original_true_ruinclipped_stopping_grid_mixed_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:57:20.186943+00:00
-- url     : https://prove2.me/submissions/cc2b24c7-74a6-48a2-8c41-d5694c432de5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b61_original_compact_mixed_source_uniform_expected_square_energy
import Theorems.Thm_AvramDividend_Classical_avram_b68_original_preexit_stopped_mixed_energy_from_source
import Theorems.Thm_AvramDividend_Classical_avram_b72_original_true_ruinclock_strict_interior_source_envelope
import Theorems.Thm_AvramDividend_Classical_avram_b70_original_bounded_physical_duration_square_energy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original true ruin-clipped strict interior source cells inherit the mixed energy estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d : ℝ)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 * (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
  have hPrem (ω : Ω) (i : ℕ) (hi : i ∈ S) :=
    avram_b72_original_true_ruinclock_strict_interior_source_envelope
      X x C D hD n ρ hρbound hρclip κ hκexact k S s t
      hInterior ω i hi
  have hCell (ω : Ω) (i : ℕ) (hi : i ∈ S) :
      s i ω ≤ t i ω ∧ t i ω ≤ (n : ℝ≥0) :=
    (hPrem ω i hi).1
  have hLower (ω : Ω) (i : ℕ) (hi : i ∈ S) :
      -x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω :=
    (hPrem ω i hi).2.1
  have hBeforeUp (ω : Ω) (i : ℕ) (hi : i ∈ S) :
      (s i ω : ℝ≥0∞) <
          twoSidedExitUpTime X ((k : ℝ) + 1) ω ∧
      (t i ω : ℝ≥0∞) <
          twoSidedExitUpTime X ((k : ℝ) + 1) ω :=
    (hPrem ω i hi).2.2
  have hxb : 0 ≤ x + ((k : ℝ) + 1) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hPair :=
    avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
      X S s t hsStop htStop (fun ω i hi => (hCell ω i hi).1)
  have hEmeas : Measurable (fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2) :=
    hPair.1
  have hDurationMeas : AEStronglyMeasurable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P :=
    hPair.2.aestronglyMeasurable
  have hDI : Integrable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P :=
    avram_b70_original_bounded_physical_duration_square_energy_integrable
      X (n : ℝ≥0) S s t hDurationMeas
      (fun ω i hi => (hCell ω i hi).2)
  exact avram_b68_original_preexit_stopped_mixed_energy_from_source
    X hFinite (n : ℝ≥0) S s t V J x ((k : ℝ) + 1) d
    hxb hCell hLower hBeforeUp hJsub hJmeas hJdom
    hNoJump hEmeas hGI hDI
