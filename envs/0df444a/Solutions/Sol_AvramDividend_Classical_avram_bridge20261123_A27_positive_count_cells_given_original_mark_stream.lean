-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A27_positive_count_cells_given_original_mark_stream
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:08:05.382112+00:00
-- url     : https://prove2.me/submissions/7ba17d9e-c70c-4eb6-a13e-8b99b6494a23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_mark_event_moment_matching
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_real_geometric_sequence_integrable_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)
    (hActualMarks :
    ∃ (Y : ℕ → Ω → ℝ) (m : ℝ),
      (∀ i, Measurable (Y i)) ∧
      (∀ k, IndepFun K
        (fun ω => ∑ i ∈ Finset.range k, Y i ω) P) ∧
      (∀ᵐ ω ∂P, J ω = ∑ i ∈ Finset.range (K ω), Y i ω) ∧
      (∀ k, (∫ ω, Real.exp
        (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) = m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν)) :
    ∃ m : ℝ,
      Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) ∧
      (∀ k : ℕ, 0 < k →
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
          (poissonMeasure r).real {k} * m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  rcases hActualMarks with ⟨Y, m, hY, hIndep, hRep, hFixed, hRate⟩
  refine ⟨m, avram_a27_poisson_real_geometric_sequence_integrable_20261117 r m, ?_, hRate⟩
  intro k hk
  have hs : MeasurableSet {ω : Ω | K ω = k} :=
    hK (measurableSet_singleton k)
  have hRepOn :
      ∀ᵐ ω ∂(P.restrict {ω : Ω | K ω = k}),
        J ω = ∑ i ∈ Finset.range (K ω), Y i ω :=
    ae_restrict_of_ae hRep
  have hLeft :
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) =
      (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * ∑ i ∈ Finset.range (K ω), Y i ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [hRepOn] with ω hω
    rw [hω]
  have hMark :=
    AvramDividend.Classical.chat06_mark_event_moment_matching
      K hK Y hY hIndep θ m hFixed k
  have hMass : P.real {ω : Ω | K ω = k} =
      (poissonMeasure r).real {k} := by
    have heq : P {ω : Ω | K ω = k} =
        (poissonMeasure r) {k} := by
      rw [show {ω : Ω | K ω = k} = K ⁻¹' {k} from rfl,
        ← Measure.map_apply hK (measurableSet_singleton k), hLaw.map_eq]
    rw [measureReal_def, heq, ← measureReal_def]
  have hConst :
      (∫ ω in {ω : Ω | K ω = k}, m ^ (K ω) ∂P) =
        (poissonMeasure r).real {k} * m ^ k := by
    calc
      (∫ ω in {ω : Ω | K ω = k}, m ^ (K ω) ∂P) =
        (∫ ω in {ω : Ω | K ω = k}, (fun _ : Ω => m ^ k) ω ∂P) := by
          apply setIntegral_congr_fun hs
          intro ω hω
          change K ω = k at hω
          simpa only using congrArg (fun j : ℕ => m ^ j) hω
      _ = (poissonMeasure r).real {k} * m ^ k := by
          simpa only [integral_const, Measure.real,
            Measure.restrict_apply_univ, smul_eq_mul] using
            congrArg (fun c : ℝ => c * m ^ k) hMass
  exact hLeft.trans (hMark.trans hConst)
