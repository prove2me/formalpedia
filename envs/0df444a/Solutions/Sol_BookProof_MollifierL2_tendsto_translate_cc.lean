-- Prove2me | solution 1 for BookProof.MollifierL2.tendsto_translate_cc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:05:29.84831+00:00
-- url     : https://prove2.me/submissions/086f3207-58db-431d-916b-519223c6af5c

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.tendsto_translate_cc
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2




open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1000000 in
theorem solution {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {g : E → F}
    (hg : Continuous g) (hcs : HasCompactSupport g) :
    Tendsto (fun a : E => eLpNorm (fun x => g (x - a) - g x) p μ) (𝓝 0) (𝓝 0) := by

  classical
  set K : Set E := (tsupport g) + Metric.closedBall (0 : E) 1 with hK
  have hKc : IsCompact K := hcs.isCompact.add (isCompact_closedBall (0 : E) 1)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hμK : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  set M : ℝ≥0∞ := μ K ^ (1 / p.toReal) with hM
  have hMne : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hμK
  have huc : UniformContinuous g := hcs.uniformContinuous_of_continuous hg
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hM1 : M + 1 ≠ 0 := by positivity
  have hM1top : M + 1 ≠ ⊤ := by simp [hMne]
  set r : ℝ≥0∞ := ε / (M + 1) with hr
  have hrpos : r ≠ 0 := by simp [hr, hε.ne', hM1top]
  have hrtop : r ≠ ⊤ := by
    rw [hr, Ne, ENNReal.div_eq_top]
    push_neg
    exact ⟨fun _ h => absurd h hM1, fun h => absurd h hεtop⟩
  have hrmul : r * (M + 1) = ε := ENNReal.div_mul_cancel hM1 hM1top
  set c : ℝ := r.toReal with hc
  have hc0 : 0 < c := ENNReal.toReal_pos hrpos hrtop
  have hcof : ENNReal.ofReal c = r := ENNReal.ofReal_toReal hrtop
  have hcle : ENNReal.ofReal c * M ≤ ε := by
    rw [hcof, ← hrmul]
    gcongr
    exact le_self_add
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp huc c hc0
  have hunif : ∀ᶠ a : E in 𝓝 (0 : E), ∀ x : E, ‖g (x - a) - g x‖ ≤ c := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hδ0] with a ha x
    have hd : dist (x - a) x < δ := by
      simpa [dist_eq_norm, Metric.mem_ball, sub_sub_cancel_left] using ha
    have hgd := hδ hd
    rw [dist_eq_norm] at hgd
    exact hgd.le
  filter_upwards [hunif, Metric.closedBall_mem_nhds (0 : E) one_pos] with a ha hball
  have hsupp : ∀ x : E, ‖g (x - a) - g x‖ ≤ ‖K.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      simpa [Real.norm_eq_abs, abs_of_pos hc0] using ha x
    · have h1 : g x = 0 := by
        have hnm : x ∉ tsupport g := by
          intro hmem
          exact hx ⟨x, hmem, 0, by simp, by simp⟩
        exact image_eq_zero_of_notMem_tsupport hnm
      have h2 : g (x - a) = 0 := by
        have hnm : x - a ∉ tsupport g := by
          intro hmem
          refine hx ⟨x - a, hmem, a, ?_, by abel⟩
          simpa [Metric.mem_closedBall, dist_eq_norm] using hball
        exact image_eq_zero_of_notMem_tsupport hnm
      simp [h1, h2]
  calc eLpNorm (fun x => g (x - a) - g x) p μ
      ≤ eLpNorm (K.indicator (fun _ => c)) p μ := eLpNorm_mono hsupp
    _ = ‖c‖ₑ * μ K ^ (1 / p.toReal) := eLpNorm_indicator_const hKm hp0 hp
    _ ≤ ε := by
        have hcc : ‖c‖ₑ = ENNReal.ofReal c := by
          simp [Real.enorm_eq_ofReal_abs, abs_of_pos hc0]
        rw [hcc, ← hM]
        exact hcle
