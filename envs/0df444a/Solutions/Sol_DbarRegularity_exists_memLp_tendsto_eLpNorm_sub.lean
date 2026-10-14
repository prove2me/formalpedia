-- Prove2me | solution 1 for DbarRegularity.exists_memLp_tendsto_eLpNorm_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:18:21.427263+00:00
-- url     : https://prove2.me/submissions/8d723fbb-f734-44e6-bd06-78e53f118196

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Cauchy



namespace DbarRegularity

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Completeness of `L^p` along `ε → 0⁺`: a family `u ε ∈ L^p` (`ε > 0`) which is Cauchy in
`L^p` as `ε → 0⁺` converges in `L^p` to some `g ∈ L^p`. -/
theorem exists_memLp_tendsto_eLpNorm_sub {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : ℝ → α → E)
    (hu : ∀ ε : ℝ, 0 < ε → MemLp (u ε) p μ)
    (hc : ∀ δ : ℝ, 0 < δ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ε η : ℝ, 0 < ε → ε < η₀ → 0 < η → η < η₀ →
      eLpNorm (u ε - u η) p μ ≤ ENNReal.ofReal δ) :
    ∃ g : α → E, MemLp g p μ ∧
      Tendsto (fun ε : ℝ => eLpNorm (u ε - g) p μ) (𝓝[>] 0) (𝓝 0) := by
  classical
  let v : ℝ → Lp E p μ := fun ε => if h : 0 < ε then (hu ε h).toLp (u ε) else 0
  have hv : ∀ ε (h : 0 < ε), v ε = (hu ε h).toLp (u ε) := fun ε h => dif_pos h
  have hdist : ∀ ε η, 0 < ε → 0 < η → edist (v ε) (v η) = eLpNorm (u ε - u η) p μ := by
    intro ε η hε hη
    rw [hv ε hε, hv η hη, Lp.edist_def]
    exact eLpNorm_congr_ae (((hu ε hε).coeFn_toLp).sub (hu η hη).coeFn_toLp)
  have hcauchy : Cauchy (map v (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun δ hδ => ?_⟩
    obtain ⟨η₀, hη₀, h⟩ := hc (δ / 2) (half_pos hδ)
    refine ⟨v '' Ioo 0 η₀, image_mem_map (Ioo_mem_nhdsGT hη₀), ?_⟩
    rintro _ ⟨ε, ⟨hε0, hε1⟩, rfl⟩ _ ⟨η, ⟨hη0, hη1⟩, rfl⟩
    rw [dist_edist, hdist ε η hε0 hη0]
    have h1 := h ε η hε0 hε1 hη0 hη1
    have h2 : eLpNorm (u ε - u η) p μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    calc (eLpNorm (u ε - u η) p μ).toReal ≤ δ / 2 := by
          rw [← ENNReal.toReal_ofReal (half_pos hδ).le]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ < δ := half_lt_self hδ
  obtain ⟨G, hG⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  refine ⟨G, Lp.memLp G, ?_⟩
  have h1 := (tendsto_iff_edist_tendsto_0.1 hG)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hv ε hε, Lp.edist_def]
  exact eLpNorm_congr_ae (((hu ε hε).coeFn_toLp).sub (EventuallyEq.refl _ _))

end DbarRegularity

open DbarRegularity

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem solution {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : ℝ → α → E)
    (hu : ∀ ε : ℝ, 0 < ε → MemLp (u ε) p μ)
    (hc : ∀ δ : ℝ, 0 < δ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ε η : ℝ, 0 < ε → ε < η₀ → 0 < η → η < η₀ →
      eLpNorm (u ε - u η) p μ ≤ ENNReal.ofReal δ) :
    ∃ g : α → E, MemLp g p μ ∧
      Tendsto (fun ε : ℝ => eLpNorm (u ε - g) p μ) (𝓝[>] 0) (𝓝 0) :=
  DbarRegularity.exists_memLp_tendsto_eLpNorm_sub u hu hc
