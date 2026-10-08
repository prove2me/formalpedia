-- Prove2me | solution 1 for BalkemaDeHaan.DiscreteDomain.tailEquiv_mem_Dr
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:41:20.842653+00:00
-- url     : https://prove2.me/submissions/6f336d02-c41f-4258-aec3-0bac620dfc39

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology


namespace BalkemaDeHaan.DiscreteDomain

lemma te_tail_Ioc_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (t y : ℝ) (hy : 0 ≤ y) :
    (μ (Set.Ioc t (t + y))).toReal = (μ (Set.Ioi t)).toReal - (μ (Set.Ioi (t + y))).toReal := by
  have hU : Set.Ioc t (t + y) ∪ Set.Ioi (t + y) = Set.Ioi t :=
    Set.Ioc_union_Ioi_eq_Ioi (by linarith)
  have hD : Disjoint (Set.Ioc t (t + y)) (Set.Ioi (t + y)) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd hx.2 (not_le.2 hx')
  have := measure_union hD measurableSet_Ioi (μ := μ)
  rw [hU] at this
  rw [this, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]; ring

lemma te_residualCDF_of_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (t y : ℝ) (hy : 0 ≤ y)
    (ht : 0 < μ (Set.Ioi t)) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y =
      1 - (μ (Set.Ioi (t + y))).toReal / (μ (Set.Ioi t)).toReal := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  have hpos : 0 < (μ (Set.Ioi t)).toReal := ENNReal.toReal_pos ht.ne' (measure_ne_top _ _)
  rw [te_tail_Ioc_eq μ t y hy, sub_div, div_self hpos.ne']

lemma te_residualCDF_of_neg (μ : Measure ℝ) (t y : ℝ) (hy : y < 0) :
    BalkemaDeHaan.LimitTypes.residualCDF μ t y = 0 := by
  unfold BalkemaDeHaan.LimitTypes.residualCDF
  rw [Set.Ioc_eq_empty (by intro h; linarith), measure_empty, ENNReal.toReal_zero, zero_div]

lemma te_tail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] {s u : ℝ} (h : s ≤ u) :
    (μ (Set.Ioi u)).toReal ≤ (μ (Set.Ioi s)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi h))

/-- Tail equivalence transfers the weak convergence of residual distribution functions. -/
theorem tailEquiv_mem_Dr_core (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h12 : TailEquiv μ₁ μ₂) (h2 : InDr μ₂ (piPC p c)) :
    InDr μ₁ (piPC p c) := by
  obtain ⟨hpos1, hpos2, hlim⟩ := h12
  obtain ⟨_, a, b, ha, hconv⟩ := h2
  refine ⟨hpos1, a, b, ha, ?_⟩
  intro x hx
  have h2x := hconv x hx
  have key : Tendsto (fun t => BalkemaDeHaan.LimitTypes.residualCDF μ₁ t (b t + x * a t) -
      BalkemaDeHaan.LimitTypes.residualCDF μ₂ t (b t + x * a t)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη0 : 0 < min (ε / 8) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hη1 : min (ε / 8) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hηε : min (ε / 8) (1 / 2) ≤ ε / 8 := min_le_left _ _
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) _ hη0)
    rw [eventually_atTop]
    refine ⟨T, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero]
    by_cases hy : 0 ≤ b t + x * a t
    · rw [te_residualCDF_of_nonneg μ₁ t _ hy (hpos1 t), te_residualCDF_of_nonneg μ₂ t _ hy (hpos2 t)]
      have hA : 0 < (μ₂ (Set.Ioi t)).toReal :=
        ENNReal.toReal_pos (hpos2 t).ne' (measure_ne_top _ _)
      have hB : 0 < (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal :=
        ENNReal.toReal_pos (hpos2 _).ne' (measure_ne_top _ _)
      have hBA : (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal ≤ (μ₂ (Set.Ioi t)).toReal :=
        te_tail_antitone μ₂ (by linarith)
      have hu := hT t ht
      have hv := hT (t + (b t + x * a t)) (by linarith)
      rw [Real.dist_eq] at hu hv
      set u := (μ₁ (Set.Ioi t)).toReal / (μ₂ (Set.Ioi t)).toReal with hu_def
      set v := (μ₁ (Set.Ioi (t + (b t + x * a t)))).toReal /
        (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal with hv_def
      set A := (μ₂ (Set.Ioi t)).toReal
      set B := (μ₂ (Set.Ioi (t + (b t + x * a t)))).toReal
      have hR1 : (μ₁ (Set.Ioi t)).toReal = u * A := by
        rw [hu_def]; field_simp
      have hR1' : (μ₁ (Set.Ioi (t + (b t + x * a t)))).toReal = v * B := by
        rw [hv_def]; field_simp
      rw [hR1, hR1']
      have hu' := abs_sub_lt_iff.1 hu
      have hv' := abs_sub_lt_iff.1 hv
      have hu0 : 0 < u := by linarith
      have heq : 1 - v * B / (u * A) - (1 - B / A) = (B / A) * ((u - v) / u) := by
        field_simp; ring
      rw [heq, abs_mul]
      have h1 : |B / A| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg hB.le hA.le)]; exact div_le_one_of_le₀ hBA hA.le
      have h2 : |(u - v) / u| ≤ 4 * min (ε / 8) (1 / 2) := by
        rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
        calc |u - v| ≤ 2 * min (ε / 8) (1 / 2) := by
              rw [abs_sub_le_iff]; constructor <;> linarith
          _ ≤ 4 * min (ε / 8) (1 / 2) * u := by nlinarith
      calc |B / A| * |(u - v) / u| ≤ 1 * (4 * min (ε / 8) (1 / 2)) :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ < ε := by linarith
    · push_neg at hy
      rw [te_residualCDF_of_neg μ₁ t _ hy, te_residualCDF_of_neg μ₂ t _ hy]
      simpa using hε
  have := key.add h2x
  simp only [sub_add_cancel, zero_add] at this
  exact this

end BalkemaDeHaan.DiscreteDomain

open BalkemaDeHaan.DiscreteDomain


theorem solution (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h12 : TailEquiv μ₁ μ₂) (h2 : InDr μ₂ (piPC p c)) :
    InDr μ₁ (piPC p c) := by
  exact tailEquiv_mem_Dr_core p c hp hc μ₁ μ₂ h12 h2
