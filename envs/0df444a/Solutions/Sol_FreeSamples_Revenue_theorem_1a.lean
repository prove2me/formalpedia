-- Prove2me | solution 1 for FreeSamples.Revenue.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:17:13.124687+00:00
-- url     : https://prove2.me/submissions/28ef4cf8-8205-42bf-9b9d-227369425635

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting
import Theorems.Thm_FreeSamples_Revenue_lemma_4b

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamplesRedAux
open FreeSamples.Revenue

lemma BR_nonneg (u : ℝ → ℝ → ℝ) (hu : HasMax u) (m v : ℝ) (hv : 0 < v) : 0 ≤ BR u m v := by
  obtain ⟨a₀, ha₀⟩ := hu.expected m v hv
  have hU : Uval u m v = ∫ x, u a₀ x ∂N m v := by
    unfold Uval
    exact le_antisymm (ciSup_le ha₀) (le_ciSup ⟨_, by rintro _ ⟨a, rfl⟩; exact ha₀ a⟩ a₀)
  unfold BR
  rw [hU, sub_nonneg]
  refine integral_mono (hu.integrable m v hv a₀) (hu.integrable_max m v hv) ?_
  intro x
  obtain ⟨b, hb⟩ := hu.pointwise x
  exact le_ciSup ⟨_, by rintro _ ⟨a, rfl⟩; exact hb a⟩ a₀

end FreeSamplesRedAux

open FreeSamples.Revenue in
theorem solution (p : Params) (u : ℝ → ℝ → ℝ) (hu : HasMax u) (hA : Assumption1 u)
    (hG : GrowthPin (BR u) p.σ₀sq)
    (h4 : 0 < (1 / 2) * dθθ (BR u) p.θ₀ p.σ₀sq - dv (BR u) p.θ₀ p.σ₀sq
      + p.μb / p.σ₀sq * dθ (BR u) p.θ₀ p.σ₀sq)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (θ : Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hM : IsModel P (p.θ₀ + p.μb) p.σssq θ B) :
    ∃ T : Ω → ℝ≥0, IsFreeSamplePolicy (dataFiltration p.σsq θ B hM.meas_θ hM.meas_B) T ∧
      Integrable (revenue p u θ B T) P ∧
      BR u p.θ₀ p.σ₀sq < ∫ ω, revenue p u θ B T ω ∂P := by
  have hP := hM.isProb
  have hd := lemma_4b p u hu hA hG P θ B hM
  set f : ℝ → ℝ := fun h : ℝ => ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω))
    (p.buyerVar h) ∂P with hf
  have hD : 0 < drift (BR u) p.θ₀ p.σ₀sq p.μb * p.σ₀sq ^ 2 / p.σsq := by
    have : 0 < drift (BR u) p.θ₀ p.σ₀sq p.μb := h4
    have := p.σ₀sq_pos; have := p.σsq_pos
    positivity
  -- value at 0
  have hf0 : f 0 = BR u p.θ₀ p.σ₀sq := by
    have hv0 : p.buyerVar 0 = p.σ₀sq := by
      unfold Params.buyerVar postVar
      have := p.σsq_pos.ne'
      simp [this]
    have hae : (fun ω => BR u (p.buyerMean 0 (Y p.σsq θ B (0:ℝ).toNNReal ω)) (p.buyerVar 0))
        =ᵐ[P] fun _ => BR u p.θ₀ p.σ₀sq := by
      filter_upwards [hM.brownian.eval_zero_ae_eq_zero] with ω hω
      have hY : Y p.σsq θ B (0:ℝ).toNNReal ω = 0 := by
        simp [Y, hω]
      rw [hY, hv0]
      congr 1
      unfold Params.buyerMean postMean
      rw [show postVar p.σsq p.σ₀sq 0 = p.σ₀sq from hv0]
      have := p.σ₀sq_pos.ne'
      field_simp
      simp
    simp only [hf]
    rw [integral_congr_ae hae]
    simp
  -- slope positivity
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  have hIci : Set.Ici (0:ℝ) \ {0} = Set.Ioi 0 := by
    ext x; simp [lt_iff_le_and_ne, eq_comm]
  rw [hIci] at hslope
  have hev : ∀ᶠ h in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < slope f 0 h ∧ 0 < h :=
    (hslope.eventually (lt_mem_nhds hD)).and self_mem_nhdsWithin
  obtain ⟨h, hs, hpos⟩ := hev.exists
  have hlt : f 0 < f h := by
    rw [slope_def_field] at hs
    have : 0 < f h - f 0 := by
      have h' : (0:ℝ) < h - 0 := by linarith
      exact (div_pos_iff_of_pos_right h').mp hs
    linarith
  refine ⟨fun _ => h.toNNReal, ⟨isStoppingTime_const _ _, ⟨h.toNNReal, fun _ => le_rfl⟩⟩, ?_⟩
  have hrev : revenue p u θ B (fun _ => h.toNNReal) = fun ω =>
      BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) (p.buyerVar h) := by
    funext ω
    simp only [revenue, Real.coe_toNNReal _ hpos.le]
  rw [hrev]
  have hint : ∫ ω, BR u (p.buyerMean h (Y p.σsq θ B h.toNNReal ω)) (p.buyerVar h) ∂P = f h := rfl
  have hBR0 := FreeSamplesRedAux.BR_nonneg u hu p.θ₀ p.σ₀sq p.σ₀sq_pos
  refine ⟨?_, by rw [hint, ← hf0]; exact hlt⟩
  by_contra hni
  have : f h = 0 := integral_undef hni
  linarith
