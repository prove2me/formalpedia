-- Prove2me | solution 1 for FracColorLocal.KrFree.eq_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:02:14.551798+00:00
-- url     : https://prove2.me/submissions/2d581420-335e-45fd-bee2-d017979ad6c5

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Potential

set_option autoImplicit false

open FracColorLocal.KrFree
open OAI.CliqueFreeIndependence.WeightedGraph
open Filter Topology

/-- `f ≥ 0` on `[0, ∞)`, from `t log t ≥ t - 1`. -/
private lemma shearerF_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ shearerF t := by
  unfold shearerF
  split_ifs with h0 h1
  · norm_num
  · norm_num
  · apply div_nonneg _ (sq_nonneg _)
    have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
    have hl := Real.one_sub_inv_le_log_of_pos htp
    have : t * (1 - t⁻¹) ≤ t * Real.log t := mul_le_mul_of_nonneg_left hl ht
    rw [mul_sub, mul_one, mul_inv_cancel₀ h0] at this
    linarith

/-- `f(t) → 1 = f(0)` as `t → 0⁺`. -/
private lemma shearerF_tendsto_zero :
    Tendsto shearerF (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  set h : ℝ → ℝ := fun t => (t * Real.log t - t + 1) / (t - 1) ^ 2 with hh
  have hc : ContinuousAt h 0 := by
    apply ContinuousAt.div
    · exact ((Real.continuous_mul_log.continuousAt).sub continuousAt_id).add continuousAt_const
    · fun_prop
    · norm_num
  have h0 : h 0 = 1 := by simp [hh]
  have hlim : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    rw [← h0]; exact tendsto_nhdsWithin_of_tendsto_nhds hc
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  unfold shearerF
  rw [if_neg ht.1.ne', if_neg ht.2.ne]

/-- `U_a(x) ≤ a f(d) + d x²` for `a, x > 0`, `d ≥ 0`. -/
private lemma scalarU_le (a x d : ℝ) (ha : 0 < a) (hx : 0 < x) (hd : 0 ≤ d) :
    scalarU a x ≤ a * shearerF d + d * x ^ 2 := by
  unfold scalarU
  rw [if_neg hx.ne']
  have hbdd : BddBelow (Set.range fun t : {t : ℝ // 0 < t} => a * shearerF t + t * x ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact add_nonneg (mul_nonneg ha.le (shearerF_nonneg t t.2.le))
      (mul_nonneg t.2.le (sq_nonneg _))
  rcases hd.lt_or_eq with hd | hd
  · exact ciInf_le hbdd ⟨d, hd⟩
  · subst hd
    have key : Tendsto (fun t => a * shearerF t + t * x ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (a * shearerF 0 + 0 * x ^ 2)) := by
      have hf0 : shearerF 0 = 1 := by simp [shearerF]
      rw [hf0]
      apply Tendsto.add
      · exact shearerF_tendsto_zero.const_mul a
      · exact (tendsto_nhdsWithin_of_tendsto_nhds
          ((continuous_id.mul continuous_const).tendsto 0))
    apply ge_of_tendsto key
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ciInf_le hbdd ⟨t, ht⟩

private lemma crossMass_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (w : V → ℝ) :
    crossMass G w Finset.univ Finset.univ = ∑ v, w v * neighborMass G w v := by
  classical
  unfold crossMass neighborMass mass neighbors
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (u w : V → ℝ)
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) :
    potential G u w ≤ phiPot G u w := by
  unfold potential potentialOn phiPot
  have hv : ∀ v, scalarU (u v) (w v) ≤
      u v * shearerF (weightedDegree G w v) + w v * neighborMass G w v := by
    intro v
    have hnm : 0 ≤ neighborMass G w v :=
      Finset.sum_nonneg fun x _ => (hw x).le
    have := scalarU_le (u v) (w v) (weightedDegree G w v) (hu v) (hw v)
      (div_nonneg hnm (hw v).le)
    have he : weightedDegree G w v * w v ^ 2 = w v * neighborMass G w v := by
      unfold weightedDegree
      field_simp [(hw v).ne']
    linarith
  have hs := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hv v
  rw [Finset.sum_add_distrib] at hs
  rw [crossMass_eq]
  linarith
