-- Prove2me | solution 1 for ExtraConsensus.Sublinear.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:18:22.019055+00:00
-- url     : https://prove2.me/submissions/6c73d364-fea3-4c29-92fc-079956e9ab86

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model
set_option autoImplicit false
open ExtraConsensus.Sublinear
open Matrix Filter Topology Asymptotics

theorem solution (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : Summable a) :
    Tendsto a atTop (𝓝 0) ∧
      (fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.Icc 1 k, a t) =O[atTop]
        (fun k : ℕ => (1 : ℝ) / k) ∧
      (fun k : ℕ => runMin a k) =o[atTop] (fun k : ℕ => (1 : ℝ) / k) := by
  refine ⟨hsum.tendsto_atTop_zero, ?_, ?_⟩
  · apply IsBigO.of_bound (∑' t, a t)
    refine Filter.Eventually.of_forall (fun k => ?_)
    have h1 : ∑ t ∈ Finset.Icc 1 k, a t ≤ ∑' t, a t := hsum.sum_le_tsum _ (fun t _ => ha t)
    have h2 : 0 ≤ ∑ t ∈ Finset.Icc 1 k, a t := Finset.sum_nonneg (fun t _ => ha t)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (k:ℝ))]
    calc 1 / (k:ℝ) * ∑ t ∈ Finset.Icc 1 k, a t ≤ 1 / (k:ℝ) * ∑' t, a t :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (∑' t, a t) * (1 / (k:ℝ)) := by ring
  · apply IsLittleO.of_bound
    intro c hc
    have hcs : CauchySeq (fun n => ∑ i ∈ Finset.range n, a i) := hsum.hasSum.tendsto_sum_nat.cauchySeq
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcs (c / 2) (by positivity)
    rw [Filter.eventually_atTop]
    refine ⟨2 * N + 2, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := by omega
    have hkpos : (0:ℝ) < k := by exact_mod_cast hk1
    set J := Finset.Ico (k / 2 + 1) (k + 1) with hJ
    have hcard : J.card = k - k / 2 := by rw [hJ, Nat.card_Ico]; omega
    have hcardr : (k : ℝ) / 2 ≤ (J.card : ℝ) := by
      rw [hcard]
      have : k / 2 ≤ k := Nat.div_le_self _ _
      rw [Nat.cast_sub this]
      have h2 : (k / 2 : ℕ) * 2 ≤ k := by omega
      have h3 : ((k / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) := by exact_mod_cast h2
      linarith
    have hsumJ : ∑ t ∈ J, a t < c / 2 := by
      rw [hJ, Finset.sum_Ico_eq_sub _ (by omega : k / 2 + 1 ≤ k + 1)]
      have := hN (k + 1) (by omega) (k / 2 + 1) (by omega)
      rw [Real.dist_eq] at this
      have h' := (abs_lt.1 this).2
      linarith
    have hmin : ∀ t ∈ J, runMin a k ≤ a t := by
      intro t ht
      rw [hJ, Finset.mem_Ico] at ht
      unfold runMin
      apply ciInf_le_of_le (⟨0, by
        rintro _ ⟨s, rfl⟩; exact ha _⟩ : BddBelow (Set.range fun t : Finset.Icc 1 k => a t.1))
        ⟨t, by rw [Finset.mem_Icc]; omega⟩
      exact le_refl _
    have hm0 : 0 ≤ runMin a k := by
      unfold runMin
      haveI : Nonempty (Finset.Icc 1 k) := ⟨⟨1, by rw [Finset.mem_Icc]; omega⟩⟩
      exact le_ciInf (fun t => ha _)
    have hle : (J.card : ℝ) * runMin a k ≤ ∑ t ∈ J, a t := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum J _ _ hmin
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (k:ℝ))]
    have h1 : (k:ℝ) / 2 * runMin a k ≤ c / 2 := by
      calc (k:ℝ) / 2 * runMin a k ≤ (J.card : ℝ) * runMin a k := mul_le_mul_of_nonneg_right hcardr hm0
        _ ≤ ∑ t ∈ J, a t := hle
        _ ≤ c / 2 := hsumJ.le
    rw [show c * (1 / (k:ℝ)) = c / k by ring, le_div_iff₀ hkpos]
    linarith
