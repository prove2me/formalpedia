-- Prove2me | solution 1 for CapScaleML.ABCS.theorem_4_7
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:14:34.520739+00:00
-- url     : https://prove2.me/submissions/12d51f8a-556b-45ae-a838-1ed27c669b30

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS.CostBug

/-- Instance: ω = 1, β = 8, θ = 0, T = 4, λ ≡ 1, λ̃ ≡ 0. -/
noncomputable abbrev L1 : ℝ → ℝ := fun _ => 1
noncomputable abbrev Z0 : ℝ → ℝ := fun _ => 0
noncomputable abbrev M2 : ℝ → ℝ := apOnline 1 8 L1 Z0

lemma sqrt16 : Real.sqrt 16 = 4 := by
  rw [show (16:ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma sqrt_inv16 : Real.sqrt (1 / (2 * 8)) = 1 / 4 := by
  rw [show (1 / (2 * 8) : ℝ) = (1 / 4) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma delta_val (s : ℝ) : deltaLam L1 Z0 s = if 0 ≤ s then 1 else 0 := by
  simp [deltaLam]

lemma M2_val (t : ℝ) (ht : t ∈ Icc (0:ℝ) 4) : M2 t = t / 4 := by
  show apOnline 1 8 L1 Z0 t = t / 4
  unfold apOnline
  rw [sqrt_inv16, show (2 * 8 / 1 : ℝ) = 16 by norm_num, sqrt16]
  rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => (1:ℝ) / 4) ht.1]
  · simp; ring
  · intro s hs
    simp only [delta_val]
    rw [if_pos hs.1.le, if_neg (by linarith [hs.2, ht.2])]
    ring

lemma switchSum_M2 (δ : ℝ) (hδ : 0 < δ) : switchSum 4 δ M2 = 1 := by
  unfold switchSum
  set N := ⌊(4:ℝ) / δ⌋₊
  have hN : (N : ℝ) * δ ≤ 4 := by
    have := Nat.floor_le (show (0:ℝ) ≤ 4 / δ by positivity)
    calc (N : ℝ) * δ ≤ 4 / δ * δ := by gcongr
      _ = 4 := by field_simp
  have hN1 : 4 < ((N : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one ((4:ℝ) / δ)
    calc (4:ℝ) = 4 / δ * δ := by field_simp
      _ < ((N : ℝ) + 1) * δ := by gcongr
  let h : ℕ → ℝ := fun i => min ((i : ℝ) * δ) 4 / 4
  have key : ∀ i ∈ Finset.range (N + 1),
      ENNReal.ofReal (M2 (min (((i : ℕ) + 1 : ℝ) * δ) 4) - M2 ((i : ℝ) * δ)) =
      ENNReal.ofReal (h (i + 1) - h i) := by
    intro i hi
    have hi' : (i : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hiδ : (i : ℝ) * δ ≤ 4 := le_trans (by gcongr) hN
    have hi0 : 0 ≤ (i : ℝ) * δ := by positivity
    rw [M2_val _ ⟨le_min (by positivity) (by norm_num), min_le_right _ _⟩,
      M2_val _ ⟨hi0, hiδ⟩]
    simp only [h, Nat.cast_add, Nat.cast_one, min_eq_left hiδ]
  rw [Finset.sum_congr rfl key, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [Finset.sum_range_sub (fun i => h i) (N + 1)]
    simp only [h]
    rw [min_eq_right (by push_cast; linarith)]
    simp
  · intro i _
    simp only [h, sub_nonneg]
    gcongr
    push_cast; linarith

lemma switching_M2 : switching 4 M2 = 1 := by
  unfold switching
  have : (fun δ => switchSum 4 δ M2) =ᶠ[nhdsWithin 0 (Ioi 0)] fun _ => 1 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact switchSum_M2 δ hδ
  rw [Filter.limsup_congr this, Filter.limsup_const]

lemma switching_zero (t : ℝ) : switching t (fun _ => (0:ℝ)) = 0 := by
  unfold switching switchSum
  simp

/-- The (as-formalized) cost of AP's online component on this instance is at least 32. -/
lemma cost_M2_ge (q : ℝ → ℝ) : (32 : ℝ≥0∞) ≤ cost 1 8 0 4 M2 q := by
  unfold cost
  rw [switching_M2, ENNReal.ofReal_one, one_mul]
  calc (32 : ℝ≥0∞) = ∫⁻ _ in Icc (0:ℝ) 4, (8 : ℝ≥0∞) := by
        rw [setLIntegral_const, Real.volume_Icc]
        rw [show (4:ℝ) - 0 = 4 by norm_num]
        rw [show (8 : ℝ≥0∞) * ENNReal.ofReal 4 = ENNReal.ofReal (8 * 4) by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp]
        norm_num
    _ ≤ _ := by
        refine lintegral_mono (fun s => ?_)
        rw [show ENNReal.ofReal 8 = (8 : ℝ≥0∞) by simp, mul_one]
        calc (8 : ℝ≥0∞) ≤ ENNReal.ofReal (q s) + 8 := le_add_self
          _ ≤ _ := le_self_add

/-- An explicit workload for `M2` under any arrival process equal to `1` on `[0,4]`. -/
noncomputable def Q2 : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, (1 - M2 s)

lemma one_sub_M2_ii : IntervalIntegrable (fun s => 1 - M2 s) volume 0 4 := by
  have hc : IntervalIntegrable (fun s : ℝ => 1 - s / 4) volume 0 4 :=
    (continuous_const.sub (continuous_id.div_const 4)).intervalIntegrable _ _
  refine hc.congr (fun s hs => ?_)
  rw [uIoc_of_le (by norm_num)] at hs
  rw [M2_val s ⟨hs.1.le, hs.2⟩]

lemma workload_Q2 (L : ℝ → ℝ) (hL : ∀ s ∈ Icc (0:ℝ) 4, L s = 1) : IsWorkload 4 L M2 Q2 := by
  have hpt : ∀ s ∈ Icc (0:ℝ) 4,
      (if 0 < Q2 s ∨ M2 s ≤ L s then L s - M2 s else 0) = 1 - M2 s := by
    intro s hs
    rw [hL s hs, if_pos (Or.inr (by rw [M2_val s hs]; linarith [hs.2]))]
  refine ⟨?_, ?_⟩
  · refine one_sub_M2_ii.congr (fun s hs => ?_)
    rw [uIoc_of_le (by norm_num)] at hs
    exact (hpt s ⟨hs.1.le, hs.2⟩).symm
  · intro t ht
    unfold Q2
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le ht.1] at hs
    exact (hpt s ⟨hs.1, hs.2.trans ht.2⟩).symm

lemma mae_one : mae 4 (deltaLam L1 Z0) (fun _ => 0) = 1 := by
  unfold mae
  rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => (1:ℝ)) (by norm_num)]
  · simp
  · intro s hs
    simp only [delta_val, if_pos hs.1.le]; simp

lemma mae_one' : mae 4 Z0 L1 = 1 := by
  unfold mae
  simp

end CapScaleML.ABCS.CostBug

namespace CapScaleML.ABCS.CostBug

lemma cost_zero (t : ℝ) (ω β θ : ℝ) : cost ω β θ t Z0 Z0 = 0 := by
  unfold cost
  rw [switching_zero]
  simp

lemma workload_zero : IsWorkload 4 Z0 Z0 Z0 := by
  refine ⟨?_, ?_⟩
  · simp
  · intro t _; simp

lemma adm_zero : Admissible 4 Z0 := ⟨rfl, fun _ _ => le_rfl, intervalIntegrable_const⟩

lemma opt_zero : opt 1 8 0 4 Z0 = 0 :=
  le_antisymm (iInf_le_of_le Z0 (iInf_le_of_le Z0 (iInf_le_of_le ⟨adm_zero, workload_zero⟩
    (cost_zero 4 1 8 0).le))) (zero_le')

lemma ap_advice : IsAPAdvice 1 8 0 4 L1 Z0 M2 :=
  ⟨Z0, Z0, ⟨adm_zero, workload_zero, by rw [cost_zero, opt_zero]⟩, fun t _ => by simp [M2]⟩

lemma workload_id : IsWorkload 4 L1 Z0 (fun t => t) := by
  refine ⟨?_, ?_⟩
  · simp
  · intro t _; simp

lemma opt_L1_le : opt 1 8 0 4 L1 ≤ ENNReal.ofReal 8 := by
  refine iInf_le_of_le Z0 (iInf_le_of_le (fun t => t) (iInf_le_of_le ⟨adm_zero, workload_id⟩ ?_))
  unfold cost
  rw [switching_zero]
  simp only [ENNReal.ofReal_one, one_mul, mul_zero, add_zero, ENNReal.ofReal_zero, zero_mul]
  have hint : IntegrableOn (fun s : ℝ => s) (Icc (0:ℝ) 4) := continuous_id.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hx.1))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

end CapScaleML.ABCS.CostBug

open CapScaleML.ABCS CapScaleML.ABCS.CostBug in
theorem solution : ¬ (∀ (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (mAdv qAdv : ℝ → ℝ) (hAP : IsAPAdvice ω β θ T lam lamHat mAdv)
    (hq : IsWorkload T lam mAdv qAdv),
    cost ω β θ T mAdv qAdv ≤ opt ω β θ T lam +
      ENNReal.ofReal ((Real.sqrt (2 * ω * β) + θ) * (T * mae T lamHat lam)) ∧
    (∀ η : ℝ, 0 < η → IsEtaAccurate ω β θ T η lam lamHat →
      cost ω β θ T mAdv qAdv ≤
        ENNReal.ofReal (1 + (Real.sqrt (2 * ω * β) + θ) * η) * opt ω β θ T lam)) := by
  intro H
  have h := (H 1 8 0 4 (by norm_num) (by norm_num) le_rfl (by norm_num) L1 Z0
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) intervalIntegrable_const
    intervalIntegrable_const M2 Q2 ap_advice (workload_Q2 _ (fun _ _ => rfl))).1
  have hlb := cost_M2_ge Q2
  rw [mae_one', show (2 * 1 * 8 : ℝ) = 16 by norm_num, sqrt16,
    show ((4 : ℝ) + 0) * (4 * 1) = 16 by norm_num] at h
  have h2 := hlb.trans (h.trans (add_le_add opt_L1_le le_rfl))
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    show (32 : ℝ≥0∞) = ENNReal.ofReal 32 by simp,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h2
  norm_num at h2
