-- Prove2me | solution 1 for DaiWeissFluid.KellyType.lemma3_2_conditions
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:16:19.827629+00:00
-- url     : https://prove2.me/submissions/4d5b4e84-7a29-4a44-9251-55a1cdc16d9a

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine
import Theorems.Thm_DaiWeissFluid_KellyType_condition_b
import Theorems.Thm_DaiWeissFluid_KellyType_drift_identity

open Filter Topology

namespace Aux_Kelly_l32c
open DaiWeissFluid.KellyType

variable {I K : ℕ}

lemma T_lip (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) : T y k - T x k ≤ y - x := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hidle := hsol.idle_mono (L.σ k) (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy
  simp only [ReentrantLine.idle, ReentrantLine.busy] at hidle
  have hk : k ∈ L.C (L.σ k) := by simp [ReentrantLine.C]
  have hsum : T y k - T x k ≤ ∑ l ∈ L.C (L.σ k), (T y l - T x l) :=
    Finset.single_le_sum (f := fun l => T y l - T x l)
      (fun l _ => sub_nonneg.mpr (hsol.T_mono l (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy)) hk
  rw [Finset.sum_sub_distrib] at hsum
  linarith

lemma T_abs (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : |T x k - T y k| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have a1 := T_lip L hsol k x y hx h
    have a2 := hsol.T_mono k (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) h
    simp only at a2
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact a1
  · have a1 := T_lip L hsol k y x hy h
    have a2 := hsol.T_mono k (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) h
    simp only at a2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact a1

lemma Q_abs (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Q x k - Q y k| ≤ (1 + 2 * ∑ j, |L.μ j|) * |x - y| := by
  set M := ∑ j, |L.μ j| with hM
  have hMj : ∀ j, |L.μ j| ≤ M := fun j =>
    Finset.single_le_sum (f := fun j => |L.μ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hxy0 : 0 ≤ |x - y| := abs_nonneg _
  have hin : |L.inflow T k x - L.inflow T k y| ≤ (1 + M) * |x - y| := by
    unfold ReentrantLine.inflow
    split_ifs with h
    · nlinarith
    · rw [← mul_sub, abs_mul]
      have := T_abs L hsol ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ x y hx hy
      have := hMj ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩
      nlinarith [abs_nonneg (L.μ ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩),
        abs_nonneg (T x ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ -
          T y ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩)]
  have hT := T_abs L hsol k x y hx hy
  have hmk := hMj k
  rw [hsol.flow x hx k, hsol.flow y hy k]
  have e : Q 0 k + L.inflow T k x - L.μ k * T x k - (Q 0 k + L.inflow T k y - L.μ k * T y k) =
      (L.inflow T k x - L.inflow T k y) - L.μ k * (T x k - T y k) := by ring
  rw [e]
  have h2 : |L.μ k * (T x k - T y k)| ≤ M * |x - y| := by
    rw [abs_mul]
    exact mul_le_mul hmk hT (abs_nonneg _) hM0
  calc |(L.inflow T k x - L.inflow T k y) - L.μ k * (T x k - T y k)|
      ≤ |L.inflow T k x - L.inflow T k y| + |L.μ k * (T x k - T y k)| := abs_sub _ _
    _ ≤ (1 + M) * |x - y| + M * |x - y| := add_le_add hin h2
    _ = (1 + 2 * M) * |x - y| := by ring

lemma Q_contOn (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) : ContinuousOn (fun s => Q s k) (Set.Ici 0) := by
  have hC : 0 ≤ 1 + 2 * ∑ j, |L.μ j| := by
    have : 0 ≤ ∑ j, |L.μ j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith
  apply LipschitzOnWith.continuousOn (K := Real.toNNReal (1 + 2 * ∑ j, |L.μ j|))
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
  exact Q_abs L hsol k x y hx hy

lemma kellyG_eq (L : ReentrantLine I K) (Q : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) :
    L.kellyG Q i t = ∑ l, L.kellyCoeff i l * Q t l := by
  unfold ReentrantLine.kellyG DaiWeissFluid.ThreeBuffer.Qplus ReentrantLine.kellyCoeff
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

end Aux_Kelly_l32c

open DaiWeissFluid.KellyType Aux_Kelly_l32c in
theorem solution {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (β : Fin 2 → ℝ) (hkelly : L.IsKellyType β)
    (hfb : L.NoImmediateFeedback)
    (Q T : ℝ → Fin K → ℝ) (hwc : L.IsWorkConserving Q T) :
    (∀ i, (L.C i).Nonempty → 0 < (β i)⁻¹ - ((L.C i).card : ℝ)) ∧
    (∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, L.kellyCoeff i k * Q s k) d t →
        d ≤ -((β i)⁻¹ - ((L.C i).card : ℝ))) ∧
    (∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, L.kellyCoeff i k * Q t k ≤ ∑ k, L.kellyCoeff j k * Q t k) := by
  obtain ⟨hsol, hwork⟩ := hwc
  refine ⟨?_, ?_, ?_⟩
  · intro i hne
    obtain ⟨k0, hk0⟩ := hne
    have hσ : ∀ k ∈ L.C i, L.m k = β i := by
      intro k hk
      rw [hkelly k, (Finset.mem_filter.mp hk).2]
    have hβ : 0 < β i := by rw [← hσ k0 hk0]; exact hm k0
    have hρi : L.ρ i = ((L.C i).card : ℝ) * β i := by
      unfold ReentrantLine.ρ
      rw [Finset.sum_congr rfl hσ, Finset.sum_const, nsmul_eq_mul]
    have h1 := hρ i
    rw [hρi] at h1
    have h2 := mul_lt_mul_of_pos_right h1 (inv_pos.mpr hβ)
    rw [mul_assoc, mul_inv_cancel₀ hβ.ne', mul_one, one_mul] at h2
    linarith
  · intro i t ht hv d hd
    -- the Kelly component as a function of time
    have hFeq : (fun s => ∑ k, L.kellyCoeff i k * Q s k) = fun s => L.kellyG Q i s := by
      funext s; rw [kellyG_eq]
    rw [hFeq] at hd
    -- station i is busy at t
    have hnn : ∀ k, 0 ≤ Q t k := hsol.nonneg t ht.le
    have hpos_t : 0 < ∑ k ∈ L.C i, Q t k := by
      by_contra hcon
      have hle : ∑ k ∈ L.C i, Q t k ≤ 0 := not_lt.mp hcon
      have hz : ∀ k ∈ L.C i, Q t k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).mp
          (le_antisymm hle (Finset.sum_nonneg fun k _ => hnn k))
      have : L.volume Q i t = 0 := by
        unfold ReentrantLine.volume
        exact Finset.sum_eq_zero (fun k hk => by rw [hz k hk, mul_zero])
      linarith
    have hcont : ContinuousAt (fun s => ∑ k ∈ L.C i, Q s k) t :=
      (continuousOn_finsetSum _ (fun k _ => Q_contOn L hsol k)).continuousAt
        (Ici_mem_nhds ht)
    have h1 : ∀ᶠ s in 𝓝 t, (0 : ℝ) < ∑ k ∈ L.C i, Q s k :=
      continuousAt_const.eventually_lt hcont hpos_t
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and (Ioi_mem_nhds ht))
    -- busy time grows at unit rate near t
    have hbusy : ∀ s, dist s t < η → L.busy T i s = L.busy T i t + (s - t) := by
      intro s hs
      rcases le_total t s with h | h
      · have := hwork i t s ht.le h (fun u hu => (hball (by
          rw [Real.dist_eq] at hs ⊢; rw [abs_lt] at hs ⊢
          constructor <;> linarith [hu.1, hu.2])).1)
        unfold ReentrantLine.idle at this
        linarith
      · have := hwork i s t (hball hs).2.le h (fun u hu => (hball (by
          rw [Real.dist_eq] at hs ⊢; rw [abs_lt] at hs ⊢
          constructor <;> linarith [hu.1, hu.2])).1)
        unfold ReentrantLine.idle at this
        linarith
    set c : ℝ := ((L.C i).card : ℝ) with hc
    have hloc : ∀ᶠ s in 𝓝 t, L.kellyG Q i s = L.kellyG Q i t + (c - (β i)⁻¹) * (s - t) := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨η, hη, fun s hs => ?_⟩
      have hs0 : 0 < s := (hball hs).2
      have e1 := DaiWeissFluid.KellyType.drift_identity L hm β hkelly Q T hsol i s hs0.le
      have e2 := DaiWeissFluid.KellyType.drift_identity L hm β hkelly Q T hsol i t ht.le
      rw [e1, e2, hbusy s hs]
      ring
    have hlin : HasDerivAt (fun s => L.kellyG Q i t + (c - (β i)⁻¹) * (s - t))
        (c - (β i)⁻¹) t := by
      have := (((hasDerivAt_id t).sub_const t).const_mul (c - (β i)⁻¹)).const_add
        (L.kellyG Q i t)
      simpa using this
    have hd' : HasDerivAt (fun s => L.kellyG Q i s) (c - (β i)⁻¹) t :=
      hlin.congr_of_eventuallyEq hloc
    have := hd.unique hd'
    linarith
  · intro i t ht hv j hji
    rw [← kellyG_eq, ← kellyG_eq]
    exact (DaiWeissFluid.KellyType.condition_b L hm hfb Q T hsol t ht i j (Ne.symm hji) hv).1
