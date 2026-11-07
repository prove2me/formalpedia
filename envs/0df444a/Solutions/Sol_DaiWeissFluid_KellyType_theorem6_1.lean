-- Prove2me | solution 1 for DaiWeissFluid.KellyType.theorem6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:16:33.897827+00:00
-- url     : https://prove2.me/submissions/76b09696-4fec-41aa-88f3-57058ff51f4d

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine
import Theorems.Thm_DaiWeissFluid_KellyType_lemma2_2_ii
import Theorems.Thm_DaiWeissFluid_KellyType_lemma3_2
import Theorems.Thm_DaiWeissFluid_KellyType_lemma3_2_conditions

open Filter Topology MeasureTheory

namespace Aux_Kelly_t61
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


/-- Each queue length is differentiable at almost every `t > 0` (Rademacher). -/
lemma Q_ae_diff (L : ReentrantLine I K) {Q T : ℝ → Fin K → ℝ} (hsol : L.IsFluidSolution Q T)
    (k : Fin K) : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → DifferentiableAt ℝ (fun s => Q s k) t := by
  set C := 1 + 2 * ∑ j, |L.μ j| with hCdef
  have hC : 0 ≤ C := by
    have : 0 ≤ ∑ j, |L.μ j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith
  have hlip : LipschitzWith (Real.toNNReal C) (fun s => Q (max s 0) k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC]
    calc |Q (max x 0) k - Q (max y 0) k| ≤ C * |max x 0 - max y 0| :=
          Q_abs L hsol k _ _ (le_max_right _ _) (le_max_right _ _)
      _ ≤ C * |x - y| := mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs x y 0) hC
  filter_upwards [hlip.ae_differentiableAt] with t ht htpos
  apply ht.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htpos] with s hs
  simp [max_eq_left (le_of_lt (Set.mem_Ioi.mp hs))]

end Aux_Kelly_t61

open DaiWeissFluid.KellyType Aux_Kelly_t61 in
theorem solution {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (β : Fin 2 → ℝ) (hkelly : L.IsKellyType β)
    (hfb : L.NoImmediateFeedback) :
    DaiWeissFluid.ThreeBuffer.FluidStable L.IsWorkConserving := by
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    refine ⟨1, one_pos, fun Q T _ h1 => ?_⟩
    simp at h1
  have hI : 0 < 2 := by norm_num
  -- the drift constants
  set ε : Fin 2 → ℝ := fun i =>
    if (L.C i).Nonempty then (β i)⁻¹ - ((L.C i).card : ℝ) else 1 with hεdef
  set εm : ℝ := Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε with hεm
  set c : Fin 2 → Fin K → ℝ := fun i l => L.kellyCoeff i l with hcdef
  have hc : ∀ i l, 0 ≤ c i l := fun i l => Nat.cast_nonneg _
  have hcK : ∀ i l, c i l ≤ K := by
    intro i l
    simp only [hcdef, ReentrantLine.kellyCoeff]
    have := Finset.card_le_univ (((L.C i).filter (fun k => l ≤ k)))
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have cond := fun Q T (hwc : L.IsWorkConserving Q T) =>
    DaiWeissFluid.KellyType.lemma3_2_conditions L hm hρ β hkelly hfb Q T hwc
  have hεpos : ∀ i, 0 < ε i := by
    intro i
    simp only [hεdef]
    split_ifs with hne
    · -- the constants do not depend on the solution; use the zero solution? avoid: direct
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
    · exact one_pos
  have hεm : 0 < εm := by
    rw [hεm, Finset.lt_inf'_iff]
    exact fun i _ => hεpos i
  refine ⟨(K : ℝ) / εm + 1, by positivity, ?_⟩
  intro Q T hwc hQ0 t ht k
  have hsol := hwc.1
  obtain ⟨_, hcA, hcB⟩ := cond Q T hwc
  have ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i := by
    intro i t ht hv d hd
    by_cases hne : (L.C i).Nonempty
    · have := hcA i t ht hv d hd
      simp only [hεdef, if_pos hne]
      exact this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      unfold ReentrantLine.volume at hv
      rw [hne, Finset.sum_empty] at hv
      exact absurd hv (lt_irrefl 0)
  obtain ⟨hac, hnn, hdrv⟩ :=
    DaiWeissFluid.KellyType.lemma3_2 L hm hI Q T hsol c hc ε hεpos ha hcB
  set g : ℝ → ℝ := fun s => ⨆ i, ∑ k, c i k * Q s k with hg
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t →
      ∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t := by
    have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ k, 0 < t → DifferentiableAt ℝ (fun s => Q s k) t :=
      ae_all_iff.mpr (fun k => Q_ae_diff L hsol k)
    filter_upwards [hall] with t ht htpos i
    exact DifferentiableAt.fun_sum (fun k _ => (ht k htpos).const_mul _)
  have hdrift : ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -εm := by
    filter_upwards [hdiff] with t ht htpos hgt d hd
    exact hdrv t htpos hgt (ht htpos) d hd
  obtain ⟨hzero, _⟩ := DaiWeissFluid.KellyType.lemma2_2_ii g hac hnn εm hεm hdrift
  -- bound on g(0)
  have hg0 : g 0 ≤ K := by
    simp only [hg]
    apply ciSup_le
    intro i
    calc ∑ k, c i k * Q 0 k ≤ ∑ k, (K : ℝ) * Q 0 k :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hcK i k)
            (hsol.nonneg 0 le_rfl k))
      _ = K := by rw [← Finset.mul_sum, hQ0, mul_one]
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hgt : g t = 0 := by
    apply hzero
    calc g 0 / εm ≤ K / εm := div_le_div_of_nonneg_right hg0 hεm.le
      _ ≤ t := by linarith
  -- the station of the last class sees every queue
  set klast : Fin K := ⟨K - 1, by omega⟩ with hkl
  set i0 := L.σ klast
  have hci0 : 1 ≤ c i0 k := by
    simp only [hcdef, ReentrantLine.kellyCoeff]
    have hmem : klast ∈ (L.C i0).filter (fun k' => k ≤ k') := by
      simp only [Finset.mem_filter, ReentrantLine.C, Finset.mem_univ, true_and, i0]
      have := k.isLt; show (k : ℕ) ≤ K - 1; omega
    exact_mod_cast Finset.card_pos.mpr ⟨klast, hmem⟩
  have hnnt : ∀ l, 0 ≤ Q t l := hsol.nonneg t htpos.le
  have hle1 : c i0 k * Q t k ≤ ∑ l, c i0 l * Q t l :=
    Finset.single_le_sum (f := fun l => c i0 l * Q t l)
      (fun l _ => mul_nonneg (hc i0 l) (hnnt l)) (Finset.mem_univ k)
  have hle2 : ∑ l, c i0 l * Q t l ≤ g t :=
    le_ciSup (Finite.bddAbove_range (fun i => ∑ l, c i l * Q t l)) i0
  have hqk := hnnt k
  nlinarith
