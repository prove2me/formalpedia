-- Prove2me | solution 1 for DaiWeissFluid.LuKumar.lemma3_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:44:04.522449+00:00
-- url     : https://prove2.me/submissions/070bb88e-8e1f-48a0-8bd3-1e324a5c58a1

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

open Filter Topology

namespace Aux_LK32
open DaiWeissFluid.LuKumar

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

end Aux_LK32

open DaiWeissFluid.LuKumar in
theorem solution {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k)
    (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    let G : ℝ → ℝ := fun s => ⨆ i : Fin I, ∑ k, c i k * Q s k
    (∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval G a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ G t) ∧
    (∀ t d, 0 < t → 0 < G t → HasDerivAt G d t →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      d ≤ -(⨅ i : Fin I, ε i)) := by
  intro G
  haveI : Nonempty (Fin I) := ⟨⟨0, hI⟩⟩
  set Gi : Fin I → ℝ → ℝ := fun i s => ∑ k, c i k * Q s k with hGi
  have hGle : ∀ i s, Gi i s ≤ G s := fun i s =>
    le_ciSup (Finite.bddAbove_range (fun i => Gi i s)) i
  set LQ := 1 + 2 * ∑ j, |L.μ j| with hLQ
  set CC := ∑ i, ∑ k, c i k with hCC
  have hLQ0 : 0 ≤ LQ := by
    have : 0 ≤ ∑ j, |L.μ j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith
  have hGi_lip : ∀ i x y, 0 ≤ x → 0 ≤ y → Gi i x ≤ Gi i y + CC * LQ * |x - y| := by
    intro i x y hx hy
    have h1 : Gi i x - Gi i y ≤ ∑ k, c i k * (LQ * |x - y|) := by
      simp only [hGi]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub]
      have := Aux_LK32.Q_abs L hsol k x y hx hy
      have h3 : Q x k - Q y k ≤ LQ * |x - y| := le_trans (le_abs_self _) this
      exact mul_le_mul_of_nonneg_left h3 (hc i k)
    have h2 : ∑ k, c i k * (LQ * |x - y|) ≤ CC * LQ * |x - y| := by
      rw [← Finset.sum_mul]
      have : ∑ k, c i k ≤ CC :=
        Finset.single_le_sum (f := fun i => ∑ k, c i k)
          (fun i _ => Finset.sum_nonneg (fun k _ => hc i k)) (Finset.mem_univ i)
      have hp : 0 ≤ LQ * |x - y| := mul_nonneg hLQ0 (abs_nonneg _)
      calc (∑ k, c i k) * (LQ * |x - y|) ≤ CC * (LQ * |x - y|) :=
            mul_le_mul_of_nonneg_right this hp
        _ = CC * LQ * |x - y| := by ring
    linarith
  have hG_lip : ∀ x y, 0 ≤ x → 0 ≤ y → G x ≤ G y + CC * LQ * |x - y| := by
    intro x y hx hy
    apply ciSup_le
    intro i
    exact le_trans (hGi_lip i x y hx hy) (by linarith [hGle i y])
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha0 hab
    have hCC0 : 0 ≤ CC := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hc i k))
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal (CC * LQ))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Set.uIcc_of_le hab] at hx hy
    have hx0 : 0 ≤ x := le_trans ha0 hx.1
    have hy0 : 0 ≤ y := le_trans ha0 hy.1
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hCC0 hLQ0)]
    have a1 := hG_lip x y hx0 hy0
    have a2 := hG_lip y x hy0 hx0
    rw [abs_sub_comm y x] at a2
    rw [abs_le]
    constructor <;> linarith
  · intro t ht
    have h0 : 0 ≤ Gi ⟨0, hI⟩ t := Finset.sum_nonneg (fun k _ =>
      mul_nonneg (hc _ k) (hsol.nonneg t ht k))
    exact le_trans h0 (hGle _ t)
  · intro t d ht hGt hd hdiff
    have hvol_nn : ∀ i, 0 ≤ L.volume Q i t := fun i =>
      Finset.sum_nonneg (fun k _ => mul_nonneg (hm k).le (hsol.nonneg t ht.le k))
    obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => Gi i t)
    have hex : ∃ i, Gi i t = G t ∧ 0 < L.volume Q i t := by
      by_cases hv0 : 0 < L.volume Q i0 t
      · exact ⟨i0, hi0, hv0⟩
      · have hv0' : L.volume Q i0 t = 0 := le_antisymm (not_lt.mp hv0) (hvol_nn i0)
        have hall : ∀ j, Gi j t = G t := by
          intro j
          by_cases hj : j = i0
          · rw [hj]; exact hi0
          · apply le_antisymm (hGle j t)
            have := hb i0 t ht.le hv0' j hj
            show G t ≤ Gi j t
            calc G t = Gi i0 t := hi0.symm
              _ ≤ Gi j t := this
        by_contra hno
        push_neg at hno
        have hz : ∀ j, L.volume Q j t = 0 := fun j =>
          le_antisymm (by have := hno j (hall j); linarith) (hvol_nn j)
        have hQ0 : ∀ k, Q t k = 0 := by
          intro k
          have hv := hz (L.σ k)
          unfold ReentrantLine.volume at hv
          have hk : k ∈ L.C (L.σ k) := by simp [ReentrantLine.C]
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
            mul_nonneg (hm l).le (hsol.nonneg t ht.le l))).mp hv k hk
          exact (mul_eq_zero.mp this).resolve_left (hm k).ne'
        have : Gi i0 t = 0 := by simp [hGi, hQ0]
        rw [hi0] at this
        linarith
    obtain ⟨i, hit, hvi⟩ := hex
    set di := deriv (Gi i) t with hdidef
    have hdi' : HasDerivAt (Gi i) di t := (hdiff i).hasDerivAt
    have hmin : IsLocalMin (fun s => G s - Gi i s) t := by
      apply Filter.Eventually.of_forall
      intro s
      simp only
      rw [hit, sub_self]
      linarith [hGle i s]
    have hzero := hmin.hasDerivAt_eq_zero (hd.sub hdi')
    have hdeq : d = di := by linarith
    have hb1 := ha i t ht hvi di hdi'
    have hinf : (⨅ j, ε j) ≤ ε i := ciInf_le (Finite.bddBelow_range ε) i
    linarith
