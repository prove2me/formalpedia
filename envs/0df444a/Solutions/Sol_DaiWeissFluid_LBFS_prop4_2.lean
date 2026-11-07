-- Prove2me | solution 1 for DaiWeissFluid.LBFS.prop4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:27:36.708846+00:00
-- url     : https://prove2.me/submissions/6185134b-0c38-410a-bc27-a5d75174fc51

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel

namespace DaiWeissFluid.LBFS

open Set Filter Topology

/-- A function monotone on `[0, ∞)` has nonnegative derivative at every `t > 0`. -/
lemma p42_deriv_nonneg {f : ℝ → ℝ} {d t : ℝ} (hf : MonotoneOn f (Ici 0)) (ht : 0 < t)
    (hd : HasDerivAt f d t) : 0 ≤ d := by
  have hmono : Monotone (fun s => f (max s (t / 2))) := by
    intro a b hab
    apply hf (by simp only [mem_Ici]; exact le_trans (by linarith) (le_max_right _ _))
      (by simp only [mem_Ici]; exact le_trans (by linarith) (le_max_right _ _))
    exact max_le_max hab le_rfl
  have heq : (fun s => f (max s (t / 2))) =ᶠ[𝓝 t] f := by
    filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs
    simp only [mem_Ioi] at hs
    rw [max_eq_left hs.le]
  exact (hd.congr_of_eventuallyEq heq).nonneg_of_monotone hmono

/-- Derivative of a locally constant function vanishes. -/
lemma p42_deriv_zero_of_const {f : ℝ → ℝ} {d t c : ℝ} (hd : HasDerivAt f d t)
    (hc : f =ᶠ[𝓝 t] fun _ => c) : d = 0 :=
  hd.unique ((hasDerivAt_const t c).congr_of_eventuallyEq hc)

end DaiWeissFluid.LBFS

open DaiWeissFluid.LBFS Set Filter Topology in
theorem solution {I K : ℕ} (L : DaiWeissFluid.LBFS.ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (π : Equiv.Perm (Fin K)) (Q T : ℝ → Fin K → ℝ)
    (hsol : L.IsPrioritySolution π Q T) (t : ℝ) (ht : 0 < t)
    (dT : Fin K → ℝ) (hdT : ∀ k, HasDerivAt (fun s => T s k) (dT k) t) :
    (∀ k, Q t k = 0 → L.inRate dT k = L.outRate dT k) ∧
      ∀ k₀, 0 < Q t k₀ →
        (∀ l, L.σ l = L.σ k₀ → π l < π k₀ → Q t l = 0) →
        (∑ k ∈ L.H π k₀, L.m k * L.outRate dT k = 1) ∧
          ∀ l, L.σ l = L.σ k₀ → π k₀ < π l → L.outRate dT l = 0 := by
  obtain ⟨hfs, hpri⟩ := hsol
  have hpos_nhds : ∀ᶠ s in 𝓝 t, 0 < s := Ioi_mem_nhds ht
  -- nonnegativity of service rates
  have hdT_nonneg : ∀ k, 0 ≤ dT k := fun k => p42_deriv_nonneg (hfs.T_mono k) ht (hdT k)
  -- derivative of the inflow
  have hinfl : ∀ k, HasDerivAt (fun s => L.inflow T k s) (L.inRate dT k) t := by
    intro k
    by_cases h : (k : ℕ) = 0
    · simp only [ReentrantLine.inflow, ReentrantLine.inRate, h, dite_true]
      exact hasDerivAt_id' t
    · simp only [ReentrantLine.inflow, ReentrantLine.inRate, ReentrantLine.outRate, h,
        dite_false]
      exact (hdT _).const_mul _
  -- derivative of the buffer levels
  have hQd : ∀ k, HasDerivAt (fun s => Q s k) (L.inRate dT k - L.outRate dT k) t := by
    intro k
    have h1 : HasDerivAt (fun s => Q 0 k + L.inflow T k s - L.μ k * T s k)
        (0 + L.inRate dT k - L.μ k * dT k) t :=
      ((hasDerivAt_const t (Q 0 k)).add (hinfl k)).sub ((hdT k).const_mul _)
    have h2 : (fun s => Q s k) =ᶠ[𝓝 t] (fun s => Q 0 k + L.inflow T k s - L.μ k * T s k) := by
      filter_upwards [hpos_nhds] with s hs
      exact hfs.flow s hs.le k
    have := h1.congr_of_eventuallyEq h2
    simpa [ReentrantLine.outRate] using this
  have hmμ : ∀ k, L.m k * L.μ k = 1 := fun k => by
    simp only [ReentrantLine.μ]; exact mul_inv_cancel₀ (hm k).ne'
  refine ⟨?_, ?_⟩
  · -- (b)
    intro k hk
    have hmin : IsLocalMin (fun s => Q s k) t := by
      filter_upwards [hpos_nhds] with s hs
      rw [hk]; exact hfs.nonneg s hs.le k
    have := hmin.hasDerivAt_eq_zero (hQd k)
    linarith
  · -- (c)
    intro k₀ hk₀ _
    have hk₀H : k₀ ∈ L.H π k₀ := by simp [ReentrantLine.H]
    -- Wplus is positive near t
    have hWd : HasDerivAt (fun s => L.Wplus π Q k₀ s)
        (∑ l ∈ L.H π k₀, L.m l * (L.inRate dT l - L.outRate dT l)) t := by
      simp only [ReentrantLine.Wplus]
      exact HasDerivAt.fun_sum (fun l _ => (hQd l).const_mul _)
    have hWt : 0 < L.Wplus π Q k₀ t := by
      simp only [ReentrantLine.Wplus]
      calc 0 < L.m k₀ * Q t k₀ := mul_pos (hm k₀) hk₀
        _ ≤ ∑ l ∈ L.H π k₀, L.m l * Q t l :=
          Finset.single_le_sum (f := fun l => L.m l * Q t l)
            (fun l _ => mul_nonneg (hm l).le (hfs.nonneg t ht.le l)) hk₀H
    have hev : ∀ᶠ u in 𝓝 t, 0 < L.Wplus π Q k₀ u :=
      hWd.continuousAt.eventually (Ioi_mem_nhds hWt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set η := min (ε / 2) (t / 2) with hη
    have hη0 : 0 < η := lt_min (by linarith) (by linarith)
    have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηt : η ≤ t / 2 := min_le_right _ _
    have hconst : ∀ u ∈ Icc (t - η) (t + η), L.Uplus π T k₀ u = L.Uplus π T k₀ (t - η) := by
      intro u hu
      apply hpri k₀ (t - η) u (by linarith) hu.1
      intro v hv
      apply hball
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hv.1, hv.2, hu.1, hu.2]
    have hUd : HasDerivAt (fun s => L.Uplus π T k₀ s) (1 - ∑ l ∈ L.H π k₀, dT l) t := by
      simp only [ReentrantLine.Uplus, ReentrantLine.Tplus]
      exact (hasDerivAt_id' t).sub (HasDerivAt.fun_sum (fun l _ => hdT l))
    have hUc : (fun s => L.Uplus π T k₀ s) =ᶠ[𝓝 t] fun _ => L.Uplus π T k₀ (t - η) := by
      filter_upwards [Ioo_mem_nhds (show t - η < t by linarith) (show t < t + η by linarith)]
        with u hu
      exact hconst u ⟨hu.1.le, hu.2.le⟩
    have hsumH : ∑ l ∈ L.H π k₀, dT l = 1 := by
      have := p42_deriv_zero_of_const hUd hUc
      linarith
    have hmout : ∀ l, L.m l * L.outRate dT l = dT l := fun l => by
      simp only [ReentrantLine.outRate]; rw [← mul_assoc, hmμ, one_mul]
    refine ⟨?_, ?_⟩
    · simp only [hmout]; exact hsumH
    · intro l hl hlt
      -- idle time is monotone, so the station's total service rate is at most one
      set i := L.σ k₀
      have hId : HasDerivAt (fun s => L.idle T i s) (1 - ∑ l ∈ L.C i, dT l) t := by
        simp only [ReentrantLine.idle, ReentrantLine.busy]
        exact (hasDerivAt_id' t).sub (HasDerivAt.fun_sum (fun l _ => hdT l))
      have hIn := p42_deriv_nonneg (hfs.idle_mono i) ht hId
      have hsub : L.H π k₀ ⊆ L.C i := by
        intro x hx
        simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_filter, Finset.mem_univ,
          true_and] at hx ⊢
        exact hx.1
      have hlmem : l ∈ L.C i \ L.H π k₀ := by
        simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_sdiff, Finset.mem_filter,
          Finset.mem_univ, true_and, not_and, not_le]
        exact ⟨hl, fun _ => hlt⟩
      have hsplit := Finset.sum_sdiff hsub (f := dT)
      have hle : dT l ≤ ∑ x ∈ L.C i \ L.H π k₀, dT x :=
        Finset.single_le_sum (f := dT) (fun x _ => hdT_nonneg x) hlmem
      have hdl : dT l = 0 := le_antisymm (by linarith) (hdT_nonneg l)
      simp [ReentrantLine.outRate, hdl]
