-- Prove2me | solution 1 for DaiWeissFluid.FBFS.inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:48:46.450913+00:00
-- url     : https://prove2.me/submissions/b660948f-14c2-49a0-9c8d-fa003e6ee83e

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_FBFS_prop4_2
import Theorems.Thm_DaiWeissFluid_FBFS_lemma2_2_ii

namespace DaiWeissFluid.FBFS

open Set Filter Topology

/-- Each `T_k` is nondecreasing and 1-Lipschitz on `[0, ∞)`. -/
lemma fbfs_is_T_lip {I K : ℕ} (L : ReentrantLine I K) (Q T : ℝ → Fin K → ℝ)
    (hfs : L.IsFluidSolution Q T) (k : Fin K) (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    0 ≤ T x k - T y k ∧ T x k - T y k ≤ x - y := by
  have hx : 0 ≤ x := le_trans hy hxy
  have hmono : ∀ l, T y l ≤ T x l := fun l => hfs.T_mono l hy hx hxy
  refine ⟨by linarith [hmono k], ?_⟩
  have hid := hfs.idle_mono (L.σ k) hy hx hxy
  simp only [ReentrantLine.idle, ReentrantLine.busy] at hid
  have hk : k ∈ L.C (L.σ k) := by simp [ReentrantLine.C]
  have : T x k - T y k ≤ ∑ l ∈ L.C (L.σ k), (T x l - T y l) :=
    Finset.single_le_sum (f := fun l => T x l - T y l) (fun l _ => by linarith [hmono l]) hk
  rw [Finset.sum_sub_distrib] at this
  linarith

/-- Each buffer level `Q_k` is Lipschitz on `[0, ∞)`, with constant `1 + 2 ∑_j μ_j`. -/
lemma fbfs_is_Q_lip {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (Q T : ℝ → Fin K → ℝ) (hfs : L.IsFluidSolution Q T) (k : Fin K) (x y : ℝ)
    (hy : 0 ≤ y) (hxy : y ≤ x) :
    |Q x k - Q y k| ≤ (1 + 2 * ∑ j, L.μ j) * (x - y) := by
  have hx : 0 ≤ x := le_trans hy hxy
  have hμnn : ∀ j, 0 ≤ L.μ j := fun j => inv_nonneg.mpr (hm j).le
  have hμle : ∀ j, L.μ j ≤ ∑ j, L.μ j := fun j =>
    Finset.single_le_sum (f := L.μ) (fun j _ => hμnn j) (Finset.mem_univ j)
  have hC : 0 ≤ ∑ j, L.μ j := Finset.sum_nonneg (fun j _ => hμnn j)
  have hxy0 : 0 ≤ x - y := by linarith
  have hinf : |L.inflow T k x - L.inflow T k y| ≤ (1 + ∑ j, L.μ j) * (x - y) := by
    by_cases h : (k : ℕ) = 0
    · simp only [ReentrantLine.inflow, h, dite_true]
      rw [abs_of_nonneg hxy0]; nlinarith
    · simp only [ReentrantLine.inflow, h, dite_false]
      set j : Fin K := ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩
      obtain ⟨h1, h2⟩ := fbfs_is_T_lip L Q T hfs j x y hy hxy
      rw [← mul_sub, abs_mul, abs_of_nonneg (hμnn j), abs_of_nonneg h1]
      calc L.μ j * (T x j - T y j) ≤ L.μ j * (x - y) := mul_le_mul_of_nonneg_left h2 (hμnn j)
        _ ≤ (∑ j, L.μ j) * (x - y) := mul_le_mul_of_nonneg_right (hμle j) hxy0
        _ ≤ (1 + ∑ j, L.μ j) * (x - y) := by nlinarith
  have hTk : |L.μ k * T x k - L.μ k * T y k| ≤ (∑ j, L.μ j) * (x - y) := by
    obtain ⟨h1, h2⟩ := fbfs_is_T_lip L Q T hfs k x y hy hxy
    rw [← mul_sub, abs_mul, abs_of_nonneg (hμnn k), abs_of_nonneg h1]
    calc L.μ k * (T x k - T y k) ≤ L.μ k * (x - y) := mul_le_mul_of_nonneg_left h2 (hμnn k)
      _ ≤ (∑ j, L.μ j) * (x - y) := mul_le_mul_of_nonneg_right (hμle k) hxy0
  rw [hfs.flow x hx k, hfs.flow y hy k]
  calc |Q 0 k + L.inflow T k x - L.μ k * T x k - (Q 0 k + L.inflow T k y - L.μ k * T y k)|
      = |(L.inflow T k x - L.inflow T k y) - (L.μ k * T x k - L.μ k * T y k)| := by ring_nf
    _ ≤ |L.inflow T k x - L.inflow T k y| + |L.μ k * T x k - L.μ k * T y k| := abs_sub _ _
    _ ≤ (1 + ∑ j, L.μ j) * (x - y) + (∑ j, L.μ j) * (x - y) := add_le_add hinf hTk
    _ = (1 + 2 * ∑ j, L.μ j) * (x - y) := by ring

end DaiWeissFluid.FBFS

open DaiWeissFluid.FBFS Set Filter Topology MeasureTheory in
theorem solution {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution (fbfs K) Q T)
    (k : Fin K) (τ : ℝ) (hτ : 0 ≤ τ) (hprev : ∀ t, τ ≤ t → ∀ l, l < k → Q t l = 0) :
    ∀ t, τ + Q τ k * L.m k / (1 - ∑ l ∈ L.H (fbfs K) k, L.m l) ≤ t → Q t k = 0 := by
  have hfs := hsol.1
  set S := ∑ l ∈ L.H (fbfs K) k, L.m l with hS
  have hkH : k ∈ L.H (fbfs K) k := by simp [ReentrantLine.H]
  have hS1 : S < 1 := by
    have hsub : L.H (fbfs K) k ⊆ L.C (L.σ k) := by
      intro x hx
      simp only [ReentrantLine.H, ReentrantLine.C, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx ⊢
      exact hx.1
    calc S ≤ ∑ l ∈ L.C (L.σ k), L.m l :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => (hm l).le)
      _ = L.ρ (L.σ k) := rfl
      _ < 1 := hρ _
  set ε := (1 - S) / L.m k with hεdef
  have hε : 0 < ε := div_pos (by linarith) (hm k)
  set g : ℝ → ℝ := fun s => Q (τ + s) k with hgdef
  have hgnn : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs => hfs.nonneg _ (by linarith) k
  have hμnn : ∀ j, 0 ≤ L.μ j := fun j => inv_nonneg.mpr (hm j).le
  have hC : 0 ≤ 1 + 2 * ∑ j, L.μ j :=
    add_nonneg zero_le_one (mul_nonneg zero_le_two (Finset.sum_nonneg (fun j _ => hμnn j)))
  -- absolute continuity (indeed Lipschitz continuity) of `g`
  have hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b := by
    intro a b ha hab
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal (1 + 2 * ∑ j, L.μ j))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [uIcc_of_le hab] at hx hy
    simp only [hgdef, Real.dist_eq]
    rcases le_total y x with h | h
    · have := fbfs_is_Q_lip L hm Q T hfs k (τ + x) (τ + y) (by linarith [hy.1]) (by linarith)
      rw [abs_of_nonneg (show 0 ≤ x - y by linarith)]
      exact this.trans_eq (by rw [Real.coe_toNNReal _ hC]; ring)
    · have := fbfs_is_Q_lip L hm Q T hfs k (τ + y) (τ + x) (by linarith [hx.1]) (by linarith)
      rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (show 0 ≤ y - x by linarith)]
      exact this.trans_eq (by rw [Real.coe_toNNReal _ hC]; ring)
  -- the drift condition, almost everywhere
  have hdiff : ∀ j, ∀ᵐ s ∂volume, DifferentiableAt ℝ (fun u => T (max (τ + u) 0) j) s := by
    intro j
    apply Monotone.ae_differentiableAt
    intro a b hab
    exact hfs.T_mono j (show (0:ℝ) ≤ max (τ + a) 0 from le_max_right _ _)
      (show (0:ℝ) ≤ max (τ + b) 0 from le_max_right _ _)
      (max_le_max (by linarith) le_rfl)
  have hdiffall : ∀ᵐ s ∂volume, ∀ j, DifferentiableAt ℝ (fun u => T (max (τ + u) 0) j) s :=
    ae_all_iff.mpr hdiff
  have hmμ : ∀ j, L.m j * L.μ j = 1 := fun j => by
    simp only [ReentrantLine.μ]; exact mul_inv_cancel₀ (hm j).ne'
  have hdrift : ∀ᵐ s ∂volume, 0 < s → 0 < g s → ∀ d, HasDerivAt g d s → d ≤ -ε := by
    filter_upwards [hdiffall] with s hs hs0 hgs d hd
    have ht : 0 < τ + s := by linarith
    have heq : ∀ j, (fun u => T (max (τ + u) 0) j) =ᶠ[𝓝 s] (fun u => T (τ + u) j) := by
      intro j
      filter_upwards [Ioi_mem_nhds hs0] with u hu
      simp only [mem_Ioi] at hu
      rw [max_eq_left (by linarith)]
    set dT : Fin K → ℝ := fun j => deriv (fun u => T (max (τ + u) 0) j) s with hdTdef
    have hdTs : ∀ j, HasDerivAt (fun u => T (τ + u) j) (dT j) s :=
      fun j => ((hs j).hasDerivAt).congr_of_eventuallyEq (heq j).symm
    have hdT : ∀ j, HasDerivAt (fun u => T u j) (dT j) (τ + s) := by
      intro j
      have h1 : HasDerivAt (fun u => T (τ + u) j) (dT j) ((τ + s) - τ) := by
        rw [show τ + s - τ = s by ring]; exact hdTs j
      refine (h1.comp_sub_const (τ + s) τ).congr_of_eventuallyEq ?_
      filter_upwards with x
      simp
    obtain ⟨Pb, Pc⟩ := prop4_2 L hm (fbfs K) Q T hsol (τ + s) ht dT hdT
    have hprevt : ∀ l, l < k → Q (τ + s) l = 0 := fun l hl => hprev _ (by linarith) l hl
    -- all classes before `k` flow at rate one
    have hout : ∀ n : ℕ, ∀ hn : n < (k : ℕ),
        L.outRate dT ⟨n, lt_trans hn k.isLt⟩ = 1 := by
      intro n
      induction n with
      | zero =>
        intro hn
        rw [← Pb _ (hprevt _ (by simpa [Fin.lt_def] using hn))]
        simp [ReentrantLine.inRate]
      | succ n ih =>
        intro hn
        rw [← Pb _ (hprevt _ (by simp [Fin.lt_def]; omega))]
        have hne : ((⟨n + 1, lt_trans hn k.isLt⟩ : Fin K) : ℕ) ≠ 0 := by simp
        simp only [ReentrantLine.inRate, hne, dite_false]
        exact ih (by omega)
    have hin : L.inRate dT k = 1 := by
      by_cases h : (k : ℕ) = 0
      · simp [ReentrantLine.inRate, h]
      · simp only [ReentrantLine.inRate, h, dite_false]
        exact hout _ (by omega)
    have hsum := (Pc k hgs (fun l _ hl => hprevt l (by simpa [fbfs] using hl))).1
    rw [← Finset.add_sum_erase _ _ hkH] at hsum
    have herase : ∑ l ∈ (L.H (fbfs K) k).erase k, L.m l * L.outRate dT l =
        ∑ l ∈ (L.H (fbfs K) k).erase k, L.m l := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlk : l < k := by
        have h1 := Finset.ne_of_mem_erase hl
        have h2 := Finset.mem_of_mem_erase hl
        simp only [ReentrantLine.H, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        exact lt_of_le_of_ne h2.2 h1
      have := hout l hlk
      simp only [Fin.eta] at this
      rw [this, mul_one]
    rw [herase] at hsum
    have hS' : S = L.m k + ∑ l ∈ (L.H (fbfs K) k).erase k, L.m l := by
      rw [hS, ← Finset.add_sum_erase _ _ hkH]
    -- derivative of `g`
    have hinfl : ∀ j, HasDerivAt (fun u => L.inflow T j u) (L.inRate dT j) (τ + s) := by
      intro j
      by_cases h : (j : ℕ) = 0
      · simp only [ReentrantLine.inflow, ReentrantLine.inRate, h, dite_true]
        exact hasDerivAt_id' _
      · simp only [ReentrantLine.inflow, ReentrantLine.inRate, ReentrantLine.outRate, h,
          dite_false]
        exact (hdT _).const_mul _
    have hQd : HasDerivAt (fun u => Q u k) (L.inRate dT k - L.outRate dT k) (τ + s) := by
      have h1 : HasDerivAt (fun u => Q 0 k + L.inflow T k u - L.μ k * T u k)
          (0 + L.inRate dT k - L.μ k * dT k) (τ + s) :=
        ((hasDerivAt_const _ (Q 0 k)).add (hinfl k)).sub ((hdT k).const_mul _)
      have h2 : (fun u => Q u k) =ᶠ[𝓝 (τ + s)]
          (fun u => Q 0 k + L.inflow T k u - L.μ k * T u k) := by
        filter_upwards [Ioi_mem_nhds ht] with u hu
        exact hfs.flow u (le_of_lt hu) k
      have := h1.congr_of_eventuallyEq h2
      simpa [ReentrantLine.outRate] using this
    have hgd : HasDerivAt g (L.inRate dT k - L.outRate dT k) s := hQd.comp_const_add τ s
    have hdeq : d = 1 - L.outRate dT k := by rw [hd.unique hgd, hin]
    rw [hdeq, hεdef]
    have hmk := hm k
    have hkey : L.m k * L.outRate dT k = 1 - (S - L.m k) := by linarith
    have hout_k : L.outRate dT k = (1 - S + L.m k) / L.m k := by
      field_simp; linarith
    rw [hout_k]
    apply le_of_eq
    field_simp
    ring
  obtain ⟨hzero, _⟩ := lemma2_2_ii g hac hgnn ε hε hdrift
  intro t ht
  have h0 : g 0 / ε ≤ t - τ := by
    simp only [hgdef, add_zero, hεdef]
    rw [div_div_eq_mul_div]
    linarith
  have := hzero (t - τ) h0
  simpa [hgdef] using this
