-- Prove2me | solution 1 for DaiWeissFluid.LBFS.emptying_time
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:31:31.336243+00:00
-- url     : https://prove2.me/submissions/2c4c8763-1a86-4071-ab37-439d5647ba54

import Mathlib
import Definitions.Def_DaiWeissFluid_LBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_LBFS_drift_bound
import Theorems.Thm_DaiWeissFluid_LBFS_lemma2_2_ii

namespace DaiWeissFluid.LBFS

open Set Filter Topology

lemma et_inflow_sum {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (T : ℝ → Fin (K' + 1) → ℝ)
    (s : ℝ) :
    ∑ k, L.inflow T k s = s + ∑ i : Fin K', L.μ i.castSucc * T s i.castSucc := by
  have h0 : L.inflow T 0 s = s := by simp [ReentrantLine.inflow]
  rw [Fin.sum_univ_succ, h0]
  refine congrArg (s + ·) (Finset.sum_congr rfl ?_)
  intro i _
  have h1 : ((i.succ : Fin (K' + 1)) : ℕ) ≠ 0 := by simp
  simp only [ReentrantLine.inflow, h1, dite_false]
  have h2 : (⟨((i.succ : Fin (K' + 1)) : ℕ) - 1, by omega⟩ : Fin (K' + 1)) = i.castSucc := by
    ext; simp
  rw [h2]

lemma et_total {I K' : ℕ} (L : ReentrantLine I (K' + 1)) (Q T : ℝ → Fin (K' + 1) → ℝ)
    (hfs : L.IsFluidSolution Q T) (s : ℝ) (hs : 0 ≤ s) :
    ∑ k, Q s k = ∑ k, Q 0 k + s - L.μ (Fin.last K') * T s (Fin.last K') := by
  rw [Finset.sum_congr rfl (fun k _ => hfs.flow s hs k), Finset.sum_sub_distrib,
    Finset.sum_add_distrib, et_inflow_sum,
    Fin.sum_univ_castSucc (f := fun x => L.μ x * T s x)]
  ring

/-- Each `T_k` is 1-Lipschitz on `[0, ∞)`. -/
lemma et_T_lip {I K : ℕ} (L : ReentrantLine I K) (Q T : ℝ → Fin K → ℝ)
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

end DaiWeissFluid.LBFS

open DaiWeissFluid.LBFS Set Filter Topology MeasureTheory in
theorem solution {I K : ℕ} (L : DaiWeissFluid.LBFS.ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hρ : ∀ i, L.ρ i < 1) (hK : 0 < K)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution Fin.revPerm Q T) :
    ∀ t, (∑ k, Q 0 k) / (L.lamHat - 1) ≤ t → ∀ k, Q t k = 0 := by
  have hfs := hsol.1
  -- 1 < λ̂
  have hlam1 : 1 < L.lamHat := by
    have k0 : Fin K := ⟨0, hK⟩
    have : Nonempty (Fin I) := ⟨L.σ k0⟩
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := L.ρ)
    have hk0 : k0 ∈ L.C (L.σ k0) := by simp [ReentrantLine.C]
    have hρpos : 0 < L.ρ (L.σ k0) :=
      lt_of_lt_of_le (hm k0) (Finset.single_le_sum (f := L.m) (fun k _ => (hm k).le) hk0)
    have hle : L.ρ (L.σ k0) ≤ ⨆ i : Fin I, L.ρ i := le_ciSup (Finite.bddAbove_range _) _
    have hMpos : 0 < ⨆ i : Fin I, L.ρ i := lt_of_lt_of_le hρpos hle
    have hM1 : (⨆ i : Fin I, L.ρ i) < 1 := by rw [← hi₀]; exact hρ i₀
    show 1 < 1 / ⨆ i : Fin I, L.ρ i
    rw [lt_div_iff₀ hMpos]; linarith
  set ε := L.lamHat - 1 with hεdef
  have hε : 0 < ε := by linarith
  set g : ℝ → ℝ := fun s => ∑ k, Q s k with hgdef
  have hgnn : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs =>
    Finset.sum_nonneg (fun k _ => hfs.nonneg s hs k)
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  -- absolute continuity of g on [a, b] ⊆ [0, ∞)
  have hac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval g a b := by
    intro a b ha hab
    set μK := L.μ (Fin.last K')
    have hμK : 0 ≤ μK := inv_nonneg.mpr (hm _).le
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨1 + μK, by positivity⟩)
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [uIcc_of_le hab] at hx hy
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have hy0 : 0 ≤ y := le_trans ha hy.1
    simp only [hgdef, Real.dist_eq]
    rw [et_total L Q T hfs x hx0, et_total L Q T hfs y hy0]
    have hTl : |T x (Fin.last K') - T y (Fin.last K')| ≤ |x - y| := by
      rcases le_total y x with h | h
      · obtain ⟨h1, h2⟩ := et_T_lip L Q T hfs (Fin.last K') x y hy0 h
        rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; exact h2
      · obtain ⟨h1, h2⟩ := et_T_lip L Q T hfs (Fin.last K') y x hx0 h
        rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]
        exact h2
    calc |∑ k, Q 0 k + x - μK * T x (Fin.last K') - (∑ k, Q 0 k + y - μK * T y (Fin.last K'))|
        = |(x - y) - μK * (T x (Fin.last K') - T y (Fin.last K'))| := by ring_nf
      _ ≤ |x - y| + |μK * (T x (Fin.last K') - T y (Fin.last K'))| := abs_sub _ _
      _ = |x - y| + μK * |T x (Fin.last K') - T y (Fin.last K')| := by
          rw [abs_mul, abs_of_nonneg hμK]
      _ ≤ |x - y| + μK * |x - y| := by gcongr
      _ = (1 + μK) * |x - y| := by ring
  -- the drift condition almost everywhere
  have hdiff : ∀ k, ∀ᵐ s ∂volume, DifferentiableAt ℝ (fun u => T (max u 0) k) s := by
    intro k
    apply Monotone.ae_differentiableAt
    intro a b hab
    exact hfs.T_mono k (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
  have hdiffall : ∀ᵐ s ∂volume, ∀ k, DifferentiableAt ℝ (fun u => T (max u 0) k) s :=
    ae_all_iff.mpr hdiff
  have hdrift : ∀ᵐ t ∂volume, 0 < t → 0 < g t → ∀ d, HasDerivAt g d t → d ≤ -ε := by
    filter_upwards [hdiffall] with t ht htpos hgt d hd
    have heq : ∀ k, (fun u => T (max u 0) k) =ᶠ[𝓝 t] (fun u => T u k) := by
      intro k
      filter_upwards [Ioi_mem_nhds htpos] with u hu
      simp only [mem_Ioi] at hu
      rw [max_eq_left hu.le]
    have hdT : ∀ k, HasDerivAt (fun s => T s k) (deriv (fun u => T (max u 0) k) t) t :=
      fun k => ((ht k).hasDerivAt).congr_of_eventuallyEq ((heq k).symm)
    have := (drift_bound L hm hρ hK Q T hsol t htpos _ hdT hgt d hd).1
    linarith
  obtain ⟨hzero, _⟩ := lemma2_2_ii g hac hgnn ε hε hdrift
  intro t ht k
  have hg0 : 0 ≤ g 0 := hgnn 0 le_rfl
  have ht0 : 0 ≤ t := le_trans (div_nonneg hg0 hε.le) ht
  have hgt : g t = 0 := hzero t ht
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hfs.nonneg t ht0 k)).mp hgt k
    (Finset.mem_univ _)
  exact this
