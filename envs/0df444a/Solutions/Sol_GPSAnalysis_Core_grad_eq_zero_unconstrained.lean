-- Prove2me | solution 1 for GPSAnalysis.Core.grad_eq_zero_unconstrained
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:59:57.526385+00:00
-- url     : https://prove2.me/submissions/2433dcec-2127-4048-ab3a-6ba454eaa82d

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke

set_option autoImplicit false

open Filter Topology in
theorem GPSAnalysis.Core.Sol_pv_a6bd8bb1_Δpos {n m p : ℕ} {P : GPSAnalysis.Core.GPSSetup n m p}
    (R : GPSAnalysis.Core.GPSRun P) : ∀ k, 0 < R.Δ k := by
  intro k
  induction k with
  | zero => exact R.Δ_zero_pos
  | succ k ih =>
    rw [R.Δ_succ k]
    have hτ : (0 : ℝ) < (P.τ : ℝ) := by
      have := P.one_lt_τ
      have h1 : (1 : ℝ) < (P.τ : ℝ) := by exact_mod_cast this
      linarith
    exact mul_pos (zpow_pos hτ _) ih

open Filter Topology GPSAnalysis.Core in
theorem solution {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hΩ : P.Ω = Set.univ) (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U)
    (grad : Fin n → ℝ) (hgrad : HasStrictDirGradAt g grad xhat) :
    grad = 0 := by
  have hpos := GPSAnalysis.Core.Sol_pv_a6bd8bb1_Δpos R
  have hΔ : Tendsto (fun i => R.Δ (K i)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hK.2.2, Eventually.of_forall fun i => hpos (K i)⟩
  have hφ : Tendsto (fun i => (R.x (K i), R.Δ (K i))) atTop (𝓝 xhat ×ˢ 𝓝[>] (0 : ℝ)) :=
    hlim.prodMk hΔ
  -- for each direction j, the poll condition gives a nonneg difference quotient
  have key : ∀ j : Fin p, (∃ᶠ i in atTop, j ∈ R.Dk (K i)) → 0 ≤ grad ⬝ᵥ P.dir j := by
    intro j hj
    have hpoll : Tendsto (fun i => R.x (K i) + R.Δ (K i) • P.dir j) atTop (𝓝 xhat) := by
      have := hlim.add (hK.2.2.smul_const (P.dir j))
      simpa using this
    have hevU : ∀ᶠ i in atTop, R.x (K i) ∈ U ∧ R.x (K i) + R.Δ (K i) • P.dir j ∈ U :=
      (hlim.eventually hU).and (hpoll.eventually hU)
    have hfreq : ∃ᶠ i in atTop, (fun i => (g (R.x (K i) + R.Δ (K i) • P.dir j)
        - g (R.x (K i))) / R.Δ (K i)) i ∈ Set.Ici (0 : ℝ) := by
      refine (hj.and_eventually hevU).mono ?_
      rintro i ⟨hjD, hxU, hpU⟩
      have hopt := ((R.localOpt (K i) (hK.2.1 i)).1 j hjD)
      have hmem : ∀ y, y ∈ P.Ω := fun y => by rw [hΩ]; trivial
      have hfp : P.fΩ (R.x (K i) + R.Δ (K i) • P.dir j)
          = (g (R.x (K i) + R.Δ (K i) • P.dir j) : WithTop ℝ) := by
        unfold GPSAnalysis.Core.GPSSetup.fΩ GPSAnalysis.Core.barrier
        rw [if_pos (hmem _), hfg _ hpU]
      have hfx : P.fΩ (R.x (K i)) = (g (R.x (K i)) : WithTop ℝ) := by
        unfold GPSAnalysis.Core.GPSSetup.fΩ GPSAnalysis.Core.barrier
        rw [if_pos (hmem _), hfg _ hxU]
      rw [hfp, hfx] at hopt
      have hle : g (R.x (K i)) ≤ g (R.x (K i) + R.Δ (K i) • P.dir j) :=
        WithTop.coe_le_coe.mp hopt
      show (0 : ℝ) ≤ _
      exact div_nonneg (by linarith) (hpos (K i)).le
    have ht : Tendsto (fun i => (g (R.x (K i) + R.Δ (K i) • P.dir j)
        - g (R.x (K i))) / R.Δ (K i)) atTop (𝓝 (grad ⬝ᵥ P.dir j)) :=
      (hgrad (P.dir j)).comp hφ
    exact isClosed_Ici.mem_of_frequently_of_tendsto hfreq ht
  -- pigeonhole: some poll set recurs
  obtain ⟨D', hD'⟩ : ∃ D' : Finset (Fin p), ∃ᶠ i in atTop, R.Dk (K i) = D' := by
    by_contra hcon
    simp only [not_exists, Filter.not_frequently] at hcon
    have hall : ∀ᶠ i in atTop, ∀ D' : Finset (Fin p), R.Dk (K i) ≠ D' :=
      Filter.eventually_all.2 hcon
    obtain ⟨i, hi⟩ := hall.exists
    exact hi _ rfl
  have hD'nonneg : ∀ j ∈ D', 0 ≤ grad ⬝ᵥ P.dir j := by
    intro j hj
    apply key j
    exact hD'.mono fun i hi => by rw [hi]; exact hj
  have hspan := R.Dk_posSpanning
  -- recurring D' is positive spanning
  obtain ⟨i0, hi0⟩ := hD'.exists
  have hsp : IsPositiveSpanning P.D D' := hi0 ▸ hspan (K i0)
  have hmem : -grad ∈ nonnegSpan P.D D' := by rw [hsp]; trivial
  obtain ⟨c, hc, hceq⟩ := hmem
  have h1 : grad ⬝ᵥ (-grad) = ∑ j ∈ D', c j * (grad ⬝ᵥ P.dir j) := by
    rw [hceq, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    rfl
  have h2 : 0 ≤ ∑ j ∈ D', c j * (grad ⬝ᵥ P.dir j) :=
    Finset.sum_nonneg fun j hj => mul_nonneg (hc j) (hD'nonneg j hj)
  rw [dotProduct_neg] at h1
  have h3 : grad ⬝ᵥ grad ≤ 0 := by linarith
  have h4 : 0 ≤ grad ⬝ᵥ grad := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (grad i)
  exact dotProduct_self_eq_zero.1 (le_antisymm h3 h4)
