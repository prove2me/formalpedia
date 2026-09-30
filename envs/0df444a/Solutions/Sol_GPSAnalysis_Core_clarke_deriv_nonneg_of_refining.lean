-- Prove2me | solution 1 for GPSAnalysis.Core.clarke_deriv_nonneg_of_refining
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-29T22:28:09.211141+00:00
-- url     : https://prove2.me/submissions/e91a831d-6592-409f-ba66-51752d5ccebf

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke

set_option autoImplicit false

open Filter Topology in
theorem GPSAnalysis.Core.Sol_pv_3b72b0c3_Δpos {n m p : ℕ} {P : GPSAnalysis.Core.GPSSetup n m p}
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

open Filter Topology in
theorem solution {n m p : ℕ} (P : GPSAnalysis.Core.GPSSetup n m p) (R : GPSAnalysis.Core.GPSRun P)
    (hA1 : GPSAnalysis.Core.AssumptionA1 R) (hA2 : GPSAnalysis.Core.AssumptionA2 P)
    (hA3 : GPSAnalysis.Core.AssumptionA3 R)
    (K : ℕ → ℕ) (hK : GPSAnalysis.Core.IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (j : Fin p)
    (hj : ∃ᶠ i in atTop, j ∈ R.Dk (K i) ∧ R.x (K i) + R.Δ (K i) • P.dir j ∈ P.Ω)
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U) :
    0 ≤ GPSAnalysis.Core.clarkeDirDeriv g xhat (P.dir j) := by
  have hpos := GPSAnalysis.Core.Sol_pv_3b72b0c3_Δpos R
  have hΔ : Tendsto (fun i => R.Δ (K i)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hK.2.2, Eventually.of_forall fun i => hpos (K i)⟩
  have hφ : Tendsto (fun i => (R.x (K i), R.Δ (K i))) atTop (𝓝 xhat ×ˢ 𝓝[>] (0 : ℝ)) :=
    hlim.prodMk hΔ
  have hpoll : Tendsto (fun i => R.x (K i) + R.Δ (K i) • P.dir j) atTop (𝓝 xhat) := by
    have := hlim.add (hK.2.2.smul_const (P.dir j))
    simpa using this
  have hevU : ∀ᶠ i in atTop, R.x (K i) ∈ U ∧ R.x (K i) + R.Δ (K i) • P.dir j ∈ U :=
    (hlim.eventually (mem_nhds_iff.mp hU |> fun _ => hU)).and (hpoll.eventually hU)
  have hfreq : ∃ᶠ i in atTop, (0 : EReal) ≤
      (((g ((R.x (K i), R.Δ (K i)).1 + (R.x (K i), R.Δ (K i)).2 • P.dir j)
        - g (R.x (K i), R.Δ (K i)).1) / (R.x (K i), R.Δ (K i)).2 : ℝ) : EReal) := by
    refine (hj.and_eventually hevU).mono ?_
    rintro i ⟨⟨hjD, hΩ⟩, hxU, hpU⟩
    have hopt := ((R.localOpt (K i) (hK.2.1 i)).1 j hjD)
    have hfp : P.fΩ (R.x (K i) + R.Δ (K i) • P.dir j) = (g (R.x (K i) + R.Δ (K i) • P.dir j) : WithTop ℝ) := by
      unfold GPSAnalysis.Core.GPSSetup.fΩ GPSAnalysis.Core.barrier
      rw [if_pos hΩ, hfg _ hpU]
    rw [hfp] at hopt
    have hxΩ : R.x (K i) ∈ P.Ω := by
      by_contra hn
      have : P.fΩ (R.x (K i)) = ⊤ := by
        unfold GPSAnalysis.Core.GPSSetup.fΩ GPSAnalysis.Core.barrier
        rw [if_neg hn]
      rw [this] at hopt
      exact absurd hopt (by simp)
    have hfx : P.fΩ (R.x (K i)) = (g (R.x (K i)) : WithTop ℝ) := by
      unfold GPSAnalysis.Core.GPSSetup.fΩ GPSAnalysis.Core.barrier
      rw [if_pos hxΩ, hfg _ hxU]
    rw [hfx] at hopt
    have hle : g (R.x (K i)) ≤ g (R.x (K i) + R.Δ (K i) • P.dir j) := WithTop.coe_le_coe.mp hopt
    have : (0 : ℝ) ≤ (g (R.x (K i) + R.Δ (K i) • P.dir j) - g (R.x (K i))) / R.Δ (K i) :=
      div_nonneg (by linarith) (hpos (K i)).le
    exact_mod_cast this
  have hfreq2 : ∃ᶠ q in 𝓝 xhat ×ˢ 𝓝[>] (0 : ℝ), (0 : EReal) ≤
      (((g (q.1 + q.2 • P.dir j) - g q.1) / q.2 : ℝ) : EReal) :=
    hφ.frequently (p := fun q : (Fin n → ℝ) × ℝ => (0 : EReal) ≤
      (((g (q.1 + q.2 • P.dir j) - g q.1) / q.2 : ℝ) : EReal)) hfreq
  unfold GPSAnalysis.Core.clarkeDirDeriv
  exact le_limsup_of_frequently_le hfreq2
