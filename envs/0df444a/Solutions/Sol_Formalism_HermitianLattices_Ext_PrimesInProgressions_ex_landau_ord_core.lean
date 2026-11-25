-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_landau_ord_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:09.01519+00:00
-- url     : https://prove2.me/submissions/f90f8bf3-6d93-45da-a209-3f7a49e6b985

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLoc
import Theorems.Thm_Formalism_ZF_landauLocal
import Theorems.Thm_Formalism_ZF_landauLocal_logDeriv_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
private theorem zeros_in_closedBall_finite_of_analyticOnNhd (f : ℂ → ℂ) (z₀ : ℂ) (r s : ℝ) (hs : s < r)
    (hfa : AnalyticOnNhd ℂ f (Metric.ball z₀ r)) (hfz₀ : f z₀ ≠ 0) :
    {ρ | ρ ∈ Metric.closedBall z₀ s ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall z₀ s) (fun y hy => hy.1)
  have hxd : dist x z₀ ≤ s := Metric.mem_closedBall.mp hxK
  have hxU : x ∈ Metric.ball z₀ r := Metric.mem_ball.mpr (lt_of_le_of_lt hxd hs)
  have hfreq : ∃ᶠ y in nhdsWithin x {x}ᶜ, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun y hy => hy.2)
  have hz0 : z₀ ∈ Metric.ball z₀ r :=
    Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg (lt_of_le_of_lt hxd hs))
  exact hfz₀ (hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball z₀ r).isPreconnected hxU hfreq hz0)
private theorem exists_factor_zeros_differentiableOn_nonvanishing (f : ℂ → ℂ) (K : Set ℂ) (Z : Finset ℂ)
    (hd : DifferentiableOn ℂ f K) (hZ0 : ∀ ρ ∈ Z, f ρ = 0)
    (hfa : ∀ ρ ∈ Z, AnalyticAt ℂ f ρ) (hfin : ∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤)
    (hn : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g K ∧
      (∀ z ∈ K, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * g z) ∧
      (∀ ρ ∈ Z, g ρ ≠ 0) := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ :=
    ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    fun_prop
  have hPne : ∀ w, w ∉ Z → P w ≠ 0 := by
    intro w hw
    rw [hP, Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hw (h ▸ hρ)))
  have hPz : ∀ ρ ∈ Z, P ρ = 0 := by
    intro ρ hρ
    rw [hP]
    exact Finset.prod_eq_zero hρ (by rw [sub_self]; exact zero_pow (by have := hn ρ hρ; omega))
  have hloc : ∀ ρ ∈ Z, ∃ k : ℂ → ℂ, DifferentiableAt ℂ k ρ ∧ k ρ ≠ 0 ∧
      ∀ᶠ w in nhdsWithin ρ {ρ}ᶜ, f w / P w = k w := by
    intro ρ hρ
    obtain ⟨h, hha, hhne, hfeq⟩ := (hfa ρ hρ).analyticOrderAt_ne_top.mp (hfin ρ hρ)
    obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ, Q = fun w => ∏ σ ∈ Z.erase ρ, (w - σ) ^ analyticOrderNatAt f σ :=
      ⟨_, rfl⟩
    have hQρ : Q ρ ≠ 0 := by
      rw [hQ, Finset.prod_ne_zero_iff]
      intro σ hσ
      exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hσ) h.symm))
    have hQd : Differentiable ℂ Q := by
      rw [hQ]
      fun_prop
    have hPQ : ∀ w, P w = (w - ρ) ^ analyticOrderNatAt f ρ * Q w := by
      intro w
      rw [hP, hQ]
      exact (Finset.mul_prod_erase Z (fun σ => (w - σ) ^ analyticOrderNatAt f σ) hρ).symm
    refine ⟨fun w => h w / Q w, hha.differentiableAt.div (hQd ρ) hQρ, div_ne_zero hhne hQρ, ?_⟩
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hfeq] with w hw hfw
    rw [hfw, hPQ, smul_eq_mul]
    have h1 : (w - ρ) ^ analyticOrderNatAt f ρ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
    rw [mul_div_mul_left _ _ h1]
  choose! k hkd hkne hkeq using hloc
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun w => if w ∈ Z then k w w else f w / P w := ⟨_, rfl⟩
  have hgk : ∀ ρ ∈ Z, g =ᶠ[nhds ρ] k ρ := by
    intro ρ hρ
    have hopen : IsOpen ((↑(Z.erase ρ) : Set ℂ)ᶜ) :=
      (Finset.finite_toSet _).isClosed.isOpen_compl
    have hmem : ρ ∈ ((↑(Z.erase ρ) : Set ℂ)ᶜ) := by simp
    filter_upwards [hopen.mem_nhds hmem, eventually_nhdsWithin_iff.mp (hkeq ρ hρ)] with w hw1 hw2
    by_cases hwρ : w = ρ
    · rw [hwρ, hg]
      simp [hρ]
    · have hwZ : w ∉ Z := by
        intro hwZ
        exact hw1 (by simp [Finset.mem_erase, hwρ, hwZ])
      rw [hg]
      simp only [if_neg hwZ]
      exact hw2 hwρ
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzZ : z ∈ Z
    · exact ((hkd z hzZ).congr_of_eventuallyEq (hgk z hzZ)).differentiableWithinAt
    · have hopen : IsOpen ((↑Z : Set ℂ)ᶜ) := (Finset.finite_toSet _).isClosed.isOpen_compl
      have hev : g =ᶠ[nhdsWithin z K] fun w => f w / P w := by
        filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds (by simpa using hzZ))] with w hw
        rw [hg]
        simp only [if_neg (show w ∉ Z by simpa using hw)]
      refine ((hd z hz).div (hPd z).differentiableWithinAt (hPne z hzZ)).congr_of_eventuallyEq hev ?_
      rw [hg]
      simp only [if_neg hzZ]
      rfl
  · intro z hz
    have hPe : (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) = P z := by rw [hP]
    rw [hPe]
    by_cases hzZ : z ∈ Z
    · rw [hZ0 z hzZ, hPz z hzZ, zero_mul]
    · rw [hg]
      simp only [if_neg hzZ]
      rw [mul_div_cancel₀ _ (hPne z hzZ)]
  · intro ρ hρ
    rw [(hgk ρ hρ).self_of_nhds]
    exact hkne ρ hρ
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
open Filter Topology Metric
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 1 ≤ B)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log B / r := by
  classical
  have hr3 : r / 3 < r := by linarith
  have hball : DifferentiableOn ℂ f (Metric.ball z₀ r) := hf.mono Metric.ball_subset_closedBall
  have hfa : AnalyticOnNhd ℂ f (Metric.ball z₀ r) := hball.analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hfin := zeros_in_closedBall_finite_of_analyticOnNhd f z₀ r (r / 3) hr3 hfa hfz₀
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℂ, Z = hfin.toFinset := ⟨_, rfl⟩
  have hZmem : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0) := by
    intro ρ
    rw [hZdef, Set.Finite.mem_toFinset]
    rfl
  have hZball : ∀ ρ ∈ Z, ρ ∈ Metric.ball z₀ r := fun ρ hρ =>
    Metric.closedBall_subset_ball hr3 ((hZmem ρ).mp hρ).1
  have hord0 : analyticOrderAt f z₀ ≠ ⊤ := by
    rw [(hfa z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀]
    exact ENat.zero_ne_top
  have hfinord : ∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤ := fun ρ hρ =>
    hfa.analyticOrderAt_ne_top_of_isPreconnected (convex_ball z₀ r).isPreconnected hz₀
      (hZball ρ hρ) hord0
  have hn1 : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ := by
    intro ρ hρ
    have h1 : analyticOrderAt f ρ ≠ 0 :=
      (hfa ρ (hZball ρ hρ)).analyticOrderAt_ne_zero.mpr ((hZmem ρ).mp hρ).2
    have h2 := Nat.cast_analyticOrderNatAt (hfinord ρ hρ)
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0] at h2
    exact h1 (by rw [← h2]; simp)
  obtain ⟨g, hgd, hfg, hgZ⟩ := exists_factor_zeros_differentiableOn_nonvanishing f (Metric.closedBall z₀ r) Z hf
    (fun ρ hρ => ((hZmem ρ).mp hρ).2) (fun ρ hρ => hfa ρ (hZball ρ hρ)) hfinord hn1
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun w => ∏ ρ ∈ Z, (w - ρ) ^ analyticOrderNatAt f ρ :=
    ⟨_, rfl⟩
  have hfP : ∀ z ∈ Metric.closedBall z₀ r, f z = P z * g z := by
    intro z hz
    rw [hP]
    exact hfg z hz
  have hPne : ∀ w, w ∉ Z → P w ≠ 0 := by
    intro w hw
    rw [hP, Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hw (h ▸ hρ)))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ∑ ρ ∈ Z, analyticOrderNatAt f ρ := ⟨_, rfl⟩
  have hz₀c : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hz₀Z : z₀ ∉ Z := fun h => hfz₀ ((hZmem z₀).mp h).2
  have hgz₀ : g z₀ ≠ 0 := by
    intro h
    apply hfz₀
    rw [hfP z₀ hz₀c, h, mul_zero]
  have hgpos : 0 < ‖g z₀‖ := norm_pos_iff.mpr hgz₀
  have hr3pos : 0 < r / 3 := by positivity
  have hPz₀ : ‖P z₀‖ ≤ (r / 3) ^ N := by
    rw [hP, norm_prod, hN, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod
    · intro ρ _
      positivity
    · intro ρ hρ
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have := Metric.mem_closedBall.mp ((hZmem ρ).mp hρ).1
      rw [← dist_eq_norm, dist_comm]
      exact this
  have hPsph : ∀ z ∈ Metric.sphere z₀ r, 2 ^ N * (r / 3) ^ N ≤ ‖P z‖ := by
    intro z hz
    have hzd : dist z z₀ = r := Metric.mem_sphere.mp hz
    rw [← mul_pow, hP, norm_prod, hN, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod
    · intro ρ _
      positivity
    · intro ρ hρ
      rw [norm_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hρd := Metric.mem_closedBall.mp ((hZmem ρ).mp hρ).1
      have htri := dist_triangle z ρ z₀
      rw [← dist_eq_norm]
      linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = B / 2 ^ N := ⟨_, rfl⟩
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hsph : ∀ z ∈ Metric.sphere z₀ r, ‖g z‖ ≤ M * ‖g z₀‖ := by
    intro z hz
    have hzc : z ∈ Metric.closedBall z₀ r := Metric.sphere_subset_closedBall hz
    have hPpos : 0 < 2 ^ N * (r / 3) ^ N := by positivity
    have hfz := hbound z hzc
    rw [hfP z hzc, hfP z₀ hz₀c, norm_mul, norm_mul] at hfz
    have h1 : ‖g z‖ * (2 ^ N * (r / 3) ^ N) ≤ ‖g z‖ * ‖P z‖ :=
      mul_le_mul_of_nonneg_left (hPsph z hz) (norm_nonneg _)
    have h2 : B * (‖P z₀‖ * ‖g z₀‖) ≤ B * ((r / 3) ^ N * ‖g z₀‖) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hPz₀ (norm_nonneg _)
    have h3 : ‖g z‖ * (2 ^ N * (r / 3) ^ N) ≤ (M * ‖g z₀‖) * (2 ^ N * (r / 3) ^ N) := by
      have : (M * ‖g z₀‖) * (2 ^ N * (r / 3) ^ N) = B * ((r / 3) ^ N * ‖g z₀‖) := by
        rw [hM]
        field_simp
      rw [this]
      linarith [mul_comm (‖P z‖) (‖g z‖)]
    exact le_of_mul_le_mul_right h3 hPpos
  have hgcl : DiffContOnCl ℂ g (Metric.ball z₀ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact hgd
  have hmax : ∀ z ∈ Metric.closedBall z₀ r, ‖g z‖ ≤ M * ‖g z₀‖ := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgcl
    · rw [frontier_ball z₀ hr.ne']
      exact hsph
    · rw [closure_ball z₀ hr.ne']
      exact hz
  have hM1 : 1 ≤ M := by
    have := hmax z₀ hz₀c
    nlinarith
  have h2B : (2 : ℝ) ^ N ≤ B := by
    rw [hM, le_div_iff₀ h2N, one_mul] at hM1
    exact hM1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcount : (N : ℝ) ≤ Real.log B / Real.log 2 := by
    rw [le_div_iff₀ hlog2, ← Real.log_pow]
    exact Real.log_le_log h2N h2B
  have hMB : Real.log M ≤ Real.log B := by
    apply Real.log_le_log (by linarith)
    rw [hM]
    exact div_le_self (by linarith) (one_le_pow₀ one_le_two)
  have hgS : ∀ z ∈ Metric.closedBall z₀ (r / 3), g z ≠ 0 := by
    intro z hz hgz
    by_cases hzZ : z ∈ Z
    · exact hgZ z hzZ hgz
    · apply hzZ
      rw [hZmem]
      refine ⟨hz, ?_⟩
      rw [hfP z (Metric.closedBall_subset_closedBall hr3.le hz), hgz, mul_zero]
  obtain ⟨Z', m', hZ', -, -, hest⟩ := Formalism.ZF.landauLocal g z₀ r M hr hM1 hgd hgz₀ hmax
  have hZ'e : Z' = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    exact hgS ρ ((hZ' ρ).mp hρ).1 ((hZ' ρ).mp hρ).2
  refine ⟨Z, fun ρ => analyticOrderNatAt f ρ, hZmem, hn1, fun ρ _ => rfl, ?_, ?_⟩
  · rw [← hN]
    exact hcount
  · intro z hz hfz
    have hr6 : r / 6 < r := by linarith
    have hzb : z ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hr6 hz
    have hzc : z ∈ Metric.closedBall z₀ r := Metric.ball_subset_closedBall hzb
    have hzZ : z ∉ Z := fun h => hfz ((hZmem z).mp h).2
    have hgz : g z ≠ 0 := by
      intro h
      apply hfz
      rw [hfP z hzc, h, mul_zero]
    have hPz : P z ≠ 0 := hPne z hzZ
    have hnhd : Metric.closedBall z₀ r ∈ 𝓝 z :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hzb) Metric.ball_subset_closedBall
    have hgdz : DifferentiableAt ℂ g z := hgd.differentiableAt hnhd
    have hPdz : DifferentiableAt ℂ P z := by
      rw [hP]
      fun_prop
    have hev : f =ᶠ[𝓝 z] fun w => P w * g w := by
      filter_upwards [hnhd] with w hw
      exact hfP w hw
    have hderiv : deriv f z = deriv P z * g z + P z * deriv g z := by
      rw [hev.deriv_eq]
      exact deriv_mul hPdz hgdz
    have hlog : deriv P z / P z = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) := by
      rw [← logDeriv_apply, hP]
      apply Formalism.ZF.landauLocal_logDeriv_prod
      intro ρ hρ h
      exact hzZ (by rw [sub_eq_zero] at h; rw [h]; exact hρ)
    have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) =
        deriv g z / g z := by
      rw [← hlog, hderiv, hfP z hzc]
      field_simp
      ring
    have hg6 := hest z hz hgz
    rw [hZ'e, Finset.sum_empty, sub_zero] at hg6
    rw [hsplit]
    calc ‖deriv g z / g z‖ ≤ 72 * Real.log M / r := hg6
      _ ≤ 72 * Real.log B / r := by
        apply div_le_div_of_nonneg_right _ hr.le
        linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
