-- Prove2me | solution 1 for BootRobust.Optimality.inf_N_lt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:08:50.006478+00:00
-- url     : https://prove2.me/submissions/d58ff887-067d-4ab9-b16a-bf3492e9de33

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

set_option autoImplicit false
open BootRobust.Optimality

theorem bro_bd {ι : Type*} [Fintype ι] [DecidableEq ι] (Dtr : ι → ℝ) (hpos : ∀ i, 0 < Dtr i)
    (E : ι → ℝ) :
    BootRobust.Perf.bootDist E Dtr = ((∑ i, E i * Real.log (E i / Dtr i) : ℝ) : EReal) := by
  unfold BootRobust.Perf.bootDist
  rw [if_pos]
  intro i hi
  exact absurd hi (hpos i).ne'

theorem bro_key {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    (lam • D + (1 - lam) • Dtr) i * Real.log ((lam • D + (1 - lam) • Dtr) i / Dtr i) ≤
      lam * (D i * Real.log (D i / Dtr i)) := by
  have hp := hDtrpos i
  have hDi : 0 ≤ D i := hD.1 i
  have ha : 0 ≤ D i / Dtr i := div_nonneg hDi hp.le
  have hcv := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (zero_le_one' ℝ))
    hlam.1 (sub_nonneg.mpr hlam.2) (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at hcv
  have e1 : (lam • D + (1 - lam) • Dtr) i = Dtr i * (lam * (D i / Dtr i) + (1 - lam)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have e2 : (lam • D + (1 - lam) • Dtr) i / Dtr i = lam * (D i / Dtr i) + (1 - lam) := by
    rw [e1]; field_simp
  rw [e2, e1]
  have h3 : Dtr i * ((lam * (D i / Dtr i) + (1 - lam)) * Real.log (lam * (D i / Dtr i) + (1 - lam)))
      ≤ Dtr i * (lam * (D i / Dtr i * Real.log (D i / Dtr i))) :=
    mul_le_mul_of_nonneg_left hcv hp.le
  have h4 : Dtr i * (lam * (D i / Dtr i * Real.log (D i / Dtr i))) =
      lam * (D i * Real.log (D i / Dtr i)) := by
    field_simp
  calc (Dtr i * (lam * (D i / Dtr i) + (1 - lam))) * Real.log (lam * (D i / Dtr i) + (1 - lam))
      = Dtr i * ((lam * (D i / Dtr i) + (1 - lam)) * Real.log (lam * (D i / Dtr i) + (1 - lam))) := by ring
    _ ≤ Dtr i * (lam * (D i / Dtr i * Real.log (D i / Dtr i))) := h3
    _ = lam * (D i * Real.log (D i / Dtr i)) := h4

theorem bro_seg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    BootRobust.Perf.bootDist (lam • D + (1 - lam) • Dtr) Dtr ≤
        (lam : EReal) * BootRobust.Perf.bootDist D Dtr + ((1 - lam : ℝ) : EReal) * BootRobust.Perf.bootDist Dtr Dtr ∧
      BootRobust.Perf.bootDist Dtr Dtr = 0 ∧
      ∀ r : ℝ, BootRobust.Perf.bootDist D Dtr = (r : EReal) → 0 < r → lam ∈ Set.Ioo (0 : ℝ) 1 →
        BootRobust.Perf.bootDist (lam • D + (1 - lam) • Dtr) Dtr < (r : EReal) := by
  have h0 : BootRobust.Perf.bootDist Dtr Dtr = 0 := by
    rw [bro_bd Dtr hDtrpos]
    have : ∀ i, Dtr i * Real.log (Dtr i / Dtr i) = 0 := by
      intro i; rw [div_self (hDtrpos i).ne', Real.log_one, mul_zero]
    simp [this]
  have hle : ∑ i, (lam • D + (1 - lam) • Dtr) i * Real.log ((lam • D + (1 - lam) • Dtr) i / Dtr i)
      ≤ lam * ∑ i, D i * Real.log (D i / Dtr i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => bro_key D Dtr hD hDtrpos lam hlam i
  refine ⟨?_, h0, ?_⟩
  · rw [h0, bro_bd Dtr hDtrpos, bro_bd Dtr hDtrpos]
    rw [mul_zero, add_zero]
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact hle
  · intro r hr hr0 hlam'
    rw [bro_bd Dtr hDtrpos]
    rw [bro_bd Dtr hDtrpos] at hr
    have hr' : ∑ i, D i * Real.log (D i / Dtr i) = r := EReal.coe_eq_coe_iff.mp hr
    rw [EReal.coe_lt_coe_iff]
    rw [hr'] at hle
    nlinarith [hlam'.2, hlam'.1]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (hB : BootRobust.Perf.bootDist D Dtr = (r : EReal)) (hr : 0 < r)
    (N : Set (ι → ℝ)) (hN : relOpen N) (hDN : D ∈ N) :
    ⨅ D' ∈ N, BootRobust.Perf.bootDist D' Dtr < (r : EReal) := by
  obtain ⟨U, hU, rfl⟩ := hN
  have hDU : D ∈ U := hDN.1
  have hcont : Continuous (fun t : ℝ => t • D + (1 - t) • Dtr) := by fun_prop
  have hopen : IsOpen ((fun t : ℝ => t • D + (1 - t) • Dtr) ⁻¹' U) := hU.preimage hcont
  have h1 : (1 : ℝ) ∈ (fun t : ℝ => t • D + (1 - t) • Dtr) ⁻¹' U := by simpa using hDU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 h1
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδ2 : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlamU : (1 - δ) • D + (1 - (1 - δ)) • Dtr ∈ U := by
    have : (1 - δ) ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show (1 - δ) - 1 = -δ by ring, abs_neg, abs_of_pos hδ0]; exact hδ2
    exact hball this
  have hlamS : (1 - δ) • D + (1 - (1 - δ)) • Dtr ∈ stdSimplex ℝ ι :=
    convex_stdSimplex ℝ ι hD hDtr (by linarith) (by linarith) (by ring)
  have hmem : (1 - δ) • D + (1 - (1 - δ)) • Dtr ∈ U ∩ stdSimplex ℝ ι := ⟨hlamU, hlamS⟩
  have hlt := (bro_seg D Dtr hD hDtr hDtrpos (1 - δ) ⟨by linarith, by linarith⟩).2.2 r hB hr
    ⟨by linarith, by linarith⟩
  exact lt_of_le_of_lt (iInf₂_le _ hmem) hlt
