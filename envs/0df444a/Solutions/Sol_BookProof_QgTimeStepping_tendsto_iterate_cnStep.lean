-- Prove2me | solution 1 for BookProof.QgTimeStepping.tendsto_iterate_cnStep
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:14:23.926173+00:00
-- url     : https://prove2.me/submissions/4f0e1363-45d9-40ac-b73d-313c39a7a47e

-- Generated from ChapterQgTimeStepping.lean — theorem BookProof.QgTimeStepping.tendsto_iterate_cnStep
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Mathlib
import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgTimeStepping



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem S79dom2 (v : H) {eps : ℝ} (heps : 0 < eps) :
    ∃ x : T.domain, T.op x ∈ T.domain ∧ ‖v - (x : H)‖ < eps := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (T.jn_tendsto v) eps heps
  set n : ℝ := (N : ℝ) + 1 with hn
  have hn0 : n ≠ 0 := by positivity
  set y : T.domain := T.res (-n) v
  set z : T.domain := T.res n (y : H)
  refine ⟨((n : ℂ) ^ 2) • z, ?_, ?_⟩
  · rw [map_smul, T.op_res hn0 (y : H)]
    refine T.domain.smul_mem _ (T.domain.add_mem y.2 (T.domain.smul_mem _ z.2))
  · have h := hN N le_rfl
    rw [dist_comm, dist_eq_norm] at h
    have e : ((((n : ℂ) ^ 2) • z : T.domain) : H) = T.jn ((N : ℝ) + 1) v := by
      rw [T.jn_apply]; rfl
    rw [e]; exact h

open BookProof.QgTimeStepping in
theorem solution {t : ℝ} (ht : 0 < t) (v : H) :
    Tendsto (fun k : ℕ => (cnStep T (t / (k + 1)))^[k + 1] v) atTop
      (𝓝 (T.stoneU t v)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨x, hx, hxv⟩ := S79dom2 T v (eps := ε / 3) (by positivity)
  set C := ‖T.op ⟨T.op x, hx⟩‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t ^ 2 * C / (ε / 3))
  refine ⟨N, fun k hk => ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set τ : ℝ := t / ((k : ℝ) + 1) with hτ
  have hτ0 : 0 < τ := div_pos ht hk1
  have e1 := norm_iterate_cnStep_sub_stoneU_le T hτ0 (k + 1) x hx
  have hkt : (((k + 1 : ℕ) : ℝ)) * τ = t := by
    rw [hτ]; push_cast; field_simp
  rw [hkt] at e1
  have herr : 2 * (((k + 1 : ℕ) : ℝ)) * τ ^ 2 * C < ε / 3 := by
    have h1 : 2 * (((k + 1 : ℕ) : ℝ)) * τ ^ 2 * C = 2 * t ^ 2 * C / ((k : ℝ) + 1) := by
      rw [hτ]; push_cast; field_simp
    rw [h1, div_lt_iff₀ hk1]
    have h2 : 2 * t ^ 2 * C < ε / 3 * N := by
      rw [div_lt_iff₀ (by positivity)] at hN; linarith
    have h3 : (N : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  rw [dist_eq_norm]
  have e : (cnStep T τ)^[k + 1] v - T.stoneU t v
      = (cnStep T τ)^[k + 1] (v - x) + ((cnStep T τ)^[k + 1] (x : H) - T.stoneU t (x : H))
        + T.stoneU t ((x : H) - v) := by
    rw [← iterate_cnStep_sub, map_sub]; abel
  have hτ' : τ ≠ 0 := ne_of_gt hτ0
  have hxv' : ‖(x : H) - v‖ < ε / 3 := by rw [norm_sub_rev]; exact hxv
  calc ‖(cnStep T (t / ((k : ℝ) + 1)))^[k + 1] v - T.stoneU t v‖
      = ‖(cnStep T τ)^[k + 1] v - T.stoneU t v‖ := rfl
    _ ≤ ‖(cnStep T τ)^[k + 1] (v - x)‖ + ‖(cnStep T τ)^[k + 1] (x : H) - T.stoneU t (x : H)‖
        + ‖T.stoneU t ((x : H) - v)‖ := by rw [e]; exact norm_add₃_le
    _ < ε := by
        rw [norm_iterate_cnStep_apply T hτ', T.norm_stoneU_apply]
        linarith

