-- Prove2me | solution 1 for BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:16:29.107133+00:00
-- url     : https://prove2.me/submissions/43ec8c9e-2675-411f-a9ea-152c575e8b08

-- Generated from ChapterQgTimeStepping.lean — theorem BookProof.QgTimeStepping.qgOuterFock_fullyDiscrete_convergence
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgTruncationResolvent
import Mathlib
import Theorems.Thm_BookProof_QgTruncationResolvent_qgOuterFock_truncation_flow_convergence
import Definitions.Def_ChapterQgTimeStepping
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTimeStepping



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgOuterFockCoreFL BookProof.QgTruncationResolvent

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable {ι : Type*}
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


theorem S79cn {t : ℝ} (ht : 0 < t) (v : H) :
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

open BookProof.QgTimeStepping in
theorem solution (W : WallPot) (Q : QgModeData ι) (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        ∀ (v : Sec ι) (t : ℝ), 0 < t →
          ∃ k : ℕ → ℕ, (∀ n, 0 < k n) ∧
            Tendsto (fun n => (cnStep (S n) (t / (k n)))^[k n] v) atTop
              (𝓝 (T.stoneU t v)) := by
  obtain ⟨T, S, hT, hS, -, hflow⟩ := qgOuterFock_truncation_flow_convergence W Q Λ hexh
  refine ⟨T, S, hT, hS, fun v t ht => ?_⟩
  have hk : ∀ n : ℕ, ∃ m : ℕ, ‖(cnStep (S n) (t / ((m : ℝ) + 1)))^[m + 1] v - (S n).stoneU t v‖
      < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (S79cn (S n) ht v) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨N, by have := hN N le_rfl; rwa [dist_eq_norm] at this⟩
  choose m hm using hk
  refine ⟨fun n => m n + 1, fun n => Nat.succ_pos _, ?_⟩
  have hTK := ((hflow v 0 le_rfl).2 t)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hTK ⊢
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add hTK)
  have e : (cnStep (S n) (t / (((m n + 1 : ℕ) : ℝ))))^[m n + 1] v - T.stoneU t v
      = ((cnStep (S n) (t / ((m n : ℝ) + 1)))^[m n + 1] v - (S n).stoneU t v)
        + ((S n).stoneU t v - T.stoneU t v) := by
    push_cast; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (by simpa using (hm n).le) le_rfl)

