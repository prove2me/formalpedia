-- Prove2me | solution 1 for Freiman.perron_eventually_one_limit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:49:12.32423+00:00
-- url     : https://prove2.me/submissions/88ce5329-802a-482d-bdc1-562c76635868

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Tactic.FieldSimp

open Freiman Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 400000

private theorem finite_mem (w : List ℕ+) : finiteCF w ∈ Set.Icc (0 : ℝ) 1 := by
  induction w with
  | nil => simp [finiteCF]
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ (a : ℕ) := by exact_mod_cast a.pos
    have hd : 0 < ((a : ℕ) : ℝ) + finiteCF w := by linarith [ih.1]
    simp only [finiteCF, Set.mem_Icc]
    exact ⟨(one_div_pos.mpr hd).le, (div_le_one hd).mpr (by linarith [ih.1])⟩

theorem solution (b : ℕ → ℕ+) (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → b n = 1) :
    Tendsto (perronValue b) atTop (nhds (Real.sqrt 5)) := by
  obtain ⟨N, hN⟩ := h
  let z := cfValue (fun _ : ℕ => (1 : ℕ+))
  have hz : 0 < z := (cf_convergence _).2.2.1
  have hz1 : z < 1 := (cf_convergence _).2.2.2.1
  have hfix : z = 1 / (1 + z) := by
    simpa [z] using (cf_convergence (fun _ : ℕ => (1 : ℕ+))).2.2.2.2
  have hpoly : z * (1 + z) = 1 := (eq_div_iff (by positivity)).mp hfix
  have hsqrt : 1 + z + z = Real.sqrt 5 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hn := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  let back : ℕ → ℝ := fun n => finiteCF (((List.range n).map b).reverse)
  have hstep (m : ℕ) : back (N + (m + 1)) = 1 / (1 + back (N + m)) := by
    have hb : b (N + m) = 1 := hN _ (Nat.le_add_right _ _)
    simp only [back, ← Nat.add_assoc, List.range_succ, List.map_append,
      List.map_singleton, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, finiteCF, hb]
    norm_num
  have hback (m : ℕ) : back (N + m) =
      prefixEval (List.replicate m (1 : ℕ+)) (back N) := by
    induction m with
    | zero => simp [prefixEval]
    | succ m ih =>
      rw [hstep m, ih]
      simp [List.replicate_succ, prefixEval]
  have hzprefix (m : ℕ) : z = prefixEval (List.replicate m (1 : ℕ+)) z := by
    simpa [z, List.map_const] using cfValue_prefix (fun _ : ℕ => (1 : ℕ+)) m
  have hlim : Tendsto (fun m => back (N + m)) atTop (nhds z) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp cylinder_bound_tendsto ε hε
    refine ⟨M, ?_⟩
    intro m hm
    have ht := hM m hm
    rw [Real.dist_eq, sub_zero] at ht
    have hbound := prefixEval_cylinder_bound (List.replicate m (1 : ℕ+))
      (back N) z (finite_mem _) ⟨hz.le, hz1.le⟩
    rw [← hback m, ← hzprefix m] at hbound
    simp only [List.length_replicate] at hbound
    rw [Real.dist_eq]
    apply lt_of_le_of_lt hbound
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (sq_nonneg _))
      (abs_lt.mp ht).2
  have hevent (m : ℕ) : perronValue b (N + m) = 1 + back (N + m) + z := by
    have hb : b (N + m) = 1 := hN _ (Nat.le_add_right _ _)
    have htail : (fun k : ℕ => b (N + m + 1 + k)) = fun _ : ℕ => (1 : ℕ+) := by
      funext k
      exact hN _ (by omega)
    simp [perronValue, back, hb, htail, z]
  have hfull : Tendsto (fun m => perronValue b (N + m)) atTop
      (nhds (1 + z + z)) := by
    simpa only [hevent] using (tendsto_const_nhds.add hlim).add tendsto_const_nhds
  rw [hsqrt] at hfull
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hfull ε hε
  refine ⟨N + M, ?_⟩
  intro n hn
  have hnm : M ≤ n - N := by omega
  have heq : N + (n - N) = n := by omega
  simpa only [heq] using hM (n - N) hnm
