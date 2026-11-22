-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.finite_detector_report_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:13:08.760877+00:00
-- url     : https://prove2.me/submissions/bad50e5a-093c-40f8-bc58-3d11faf22f34

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_toggle_detector_variation

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- A finite duplicate-free detector trace has at most `T / xi` reports. -/
theorem solution {n k : ℕ} (g : Physical n k)
    (y : ℕ → Fin n → ℝ) (b : ℕ → Fin k → ℝ)
    (C : ℕ → Finset (Fin n)) (tau U : ℕ → ℝ)
    (report : ℕ → Finset (Fin k)) (xi : ℝ) (T : ℕ)
    (hu : ∀ e ∈ g.active, 0 ≤ g.u e) (hxi : 0 < xi)
    (hinit : ∀ e, b 0 e = y 0 (g.graph.tail e) - y 0 (g.graph.head e))
    (hcap : ∀ t < T, cutCapacity g (C t) ≤ U t)
    (htau0 : ∀ t < T, 0 ≤ tau t)
    (htauU : ∀ t < T, tau t ≤ 1 / U t)
    (hy : ∀ t < T, ∀ v,
      y (t + 1) v = y t v + if v ∈ C t then tau t else 0)
    (hreport : ∀ t < T, report t = g.active.filter (fun e =>
      xi ≤ |g.u e * (y (t + 1) (g.graph.tail e) -
        y (t + 1) (g.graph.head e) - b t e)|))
    (hb : ∀ t < T, ∀ e, b (t + 1) e =
      if e ∈ report t then
        y (t + 1) (g.graph.tail e) - y (t + 1) (g.graph.head e)
      else b t e) :
    ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤ (T : ℝ) / xi := by
  classical
  let Φ : ℕ → ℝ := fun t => ∑ e ∈ g.active, g.u e *
    |y t (g.graph.tail e) - y t (g.graph.head e) - b t e|
  have hΦnonneg : ∀ t, 0 ≤ Φ t := by
    intro t
    apply Finset.sum_nonneg
    intro e he
    exact mul_nonneg (hu e he) (abs_nonneg _)
  have hΦ0 : Φ 0 = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [hinit e]
    simp
  have hmain : ∀ N : ℕ,
      (∀ t < N, cutCapacity g (C t) ≤ U t) →
      (∀ t < N, 0 ≤ tau t) →
      (∀ t < N, tau t ≤ 1 / U t) →
      (∀ t < N, ∀ v,
        y (t + 1) v = y t v + if v ∈ C t then tau t else 0) →
      (∀ t < N, report t = g.active.filter (fun e =>
        xi ≤ |g.u e * (y (t + 1) (g.graph.tail e) -
          y (t + 1) (g.graph.head e) - b t e)|)) →
      (∀ t < N, ∀ e, b (t + 1) e =
        if e ∈ report t then
          y (t + 1) (g.graph.tail e) - y (t + 1) (g.graph.head e)
        else b t e) →
      Φ N + xi * ((∑ t ∈ Finset.range N, (report t).card : ℕ) : ℝ) ≤
        Φ 0 + (N : ℝ) := by
    intro N
    induction N with
    | zero =>
        intro hcap htau0 htauU hy hreport hb
        simp
    | succ N ih =>
        intro hcap htau0 htauU hy hreport hb
        have hN : N < N + 1 := Nat.lt_succ_self N
        have hprefix : Φ N + xi * ((∑ t ∈ Finset.range N, (report t).card : ℕ) : ℝ) ≤
            Φ 0 + (N : ℝ) := by
          apply ih
          · intro t ht
            exact hcap t (Nat.lt_trans ht hN)
          · intro t ht
            exact htau0 t (Nat.lt_trans ht hN)
          · intro t ht
            exact htauU t (Nat.lt_trans ht hN)
          · intro t ht
            exact hy t (Nat.lt_trans ht hN)
          · intro t ht
            exact hreport t (Nat.lt_trans ht hN)
          · intro t ht
            exact hb t (Nat.lt_trans ht hN)
        let pre : ℝ := ∑ e ∈ g.active, g.u e *
          |y (N + 1) (g.graph.tail e) - y (N + 1) (g.graph.head e) - b N e|
        have hvar : pre ≤ Φ N + 1 := by
          have h := toggle_detector_variation g (y N) (b N) (C N) (tau N) (U N)
            hu (hcap N hN) (htau0 N hN) (htauU N hN)
          dsimp [pre, Φ]
          simp_rw [hy N hN]
          exact h
        have hsub : report N ⊆ g.active := by
          rw [hreport N hN]
          exact Finset.filter_subset _ _
        have hpost : Φ (N + 1) + xi * (report N).card ≤ pre := by
          have hper : ∀ e ∈ g.active,
              g.u e * |y (N + 1) (g.graph.tail e) -
                  y (N + 1) (g.graph.head e) - b (N + 1) e| +
                (if e ∈ report N then xi else 0) ≤
              g.u e * |y (N + 1) (g.graph.tail e) -
                y (N + 1) (g.graph.head e) - b N e| := by
            intro e he
            by_cases hr : e ∈ report N
            · have hr' := hr
              rw [hreport N hN] at hr'
              have hthr := (Finset.mem_filter.mp hr').2
              rw [hb N hN e, if_pos hr]
              simp only [hr, if_true, sub_self, abs_zero, mul_zero, zero_add]
              rwa [abs_mul, abs_of_nonneg (hu e he)] at hthr
            · rw [hb N hN e, if_neg hr]
              simp [hr]
          have hsumxi : (∑ e ∈ g.active, if e ∈ report N then xi else 0) =
              xi * (report N).card := by
            calc
              (∑ e ∈ g.active, if e ∈ report N then xi else 0) =
                  ∑ e ∈ report N, if e ∈ report N then xi else 0 := by
                symm
                apply Finset.sum_subset hsub
                intro e heactive henot
                simp [henot]
              _ = xi * (report N).card := by simp [mul_comm]
          calc
            Φ (N + 1) + xi * (report N).card =
                (∑ e ∈ g.active, g.u e *
                  |y (N + 1) (g.graph.tail e) - y (N + 1) (g.graph.head e) - b (N + 1) e|) +
                  ∑ e ∈ g.active, if e ∈ report N then xi else 0 := by
                    rw [hsumxi]
            _ = ∑ e ∈ g.active, (g.u e *
                  |y (N + 1) (g.graph.tail e) - y (N + 1) (g.graph.head e) - b (N + 1) e| +
                  if e ∈ report N then xi else 0) := by rw [Finset.sum_add_distrib]
            _ ≤ pre := Finset.sum_le_sum hper
        rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_succ]
        have hstep : Φ (N + 1) + xi * (report N).card ≤ Φ N + 1 := by
          linarith
        linarith
  have hbound := hmain T hcap htau0 htauU hy hreport hb
  have hnonneg := hΦnonneg T
  have hreal : xi * ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤ (T : ℝ) := by
    rw [hΦ0] at hbound
    linarith
  exact (le_div_iff₀ hxi).2 (by simpa [mul_comm] using hreal)
