-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_detector_report_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:18:51.181287+00:00
-- url     : https://prove2.me/submissions/ac10a951-80f1-4dd4-8231-ca1776a93cfd

import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_toggle_detector_variation

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- Duplicate-free detector reports in a dynamic physical trace telescope to at most the
number of toggles divided by the threshold. -/
theorem solution {n k : ℕ}
    (s : ℕ → CutState n k) (op : ℕ → CutOp n k)
    (report : ℕ → Finset (Fin k)) (xi : ℝ) (T : ℕ)
    (hu : ∀ t ≤ T, ∀ e ∈ (s t).physical.active, 0 ≤ (s t).physical.u e)
    (hxi : 0 < xi)
    (hinit : ∀ e ∈ (s 0).physical.active,
      (s 0).baseline e = (s 0).y ((s 0).physical.graph.tail e) -
        (s 0).y ((s 0).physical.graph.head e))
    (hphysical : ∀ t < T,
      (s (t + 1)).physical = applyPhysical (s t).physical (op t))
    (hvalid : ∀ t < T, CutOp.Valid (s t) (op t))
    (hcap : ∀ t < T, ∀ tau, op t = .toggle tau →
      cutCapacity (s t).physical (s t).lastCut ≤ (s t).lastU)
    (htau0 : ∀ t < T, ∀ tau, op t = .toggle tau → 0 ≤ tau)
    (htauU : ∀ t < T, ∀ tau, op t = .toggle tau → tau ≤ 1 / (s t).lastU)
    (hy : ∀ t < T, ∀ v, (s (t + 1)).y v = match op t with
      | .toggle tau => (s t).y v + if v ∈ (s t).lastCut then tau else 0
      | _ => (s t).y v)
    (hreport : ∀ t < T, report t = match op t with
      | .toggle _ => (s t).physical.active.filter (fun e =>
          xi ≤ |(s t).physical.u e *
            ((s (t + 1)).y ((s t).physical.graph.tail e) -
              (s (t + 1)).y ((s t).physical.graph.head e) - (s t).baseline e)|)
      | _ => ∅)
    (hb : ∀ t < T, ∀ e, (s (t + 1)).baseline e = match op t with
      | .toggle _ => if e ∈ report t then
          (s (t + 1)).y ((s t).physical.graph.tail e) -
            (s (t + 1)).y ((s t).physical.graph.head e)
        else (s t).baseline e
      | .insert f a b _ => if e = f then (s t).y a - (s t).y b else (s t).baseline e
      | _ => (s t).baseline e) :
    ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤
      (∑ t ∈ Finset.range T, (match op t with
        | .toggle _ => (1 : ℝ) | _ => 0)) / xi := by
  classical
  let Φ : ℕ → ℝ := fun t => ∑ e ∈ (s t).physical.active, (s t).physical.u e *
    |(s t).y ((s t).physical.graph.tail e) -
      (s t).y ((s t).physical.graph.head e) - (s t).baseline e|
  let W : CutOp n k → ℝ := fun o => match o with
    | .toggle _ => 1
    | _ => 0
  have hΦnonneg : ∀ t ≤ T, 0 ≤ Φ t := by
    intro t ht
    apply Finset.sum_nonneg
    intro e he
    exact mul_nonneg (hu t ht e he) (abs_nonneg _)
  have hΦ0 : Φ 0 = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [hinit e he]
    simp
  have hmain : ∀ N ≤ T, Φ N + xi *
      ((∑ t ∈ Finset.range N, (report t).card : ℕ) : ℝ) ≤
      Φ 0 + ∑ t ∈ Finset.range N, W (op t) := by
    intro N
    induction N with
    | zero =>
        intro hNT
        simp [hΦ0]
    | succ N ih =>
        intro hsucc
        have hN : N < T := Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hsucc
        have hleN : N ≤ T := Nat.le_of_lt hN
        have hprefix := ih (Nat.le_trans (Nat.le_succ N) hsucc)
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        cases hop : op N with
        | toggle tau =>
            let pre : ℝ := ∑ e ∈ (s N).physical.active, (s N).physical.u e *
              |(s (N + 1)).y ((s N).physical.graph.tail e) -
                (s (N + 1)).y ((s N).physical.graph.head e) - (s N).baseline e|
            have hvar : pre ≤ Φ N + 1 := by
              have h := toggle_detector_variation (s N).physical (s N).y (s N).baseline
                (s N).lastCut tau (s N).lastU (hu N hleN) (hcap N hN tau hop)
                (htau0 N hN tau hop) (htauU N hN tau hop)
              dsimp [pre, Φ]
              simp_rw [hy N hN, hop]
              exact h
            have hsub : report N ⊆ (s N).physical.active := by
              rw [hreport N hN, hop]
              exact Finset.filter_subset _ _
            have hpost : Φ (N + 1) + xi * (report N).card ≤ pre := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              simp only [applyPhysical] at hphys
              have hper : ∀ e ∈ (s N).physical.active,
                  (s N).physical.u e * |(s (N + 1)).y ((s N).physical.graph.tail e) -
                      (s (N + 1)).y ((s N).physical.graph.head e) - (s (N + 1)).baseline e| +
                    (if e ∈ report N then xi else 0) ≤
                  (s N).physical.u e * |(s (N + 1)).y ((s N).physical.graph.tail e) -
                    (s (N + 1)).y ((s N).physical.graph.head e) - (s N).baseline e| := by
                intro e he
                by_cases hr : e ∈ report N
                · have hr' := hr
                  rw [hreport N hN, hop] at hr'
                  have hthr := (Finset.mem_filter.mp hr').2
                  have hbN := hb N hN e
                  rw [hop] at hbN
                  dsimp only at hbN
                  rw [hbN, if_pos hr]
                  simp only [hr, if_true, sub_self, abs_zero, mul_zero, zero_add]
                  rwa [abs_mul, abs_of_nonneg (hu N hleN e he)] at hthr
                · have hbN := hb N hN e
                  rw [hop] at hbN
                  dsimp only at hbN
                  rw [hbN, if_neg hr]
                  simp [hr]
              have hsumxi : (∑ e ∈ (s N).physical.active,
                  if e ∈ report N then xi else 0) = xi * (report N).card := by
                calc
                  (∑ e ∈ (s N).physical.active, if e ∈ report N then xi else 0) =
                      ∑ e ∈ report N, if e ∈ report N then xi else 0 := by
                    symm
                    apply Finset.sum_subset hsub
                    intro e heactive henot
                    simp [henot]
                  _ = xi * (report N).card := by simp [mul_comm]
              calc
                Φ (N + 1) + xi * (report N).card =
                    (∑ e ∈ (s N).physical.active, (s N).physical.u e *
                      |(s (N + 1)).y ((s N).physical.graph.tail e) -
                        (s (N + 1)).y ((s N).physical.graph.head e) -
                          (s (N + 1)).baseline e|) +
                      ∑ e ∈ (s N).physical.active, if e ∈ report N then xi else 0 := by
                        rw [hsumxi]
                        dsimp [Φ]
                        rw [hphys]
                _ = ∑ e ∈ (s N).physical.active, ((s N).physical.u e *
                      |(s (N + 1)).y ((s N).physical.graph.tail e) -
                        (s (N + 1)).y ((s N).physical.graph.head e) -
                          (s (N + 1)).baseline e| +
                      if e ∈ report N then xi else 0) := by rw [Finset.sum_add_distrib]
                _ ≤ pre := Finset.sum_le_sum hper
            simp only [hop, W]
            rw [Nat.cast_add]
            linarith
        | insert e a b u =>
            have hrep : report N = ∅ := by rw [hreport N hN, hop]
            have hyN : ∀ v, (s (N + 1)).y v = (s N).y v := by
              intro v
              have h := hy N hN v
              rwa [hop] at h
            have hbN : ∀ f, (s (N + 1)).baseline f =
                if f = e then (s N).y a - (s N).y b else (s N).baseline f := by
              intro f
              have h := hb N hN f
              rwa [hop] at h
            have hzero : Φ (N + 1) = Φ N := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              have he : e ∉ (s N).physical.active := by
                have hv := hvalid N hN
                rw [hop] at hv
                exact hv.1
              dsimp [Φ]
              rw [hphys]
              simp only [applyPhysical]
              simp_rw [hyN, hbN]
              rw [Finset.sum_insert he]
              simp only [Function.update_self, if_true, sub_self, abs_zero,
                mul_zero, zero_add]
              apply Finset.sum_congr rfl
              intro f hf
              have hne : f ≠ e := by
                intro hfe
                subst f
                exact he hf
              simp [Function.update, hne]
            simp only [W, hrep, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
            rw [hzero]
            linarith
        | erase e =>
            have hrep : report N = ∅ := by rw [hreport N hN, hop]
            have hyN : ∀ v, (s (N + 1)).y v = (s N).y v := by
              intro v
              have h := hy N hN v
              rwa [hop] at h
            have hbN : ∀ f, (s (N + 1)).baseline f = (s N).baseline f := by
              intro f
              have h := hb N hN f
              rwa [hop] at h
            have hdrop : Φ (N + 1) ≤ Φ N := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              have he : e ∈ (s N).physical.active := by
                have hv := hvalid N hN
                rw [hop] at hv
                exact hv
              dsimp [Φ]
              rw [hphys]
              simp only [applyPhysical]
              simp_rw [hyN, hbN]
              have hsum := Finset.sum_erase_add (s N).physical.active
                (fun f => (s N).physical.u f *
                  |(s N).y ((s N).physical.graph.tail f) -
                    (s N).y ((s N).physical.graph.head f) - (s N).baseline f|) he
              have hterm : 0 ≤ (s N).physical.u e *
                  |(s N).y ((s N).physical.graph.tail e) -
                    (s N).y ((s N).physical.graph.head e) - (s N).baseline e| :=
                mul_nonneg (hu N hleN e he) (abs_nonneg _)
              linarith
            simp only [W, hrep, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
            linarith
        | paired a b delta =>
            have hrep : report N = ∅ := by rw [hreport N hN, hop]
            have hyN : ∀ v, (s (N + 1)).y v = (s N).y v := by
              intro v
              have h := hy N hN v
              rwa [hop] at h
            have hbN : ∀ f, (s (N + 1)).baseline f = (s N).baseline f := by
              intro f
              have h := hb N hN f
              rwa [hop] at h
            have hzero : Φ (N + 1) = Φ N := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              dsimp [Φ]
              rw [hphys]
              simp only [applyPhysical]
              simp_rw [hyN, hbN]
            simp only [W, hrep, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
            rw [hzero]
            linarith
        | ratio =>
            have hrep : report N = ∅ := by rw [hreport N hN, hop]
            have hyN : ∀ v, (s (N + 1)).y v = (s N).y v := by
              intro v
              have h := hy N hN v
              rwa [hop] at h
            have hbN : ∀ f, (s (N + 1)).baseline f = (s N).baseline f := by
              intro f
              have h := hb N hN f
              rwa [hop] at h
            have hzero : Φ (N + 1) = Φ N := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              dsimp [Φ]
              rw [hphys]
              simp only [applyPhysical]
              simp_rw [hyN, hbN]
            simp only [W, hrep, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
            rw [hzero]
            linarith
        | queryY v =>
            have hrep : report N = ∅ := by rw [hreport N hN, hop]
            have hyN : ∀ w, (s (N + 1)).y w = (s N).y w := by
              intro w
              have h := hy N hN w
              rwa [hop] at h
            have hbN : ∀ f, (s (N + 1)).baseline f = (s N).baseline f := by
              intro f
              have h := hb N hN f
              rwa [hop] at h
            have hzero : Φ (N + 1) = Φ N := by
              have hphys := hphysical N hN
              rw [hop] at hphys
              dsimp [Φ]
              rw [hphys]
              simp only [applyPhysical]
              simp_rw [hyN, hbN]
            simp only [W, hrep, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
            rw [hzero]
            linarith
  have hbound := hmain T le_rfl
  have hlast := hΦnonneg T le_rfl
  rw [hΦ0] at hbound
  have hreal : xi * ((∑ t ∈ Finset.range T, (report t).card : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range T, W (op t) := by
    linarith
  exact (le_div_iff₀ hxi).2 (by simpa [W, mul_comm] using hreal)