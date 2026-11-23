-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.place_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:27.255892+00:00
-- url     : https://prove2.me/submissions/b19a074d-1d2d-471e-b1cf-05506e45ac13

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hV : VandPlace) (ε x C₀ : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) (hC₀ : 0 ≤ C₀)
    (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hΔ : 1 ≤ Δ)
    (hkx : (k : ℝ) ≤ x ^ C₀)
    (hP : PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w) :
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧ (∀ j, j < m → 0 < w j) ∧
    (k : ℝ) * ∑ j ∈ range m, Real.log (w j)
      ≤ (Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k))
        + k * x ^ ε * (20 + (2 + 2 * C₀) / ε) + 2 * m * x ^ ε := by
  obtain ⟨hu, hl, hVb⟩ := hV ε x hε hx k m Δ u v b w hk hm hΔ hP
  obtain ⟨-, -, -, -, -, hbw, hbb, hb0, hwtop⟩ := hP
  set L := x ^ ε with hLdef
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := Real.one_le_rpow hx hε.le
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogx : Real.log x ≤ L / ε := by
    have h1 := Real.add_one_le_exp (Real.log x * ε)
    rw [← Real.rpow_def_of_pos hx0] at h1
    rw [le_div_iff₀ hε]; linarith
  have hlogk : Real.log k ≤ C₀ * (L / ε) := by
    have h1 : Real.log k ≤ Real.log (x ^ C₀) := Real.log_le_log hk0 hkx
    rw [Real.log_rpow hx0] at h1
    nlinarith [mul_le_mul_of_nonneg_left hlogx hC₀]
  have hexp0 : 0 < Real.exp L := Real.exp_pos L
  have hxe : 0 < x * Real.exp L := mul_pos hx0 hexp0
  have hlog8a : Real.log (8 * (x * Real.exp L)) ≤ 7 + L / ε + L := by
    rw [Real.log_mul (by norm_num) hxe.ne', Real.log_mul hx0.ne' hexp0.ne', Real.log_exp]
    have : Real.log 8 ≤ 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hΔk : (8 : ℝ) ≤ k * (4 * Δ) := by nlinarith
  have hb0x : 8 * x ≤ b 0 := by
    have := (le_div_iff₀ hx0).mp hb0; nlinarith
  have hb0' : 1 ≤ b 0 := by nlinarith
  have hbmono : ∀ j, j < m → b 0 ≤ b j := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ n ih =>
      intro hn
      have h1 := (hbb n hn).2
      have h2 := ih (by omega)
      linarith
  have hbpos : ∀ j, j < m → 0 < b j := fun j hj => by linarith [hbmono j hj]
  have hwpos : ∀ j, j < m → 0 < w j := fun j hj => by linarith [hbpos j hj, (hbw j hj).1]
  have hwstep : ∀ j, j + 1 < m → w j ≤ w (j + 1) := by
    intro j hj
    have h1 := (hbb j hj).1
    have h2 := (hbw (j + 1) hj).1
    linarith
  have hwmono : ∀ i j, i ≤ j → j < m → w i ≤ w j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ n hn ih =>
      intro h
      exact le_trans (ih (by omega)) (hwstep n h)
  have hwtop' : ∀ j, j < m → w j ≤ 2 * Real.exp L := fun j hj =>
    le_trans (hwmono j (m - 1) (by omega) (by omega)) hwtop
  have hlogtop : Real.log (2 * Real.exp L) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) hexp0.ne', Real.log_exp]
  have hlogb : ∀ j, j < m → Real.log (b j) ≤ 1 + L := by
    intro j hj
    have h1 : Real.log (b j) ≤ Real.log (2 * Real.exp L) :=
      Real.log_le_log (hbpos j hj) (le_trans (hbw j hj).1.le (hwtop' j hj))
    linarith
  have hsumb : ∑ j ∈ range m, Real.log (b j) ≤ m * (1 + L) := by
    have := Finset.sum_le_sum (fun j hj => hlogb j (Finset.mem_range.mp hj))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have htele : ∀ n, 1 ≤ n → n ≤ m →
      ∑ j ∈ range n, (Real.log (w j) - Real.log (b j)) ≤ Real.log (w (n - 1)) - Real.log (b 0) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; simp
    | succ n hn ih =>
      intro h
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 : Real.log (w (n - 1)) ≤ Real.log (b n) := by
        have h3 := (hbb (n - 1) (by omega)).1
        rw [show n - 1 + 1 = n by omega] at h3
        exact Real.log_le_log (hwpos (n - 1) (by omega)) h3.le
      simp only [Nat.add_sub_cancel]
      linarith
  have htel := htele m hm le_rfl
  have hwlast : Real.log (w (m - 1)) ≤ 1 + L := by
    have h1 : Real.log (w (m - 1)) ≤ Real.log (2 * Real.exp L) :=
      Real.log_le_log (hwpos (m - 1) (by omega)) hwtop
    linarith
  have hlb0 : 0 ≤ Real.log (b 0) := Real.log_nonneg hb0'
  have hsplit : ∑ j ∈ range m, Real.log (w j) = ∑ j ∈ range m, Real.log (b j)
      + ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) := by
    rw [Finset.sum_sub_distrib]; ring
  have hkA : (k : ℝ) * (L / ε) * 2 + 2 * k * (C₀ * (L / ε)) = k * L * ((2 + 2 * C₀) / ε) := by
    field_simp
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkL : (k : ℝ) * 1 ≤ k * L := mul_le_mul_of_nonneg_left hL1 hk0.le
  have hmL : (m : ℝ) * 1 ≤ m * L := mul_le_mul_of_nonneg_left hL1 (by linarith)
  have e1 : (k : ℝ) * Real.log (8 * (x * Real.exp L)) ≤ k * (7 + L / ε + L) :=
    mul_le_mul_of_nonneg_left hlog8a hk0.le
  have e2 : (k : ℝ) * Real.log k ≤ k * (C₀ * (L / ε)) := mul_le_mul_of_nonneg_left hlogk hk0.le
  have e3 : (k : ℝ) * ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ≤ k * (1 + L) := by
    apply mul_le_mul_of_nonneg_left _ hk0.le; linarith
  refine ⟨hu, hl, hwpos, ?_⟩
  rw [hsplit]
  linarith
end Formalism.LogVandermondeBounds.StandardLattice
