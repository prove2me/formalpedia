-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.initial_sum_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:48.701068+00:00
-- url     : https://prove2.me/submissions/37954750-4344-47b6-8254-1692ef5414cd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FactorialProductRearrangement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma interlaced_lower_one_le (m : ℕ) (b w : ℕ → ℝ) (hb0 : 1 ≤ b 0) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ j, j < m → 1 ≤ b j := by
  intro j
  induction j with
  | zero => intro _; exact hb0
  | succ n ih =>
    intro hn
    have e1 := h1 n (by omega)
    have e2 := h2 n hn
    have e3 := ih (by omega)
    linarith
private lemma interlaced_sequence_monotone (m : ℕ) (b w : ℕ → ℝ) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ i j, i ≤ j → j < m → w i ≤ w j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ n hin ih =>
    intro hj
    have e1 := ih (by omega)
    have e2 := h2 n hj
    have e3 := h1 (n + 1) hj
    linarith
private lemma interlaced_log_telescoping (m : ℕ) (b w : ℕ → ℝ) (hb0 : 1 ≤ b 0) (h1 : ∀ j, j < m → b j < w j)
    (h2 : ∀ j, j + 1 < m → w j < b (j + 1)) : ∀ n, n < m →
    ∑ j ∈ range (n + 1), (Real.log (w j) - Real.log (b j)) ≤ Real.log (w n) - Real.log (b 0) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ]
    have e1 := ih (by omega)
    have hb := interlaced_lower_one_le m b w hb0 h1 h2 n (by omega)
    have hwn := h1 n (by omega)
    have h2n := h2 n hn
    have : Real.log (w n) ≤ Real.log (b (n + 1)) := Real.log_le_log (by linarith) h2n.le
    linarith
private lemma interlaced_log_chain_bounds (m : ℕ) (L : ℝ) (b w : ℕ → ℝ) (hm : 1 ≤ m) (hb0 : 1 ≤ b 0)
    (h1 : ∀ j, j < m → b j < w j) (h2 : ∀ j, j + 1 < m → w j < b (j + 1))
    (htop : w (m - 1) ≤ 2 * Real.exp L) :
    (∀ j, j < m → 1 ≤ b j ∧ 1 < w j ∧ Real.log (b j) ≤ L + Real.log 2) ∧
    0 ≤ ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ∧
    ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ≤ L + Real.log 2 := by
  have hlog : Real.log (2 * Real.exp L) = L + Real.log 2 := by
    rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp]; ring
  have hbg := interlaced_lower_one_le m b w hb0 h1 h2
  have hwle := interlaced_sequence_monotone m b w h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have e1 := hbg j hj
    have e2 := h1 j hj
    have e3 := hwle j (m - 1) (by omega) (by omega)
    refine ⟨e1, by linarith, ?_⟩
    rw [← hlog]
    exact Real.log_le_log (by linarith) (by linarith)
  · apply Finset.sum_nonneg
    intro j hj
    rw [Finset.mem_range] at hj
    have e1 := hbg j hj
    have e2 := h1 j hj
    have : Real.log (b j) ≤ Real.log (w j) := Real.log_le_log (by linarith) e2.le
    linarith
  · have e := interlaced_log_telescoping m b w hb0 h1 h2 (m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega] at e
    have hwm := h1 (m - 1) (by omega)
    have hbm := hbg (m - 1) (by omega)
    have e4 : Real.log (w (m - 1)) ≤ L + Real.log 2 := by
      rw [← hlog]; exact Real.log_le_log (by linarith) htop
    have e5 : 0 ≤ Real.log (b 0) := Real.log_nonneg hb0
    linarith
private lemma log_volume_ratio_bounds (L vE : ℝ) (hv : Real.pi ≤ vE) (hL : Real.log vE ≤ L) :
    0 ≤ Real.log (vE / Real.pi) ∧ Real.log (vE / Real.pi) ≤ L ∧ 0 ≤ L := by
  have hpi := Real.pi_pos
  have hv0 : 0 < vE := by linarith
  have h1 : 1 ≤ vE / Real.pi := by rw [le_div_iff₀ hpi]; linarith
  have h2 : 0 ≤ Real.log (vE / Real.pi) := Real.log_nonneg h1
  have h3 : Real.log (vE / Real.pi) = Real.log vE - Real.log Real.pi :=
    Real.log_div hv0.ne' hpi.ne'
  have h4 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h5 : Real.log Real.pi ≤ Real.log vE := Real.log_le_log hpi hv
  exact ⟨h2, by linarith, by linarith⟩
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : InterlacedProductComparison := by
  intro L vE aeff A m b w hm hv hL hb0 h1 h2 htop ha hA
  dsimp only
  rw [inv_div]
  obtain ⟨hl0, hlL, hL0⟩ := log_volume_ratio_bounds L vE hv hL
  obtain ⟨hj, hs0, hsL⟩ := interlaced_log_chain_bounds m L b w hm hb0 h1 h2 htop
  have hpi := Real.pi_pos
  have hv0 : 0 < vE := by linarith
  have hbpos : ∀ j ∈ range m, 0 < b j := fun j hj' => by
    have := (hj j (Finset.mem_range.mp hj')).1
    linarith
  have hwpos : ∀ j ∈ range m, 0 < w j := fun j hj' => by
    have := (hj j (Finset.mem_range.mp hj')).2.1
    linarith
  have hB : 0 < ∏ j ∈ range m, b j := Finset.prod_pos hbpos
  have hW : 0 < ∏ j ∈ range m, w j := Finset.prod_pos hwpos
  have hc : 0 < vE / Real.pi := div_pos hv0 hpi
  have eL : ∏ j ∈ range m, w j * vE / Real.pi = (∏ j ∈ range m, w j) * (vE / Real.pi) ^ m := by
    simp_rw [mul_div_assoc]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hpow : (vE / Real.pi) ^ m = (vE / Real.pi) ^ (m - 1) * (vE / Real.pi) := by
    rw [← pow_succ]
    congr 1
    omega
  have e1 : ∏ j ∈ range m, w j * vE / Real.pi =
      ((vE / Real.pi) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff) *
        (vE / Real.pi * aeff * ∏ j ∈ range m, w j / b j) := by
    rw [eL, Finset.prod_div_distrib, hpow]
    have hB0 := hB.ne'
    have ha0 := ha.ne'
    field_simp
  refine ⟨e1, ?_⟩
  have hX : 0 < (vE / Real.pi) ^ (m - 1) * (∏ j ∈ range m, b j) / aeff := by positivity
  have hQ : 0 < ∏ j ∈ range m, w j / b j :=
    Finset.prod_pos (fun j hj' => div_pos (hwpos j hj') (hbpos j hj'))
  have hY : 0 < vE / Real.pi * aeff * ∏ j ∈ range m, w j / b j := by positivity
  rw [e1, Real.log_mul hX.ne' hY.ne', add_sub_cancel_left,
    Real.log_mul (by positivity) hQ.ne', Real.log_mul hc.ne' ha.ne']
  have hsum : Real.log (∏ j ∈ range m, w j / b j) =
      ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) := by
    rw [Real.log_prod (fun j hj' => (div_pos (hwpos j hj') (hbpos j hj')).ne')]
    apply Finset.sum_congr rfl
    intro j hj'
    exact Real.log_div (hwpos j hj').ne' (hbpos j hj').ne'
  rw [hsum]
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le]
  constructor <;> linarith
end Formalism.HermitianLattices.GenusMassVolumes
