-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.logWeylDimensionEstimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:43:53.908802+00:00
-- url     : https://prove2.me/submissions/6d254d01-984a-4eee-9555-9f4c890faa25

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_fT_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_nonneg
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_hh_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_dom_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_pos_row
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_neg_row
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_G_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_G_split
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_ite_const_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TDim_sum_pa_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
namespace TDim
private theorem log_one_add_le_lemma {x A : ℝ} (hx : 0 ≤ x) (h : x ≤ A) :
    Real.log (1 + x) ≤ Real.log (1 + A) :=
  Real.log_le_log (by linarith) (by linarith)
private theorem sum_rows_lemma_2 {n Ns : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hc : ((range n).filter p).card ≤ Ns) (R B : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : ∀ i ∈ range n, B i - (if p i then a else 0) ≤ R i ∧ R i ≤ B i + (if p i then b else 0)) :
    (∑ i ∈ range n, B i) - (Ns : ℝ) * a ≤ ∑ i ∈ range n, R i ∧
      ∑ i ∈ range n, R i ≤ (∑ i ∈ range n, B i) + (Ns : ℝ) * b := by
  have h1 := sum_ite_const_le (n := n) p hc ha
  have h2 := sum_ite_const_le (n := n) p hc hb
  have l1 : ∑ i ∈ range n, (B i - (if p i then a else 0)) ≤ ∑ i ∈ range n, R i :=
    Finset.sum_le_sum fun i hi => (hR i hi).1
  have l2 : ∑ i ∈ range n, R i ≤ ∑ i ∈ range n, (B i + (if p i then b else 0)) :=
    Finset.sum_le_sum fun i hi => (hR i hi).2
  rw [Finset.sum_sub_distrib] at l1
  rw [Finset.sum_add_distrib] at l2
  constructor <;> linarith
private theorem factor_pos_lemma_3 {n : ℕ} {la : ℕ → ℤ} (hd : Formalism.InvariantFactorPaths.BranchingDimensions.Dom n la) {i j : ℕ} (hij : i < j)
    (hj : j < n) :
    0 < (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) := by
  have h1 : (i : ℝ) < j := by exact_mod_cast hij
  have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (dom_anti hd hij.le hj)
  have h2 : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
  apply div_pos <;> linarith
private theorem log_weylDim_lemma_4 {n : ℕ} {la : ℕ → ℤ} (hd : Formalism.InvariantFactorPaths.BranchingDimensions.Dom n la) :
    0 < weylDim n la ∧
      Real.log (weylDim n la) = ∑ j ∈ range n, ∑ i ∈ range j, G la i j := by
  have hpos : ∀ j ∈ range n, ∀ i ∈ range j,
      0 < (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) := by
    intro j hj i hi
    rw [Finset.mem_range] at hj hi
    exact factor_pos_lemma_3 hd hi hj
  have hinner : ∀ j ∈ range n,
      0 < ∏ i ∈ range j, (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) :=
    fun j hj => Finset.prod_pos (hpos j hj)
  unfold weylDim
  refine ⟨Finset.prod_pos hinner, ?_⟩
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Real.log_prod]
    · rfl
    · intro i hi
      exact (hpos j hj i hi).ne'
  · intro j hj
    exact (hinner j hj).ne'
end TDim
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : LogWeylDimensionEstimate := by
  unfold LogWeylDimensionEstimate
  intro r K Ns n la A0 h2 hK hn hd hP hM hA0
  have hA : ∀ x : ℤ, x ≤ max (la 0) 0 + max (-(la (n - 1))) 0 → (x : ℝ) ≤ A0 :=
    fun x hx => le_trans (Int.cast_le.mpr hx) hA0
  have hm1 := le_max_left (la 0) 0
  have hm2 := le_max_right (la 0) 0
  have hm3 := le_max_left (-(la (n - 1))) 0
  have hm4 := le_max_right (-(la (n - 1))) 0
  have htop : ∀ i, i < n → la i ≤ la 0 := fun i hi => Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd (Nat.zero_le i) hi
  have hbot : ∀ j, j < n → la (n - 1) ≤ la j := fun j hj => Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd (by omega) (by omega)
  have hA0nn : 0 ≤ A0 := by
    have := hA 0 (by linarith)
    rw [Int.cast_zero] at this
    exact this
  have hL0 : 0 ≤ Real.log (1 + A0) := Real.log_nonneg (by linarith)
  have hG : ∀ i j, i < j → j < n → Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G la i j ≤ Real.log (1 + A0) := by
    intro i j hij hj
    rw [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_eq hij]
    have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd hij.le hj)
    have hnn : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
    refine (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_le hnn (by omega)).trans (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hnn (hA _ ?_))
    have := htop i (by omega)
    have := hbot j hj
    linarith
  obtain ⟨hWpos, hlogW⟩ := _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_weylDim_lemma_4 hd
  have hsplit : ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G la i j =
      ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa la i j +
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j +
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi hj
    exact Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_split hd hi hj
  have hB0 : 0 ≤ ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa la i j := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi hj
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pa
    split_ifs
    · rw [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_eq hi]
      have h0 : (0 : ℤ) ≤ la i - la j := sub_nonneg.mpr (Formalism.InvariantFactorPaths.BranchingDimensions.TDim.dom_anti hd hi.le hj)
      have hnn : (0 : ℝ) ≤ ((la i - la j : ℤ) : ℝ) := by exact_mod_cast h0
      exact Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_nonneg hnn (by omega)
    · exact le_rfl
  have hB1 := Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_pa_le hL0 hP hM hG
  have hswap : ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j =
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j := by
    apply Finset.sum_comm'
    intro j i
    simp only [Finset.mem_range, Finset.mem_Ico]
    constructor <;> intro h <;> omega
  have hposR : ∀ i ∈ range n,
      fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ) -
          (if 0 < la i then (Ns : ℝ) * Real.log (1 + A0) else 0) ≤
        ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ∧
      ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ≤
        fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ) +
          (if 0 < la i then ((r : ℝ) + 2 * Ns) * Real.log (1 + A0) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb
    by_cases hp : 0 < la i
    · rw [if_pos hp, if_pos hp]
      have hm : max (la i) 0 = la i := max_eq_left hp.le
      rw [hm]
      have hz : (0 : ℝ) ≤ ((la i : ℤ) : ℝ) := by exact_mod_cast hp.le
      have hle : la i ≤ max (la 0) 0 + max (-(la (n - 1))) 0 := by
        have := htop i hi
        linarith
      exact pos_row h2 hK hn hd hP hM hL0 hi hp (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hz (hA _ hle))
    · rw [if_neg hp, if_neg hp]
      have hm : max (la i) 0 = 0 := max_eq_right (not_lt.mp hp)
      rw [hm]
      simp [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_zero, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.fT_zero]
  have hnegR : ∀ j ∈ range n,
      fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ) -
          (if la j < 0 then (Ns : ℝ) * Real.log (1 + A0) else 0) ≤
        ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ∧
      ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ≤
        fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ) +
          (if la j < 0 then ((r : ℝ) + 2 * Ns) * Real.log (1 + A0) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc
    by_cases hp : la j < 0
    · rw [if_pos hp, if_pos hp]
      have hm : max (-(la j)) 0 = -la j := max_eq_left (by omega)
      rw [hm]
      have h0 : (0 : ℤ) ≤ -la j := by omega
      have hz : (0 : ℝ) ≤ ((-la j : ℤ) : ℝ) := by exact_mod_cast h0
      have hle : -la j ≤ max (la 0) 0 + max (-(la (n - 1))) 0 := by
        have := hbot j hj
        linarith
      exact neg_row h2 hK hn hd hP hM hL0 hj hp (_root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.log_one_add_le_lemma hz (hA _ hle))
    · rw [if_neg hp, if_neg hp]
      have hm : max (-(la j)) 0 = 0 := max_eq_right (by omega)
      rw [hm]
      simp [Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_zero, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.fT_zero]
  have hPos : (∑ i ∈ range n, fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ)) -
        (Ns : ℝ) * ((Ns : ℝ) * Real.log (1 + A0)) ≤
        ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ∧
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j ≤
        (∑ i ∈ range n, fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ)) +
          (Ns : ℝ) * (((r : ℝ) + 2 * Ns) * Real.log (1 + A0)) :=
    _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_rows_lemma_2 (n := n) (fun m => 0 < la m) hP (fun i => ∑ j ∈ Ico (i + 1) n, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pb la i j)
      (fun i => fT (K - 2 * Ns) ((max (la i) 0 : ℤ) : ℝ))
      (mul_nonneg (by positivity) hL0) (mul_nonneg (by positivity) hL0) hposR
  have hNeg : (∑ j ∈ range n, fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ)) -
        (Ns : ℝ) * ((Ns : ℝ) * Real.log (1 + A0)) ≤
        ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ∧
      ∑ j ∈ range n, ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j ≤
        (∑ j ∈ range n, fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ)) +
          (Ns : ℝ) * (((r : ℝ) + 2 * Ns) * Real.log (1 + A0)) :=
    _root_.Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_rows_lemma_2 (n := n) (fun m => la m < 0) hM (fun j => ∑ i ∈ range j, Formalism.InvariantFactorPaths.BranchingDimensions.TDim.pc la i j)
      (fun j => fT (K - 2 * Ns) ((max (-(la j)) 0 : ℤ) : ℝ))
      (mul_nonneg (by positivity) hL0) (mul_nonneg (by positivity) hL0) hnegR
  obtain ⟨hP1, hP2⟩ := hPos
  obtain ⟨hN1, hN2⟩ := hNeg
  refine ⟨hWpos, ?_, ?_⟩
  · rw [hlogW, hsplit, hswap]
    linarith
  · rw [hlogW, hsplit, hswap]
    linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
