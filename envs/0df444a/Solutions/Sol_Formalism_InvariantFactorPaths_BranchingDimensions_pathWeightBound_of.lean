-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pathWeightBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:49.877252+00:00
-- url     : https://prove2.me/submissions/15aacfb4-d16f-4e31-b7f9-284805bc1950

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_be_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_be_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_ent_sign
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_sum_lat
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_mem_lat
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_getD_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_bracket
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_lat_pred
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_tailPos_split
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_drop_split
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_key
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_TTyp_a_fin
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
open Letters
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
end TTyp
private theorem le_exp_mul_of_log_le_add_log {w T E : ℝ} (hw : 0 < w) (hT : 0 < T) (h : Real.log w ≤ E + Real.log T) :
    w ≤ Real.exp E * T := by
  have h' := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hw, Real.exp_add, Real.exp_log hT] at h'
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution :
    PathEntryBounds → PathInterlacingCriterion → LogBinomialProperties → LogWeylDimensionEstimate → LogRankEstimate → PathTailBounds → LogBinomialDeficit → PathWeightBound := by
  intro h20 h21 h31 h32 h33 h35 h34 D a p La b hW hPB hTD mu hP
  have h21' := h21
  unfold LogWeylDimensionEstimate at h32
  unfold LogRankEstimate at h33
  unfold PathTailBounds at h35
  unfold PathInterlacingCriterion at h21'
  have hWF := hW
  obtain ⟨hr1, hK1, h3r, hvr, hvn⟩ := hWF
  have hPB' := hPB
  obtain ⟨ha3, hpr, hp13, hBi, hdv, hdc, -, -, h2r, hkK, hNa⟩ := hPB'
  have hk : D.k = D.r + D.K := rfl
  have hn0 : D.n0 = D.Ns - D.r := rfl
  have hk' : D.k' = D.K - 2 * D.Ns := rfl
  have hK2 : 2 * D.Ns ≤ D.K := by omega
  have hk'1 : 1 ≤ D.k' := by omega
  have hnr : D.n0 + D.r = D.Ns := by omega
  have hmin : min D.Ns D.n0 = D.n0 := min_eq_right (by omega)
  have hSL : D.stLen D.Ns = D.K := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stLen
    omega
  have hstage : stage mu D.Ns = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns := by
    funext l
    simp only [Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stage, Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows]
    exact congrArg (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns) (by omega)
  have hRV : ∀ i, D.latestV i = Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B (min i D.n0) := fun i => rfl
  have hRC : ∀ i, D.latestC i = Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B (min i D.n0) := fun i => rfl
  have hP' := hP
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.IsPATH at hP'
  have hdomN : ∀ m, m + 1 < D.k → Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (m + 1) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns m := hP'.2.1 D.Ns le_rfl
  have hdomK : Dom D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) := by
    unfold Dom
    intro m hm
    show Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + (m + 1)) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m)
    rw [← Nat.add_assoc]
    exact hdomN (D.r + m) (by omega)
  have hposc : ((range D.K).filter fun m => 0 < Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m).card ≤ D.Ns := by
    calc _ ≤ (range D.Ns).card := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
          by_contra hc
          have := (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := D.Ns) (m := D.r + m) le_rfl (by omega)).2 (by omega)
          have e : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m) := rfl
          omega
      _ = D.Ns := Finset.card_range _
  have hnegc : ((range D.K).filter fun m => Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m < 0).card ≤ D.Ns := by
    calc _ ≤ (Ico (D.K - D.Ns) D.K).card := by
          apply Finset.card_le_card
          intro m hm
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hm ⊢
          refine ⟨?_, hm.1⟩
          by_contra hc
          have := (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := D.Ns) (m := D.r + m) le_rfl (by omega)).1 (by omega)
          have e : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu D.Ns (D.r + m) := rfl
          omega
      _ = D.Ns := by
          rw [Nat.card_Ico]
          omega
  have hC := (h21' D mu hW).2 hP
  have hlab : ∀ l, l < D.K → -(D.beNeg : ℤ) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns l ∧ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns l ≤ D.bePos := by
    intro l hl
    have h := hC.2.2.1 D.r le_rfl l (by omega)
    rw [hnr, hstage] at h
    exact ⟨le_trans hC.1 h.1, le_trans h.2 hC.2.1⟩
  have hbe : (D.be : ℝ) ≤ 2 * a * D.Ns := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_le D (by linarith) (fun i h1 h2 => (hBi i h1 h2).2)
  have hA0 : ((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 : ℤ) : ℝ) ≤ 2 * a * D.Ns := by
    have e := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_eq D
    have h0 := hlab 0 (by omega)
    have h1 := hlab (D.K - 1) (by omega)
    have hz : max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 ≤ (D.be : ℤ) := by
      have m1 : max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 ≤ (D.bePos : ℤ) := max_le h0.2 (by positivity)
      have m2 : max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 ≤ (D.beNeg : ℤ) := max_le (by linarith [h1.1]) (by positivity)
      rw [e]
      push_cast
      linarith
    have hz' : ((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns 0) 0 + max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns (D.K - 1))) 0 : ℤ) : ℝ) ≤ (D.be : ℝ) := by
      exact_mod_cast hz
    linarith
  have hLW := h32 D.r D.K D.Ns D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (2 * a * D.Ns) hK2 le_rfl (by omega) hdomK hposc hnegc hA0
  rw [← hk'] at hLW
  have hLR := (h33 D (2 * a) (by linarith) hr1 (by omega) hK2 (fun i h1 h2 => (hBi i h1 h2).2)).1
  have hsplitB : ∑ i ∈ Icc 1 D.n0, fT D.k' (D.B i : ℝ) =
      ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = true), fT D.k' (D.B i : ℝ) +
      ∑ i ∈ (Icc 1 D.n0).filter (fun i => (!D.vec i) = true), fT D.k' (D.B i : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro x _
    simp
  have hSv := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat (fun x : ℕ => fT D.k' (x : ℝ)) (fun l => D.vec l) D.B D.n0
  have hSc := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_lat (fun x : ℕ => fT D.k' (x : ℝ)) (fun l => !D.vec l) D.B D.n0
  have hLk : ∀ (q : ℕ → Bool) l, l < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat q D.B D.n0).length →
      D.k' ≤ (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat q D.B D.n0).getD l 0 := by
    intro q l hl
    obtain ⟨j, hj1, hj2, -, hx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem hl)
    rw [hx]
    have := (hBi j hj1 hj2).1
    omega
  have hp2 : 169 ≤ p ^ 2 := by
    calc 169 = 13 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp13 2
  have hL4v : ∀ l, l + 1 < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).length →
      4 * (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD (l + 1) 0 ≤
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD l 0 := by
    intro l hl
    have h := hdv l (by rw [hRV, min_self]; exact hl)
    rw [hRV, min_self] at h
    have h' := Nat.mul_le_mul hp2 (le_refl ((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).getD (l + 1) 0))
    linarith
  have hL4c : ∀ l, l + 1 < (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).length →
      4 * (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD (l + 1) 0 ≤
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD l 0 := by
    intro l hl
    have h := hdc l (by rw [hRC, min_self]; exact hl)
    rw [hRC, min_self] at h
    have h' := Nat.mul_le_mul hp2 (le_refl ((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).getD (l + 1) 0))
    linarith
  have hTv : ∀ u, tailPos D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) u ≤
      (((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0).drop u).sum : ℕ) := by
    intro u
    have h := ((h35 D mu hW hP).1 D.Ns u le_rfl).1
    rw [hSL, hstage] at h
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at h
    rw [hRV, hmin] at h
    exact h
  have hTc : ∀ u, tailPos D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns)) u ≤
      (((Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0).drop u).sum : ℕ) := by
    intro u
    have h := ((h35 D mu hW hP).1 D.Ns u le_rfl).2
    rw [hSL, hstage] at h
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg at h
    rw [hRC, hmin] at h
    exact h
  have hBv := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns)
    (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B D.n0) hk'1 (hLk _) hL4v hTv
  have hBc := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.bracket h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns))
    (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => !D.vec l) D.B D.n0) hk'1 (hLk _) hL4c hTc
  have hrefl : ∑ m ∈ range D.K, fT D.k' ((max (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) m) 0 : ℤ) : ℝ) =
      ∑ m ∈ range D.K, fT D.k' ((max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m)) 0 : ℤ) : ℝ) :=
    Finset.sum_range_reflect (fun m => fT D.k' ((max (-(Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns m)) 0 : ℤ) : ℝ)) D.K
  have hx2 : 0 ≤ 2 * a * (D.Ns : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hL0 : 0 ≤ Real.log (1 + 2 * a * D.Ns) := Real.log_nonneg (by linarith)
  have hcoef : (2 * (D.Ns : ℝ) * D.r + 8 * (D.Ns : ℝ) ^ 2) * Real.log (1 + 2 * a * D.Ns) ≤
      9 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns) := by
    have h2r' : 2 * (D.r : ℝ) ≤ D.Ns := by exact_mod_cast h2r
    have hN0 : (0 : ℝ) ≤ D.Ns := Nat.cast_nonneg _
    have : 2 * (D.Ns : ℝ) * D.r + 8 * (D.Ns : ℝ) ^ 2 ≤ 9 * (D.Ns : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hL0
  have hw : Formalism.InvariantFactorPaths.BranchingDimensions.Letters.wt mu = weylDim D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) := rfl
  have hwpos : 0 < Formalism.InvariantFactorPaths.BranchingDimensions.Letters.wt mu := by rw [hw]; exact hLW.1
  have hTpos : (0 : ℝ) < D.rankAA := by
    have : 0 < D.rankAA := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.rankAA
      exact Finset.prod_pos (fun i _ => Nat.choose_pos (by omega))
    exact_mod_cast this
  have hbase := hLW.2.2
  refine ⟨le_exp_mul_of_log_le_add_log hwpos hTpos (by
    rw [hw]
    linarith [hBv.1, hBc.1]), fun hnt => ?_⟩
  apply le_exp_mul_of_log_le_add_log hwpos hTpos
  rw [hw]
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.Typical at hnt
  have hTD' := hTD
  obtain ⟨hLa, hTDb⟩ := hTD'
  have hkR : (0 : ℝ) < D.k := by
    have : 0 < D.k := by omega
    exact_mod_cast this
  have hpR : (0 : ℝ) < p := by
    have := hpr.pos
    exact_mod_cast this
  have hk'R : (0 : ℝ) ≤ D.k' := Nat.cast_nonneg _
  have hm1 := min_le_left (La * D.k' / (16 * D.k)) ((D.k' : ℝ) / 12)
  have hm2 := min_le_right (La * D.k' / (16 * D.k)) ((D.k' : ℝ) / 12)
  rcases not_and_or.mp hnt with hc1 | hc23
  · push_neg at hc1
    obtain ⟨i, hi1, hiN, hvi, hgt⟩ := hc1
    have hir : D.r < i := by
      by_contra h
      push_neg at h
      have := hvr i hi1 h
      simp [this] at hvi
    have hin0 : i ≤ D.n0 := by
      by_contra h
      push_neg at h
      have := hvn i h hiN
      simp [this] at hvi
    have hX : D.XT p La b i = La * b i / (p * D.k) := rfl
    have hbpos := (hTDb i hir hiN).1
    have hB4 := (hTDb i hir hiN).2
    have hXpos : 0 < D.XT p La b i := by
      rw [hX]
      exact div_pos (mul_pos hLa hbpos) (mul_pos hpR hkR)
    have t1 := ((h35 D mu hW hP).1 (i - 1) 0 (by omega)).1
    have heqv : D.SPos 0 (i - 1) = D.SPos 0 i := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos
      rw [hRV, hRV, min_eq_left (by omega : i - 1 ≤ D.n0), min_eq_left hin0,
        Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_pred (fun l => D.vec l) D.B (i := i) (by omega) hvi]
    have hd1 : ((tailPos (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ (D.SPos 0 i : ℝ) - D.XT p La b i := by
      have t1R : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) 0 : ℤ) : ℝ) ≤ (D.SPos 0 (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [heqv] at t1R
      rw [Int.cast_sub] at hgt
      linarith
    have t2 := (h35 D mu hW hP).2.1 i 0 (D.XT p La b i) hiN hXpos.le hd1
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at t2
    rw [hRV, min_self] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (fun l => D.vec l) D.B D.n0 hk'1
      (hLk _) hL4v hTv i 0 _ hXpos t2
    obtain ⟨l, hl1, hl2, hql, hgx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem td.1)
    have hli : l ≠ i := by
      rintro rfl
      simp [hql] at hvi
    have hlmin := min_le_left i D.n0
    have hlmin' := min_le_right i D.n0
    have hgle : (D.B l : ℝ) ≤ 4 * b i / p := hB4 l hl1 (by omega) (by omega)
    have hg0 : (0 : ℝ) < D.B l := by
      have := (hBi l hl1 (by omega)).1
      have : 0 < D.B l := by omega
      exact_mod_cast this
    have hthr := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin hLa hpR hkR hk'R hg0 hgle
    have td2 := td.2
    rw [hgx, hX] at td2
    linarith [hBv.1, hBc.1]
  rcases not_and_or.mp hc23 with hc2 | hc3
  · push_neg at hc2
    obtain ⟨i, hir, hiN, hvi, hgt⟩ := hc2
    have hX : D.XT p La b i = La * b i / (p * D.k) := rfl
    have hbpos := (hTDb i hir hiN).1
    have hB4 := (hTDb i hir hiN).2
    have hXpos : 0 < D.XT p La b i := by
      rw [hX]
      exact div_pos (mul_pos hLa hbpos) (mul_pos hpR hkR)
    have t1 := ((h35 D mu hW hP).1 (i - 1) 0 (by omega)).2
    have heqc : D.SNeg 0 (i - 1) = D.SNeg 0 i := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg
      rw [hRC, hRC]
      by_cases hin : i ≤ D.n0
      · rw [min_eq_left (by omega : i - 1 ≤ D.n0), min_eq_left hin,
          Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat_pred (fun l => !D.vec l) D.B (i := i) (by omega) (by simp [hvi])]
      · rw [min_eq_right (by omega : D.n0 ≤ i - 1), min_eq_right (by omega : D.n0 ≤ i)]
    have hd2 : ((tailNeg (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ (D.SNeg 0 i : ℝ) - D.XT p La b i := by
      have t1R : ((tailNeg (D.stLen (i - 1)) (stage mu (i - 1)) 0 : ℤ) : ℝ) ≤ (D.SNeg 0 (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [heqc] at t1R
      rw [Int.cast_sub] at hgt
      linarith
    have t2 := (h35 D mu hW hP).2.2 i 0 (D.XT p La b i) hiN hXpos.le hd2
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SNeg at t2
    rw [hRC, min_self] at t2
    have hfc : ((Icc (i + 1) D.n0).filter (fun l => D.vec l = false)) =
        ((Icc (i + 1) D.n0).filter (fun l => (!D.vec l) = true)) :=
      Finset.filter_congr (fun x _ => by simp)
    rw [hfc] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.revW D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns))
      (fun l => !D.vec l) D.B D.n0 hk'1 (hLk _) hL4c hTc i 0 _ hXpos t2
    obtain ⟨l, hl1, hl2, hql, hgx⟩ := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.mem_lat (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem td.1)
    have hli : l ≠ i := by
      rintro rfl
      simp [hvi] at hql
    have hlmin := min_le_left i D.n0
    have hlmin' := min_le_right i D.n0
    have hgle : (D.B l : ℝ) ≤ 4 * b i / p := hB4 l hl1 (by omega) (by omega)
    have hg0 : (0 : ℝ) < D.B l := by
      have := (hBi l hl1 (by omega)).1
      have : 0 < D.B l := by omega
      exact_mod_cast this
    have hthr := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin hLa hpR hkR hk'R hg0 hgle
    have td2 := td.2
    rw [hgx, hX] at td2
    linarith [hBv.1, hBc.1]
  · push_neg at hc3
    obtain ⟨i, hir, hiN, hgt⟩ := hc3
    have hh : D.Bo i =
        (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.lat (fun l => D.vec l) D.B (min (i - 1) D.n0)).getD (D.r - 1 - (i - 1 - D.n0)) 0 := rfl
    have hent0 : 0 ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) :=
      (Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign h20 hW hP (i := i - 1) (m := D.r - 1) (by omega) (by omega)).1 (by omega)
    have hhpos : (0 : ℝ) < D.Bo i := by
      rcases Nat.eq_zero_or_pos (D.Bo i) with h0 | h0
      · have hz : ((D.Bo i : ℕ) : ℝ) = 0 := by rw [h0]; simp
        have : (0 : ℝ) ≤ Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) := by exact_mod_cast hent0
        linarith
      · exact_mod_cast h0
    have hstu : stage mu (i - 1) (D.r - 1 - (i - 1 - D.n0)) = Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1) := by
      simp only [Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stage]
      exact congrArg (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1)) (by omega)
    have hus : D.r - 1 - (i - 1 - D.n0) < D.stLen (i - 1) := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.stLen
      omega
    have hsplitT := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.tailPos_split (D.stLen (i - 1)) (stage mu (i - 1)) hus
    rw [hstu] at hsplitT
    have t1 := ((h35 D mu hW hP).1 (i - 1) (D.r - 1 - (i - 1 - D.n0) + 1) (by omega)).1
    have hds : D.SPos (D.r - 1 - (i - 1 - D.n0)) (i - 1) =
        D.Bo i + D.SPos (D.r - 1 - (i - 1 - D.n0) + 1) (i - 1) := by
      unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos Formalism.InvariantFactorPaths.BranchingDimensions.Letters.Bo
      exact Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.drop_split _ _
    have hmx : (((max (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.ent mu (i - 1) (D.r - 1)) 0 : ℤ)) : ℝ) ≤ (2 / 3) * (D.Bo i : ℝ) := by
      rw [max_eq_left hent0]
      exact hgt.le
    have hd3 : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) (D.r - 1 - (i - 1 - D.n0)) : ℤ) : ℝ) ≤
        (D.SPos (D.r - 1 - (i - 1 - D.n0)) (i - 1) : ℝ) - (D.Bo i : ℝ) / 3 := by
      have t1R : ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) (D.r - 1 - (i - 1 - D.n0) + 1) : ℤ) : ℝ) ≤
          (D.SPos (D.r - 1 - (i - 1 - D.n0) + 1) (i - 1) : ℝ) := by
        exact_mod_cast t1
      rw [hsplitT, hds, Int.cast_add, Nat.cast_add]
      linarith
    have hX3 : (0 : ℝ) < (D.Bo i : ℝ) / 3 := by linarith
    have t2 := (h35 D mu hW hP).2.1 (i - 1) (D.r - 1 - (i - 1 - D.n0)) ((D.Bo i : ℝ) / 3) (by omega) hX3.le hd3
    rw [hSL, hstage] at t2
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.SPos at t2
    rw [hRV, min_self] at t2
    have td := Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.key h31 h34 D.k' D.K (Formalism.InvariantFactorPaths.BranchingDimensions.Letters.kaRows mu D.Ns) (fun l => D.vec l) D.B D.n0 hk'1
      (hLk _) hL4v hTv (i - 1) (D.r - 1 - (i - 1 - D.n0)) _ hX3 t2
    have td2 := td.2
    rw [← hh] at td2
    have hne : (D.Bo i : ℝ) ≠ 0 := ne_of_gt hhpos
    have e12 : (D.Bo i : ℝ) / 3 * D.k' / (4 * D.Bo i) = D.k' / 12 := by
      field_simp
      ring
    rw [e12] at td2
    linarith [hBv.1, hBc.1]
end Formalism.InvariantFactorPaths.BranchingDimensions
