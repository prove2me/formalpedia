-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.oneLevelOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.807168+00:00
-- url     : https://prove2.me/submissions/7fee4d52-29a7-49c2-abd3-f1951f7b6af2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_bud_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_bud_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_bud_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_sizes_tie
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_le_wsup
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_wsup_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_sqrt_le_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_exists_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds
namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds
theorem _root_.solution : OneLevelOfSteps := by
  intro hSplit hOff hTop hDC hC1 hCS
  intro E _ _ H _ _ W _ len Kl D Sg Φ tr Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 ep a i
    hNZ h1 hi hep ha hK hA2 hA13 hE hEst hSz
  obtain ⟨hPo, h72, h73, h74⟩ := hEst
  obtain ⟨hep1, htie⟩ := sizes_tie _ _ _ _ _ _ _ _ _ _ hSz
  obtain ⟨hL1, hL3, hep3, hs1, hs2⟩ := hSz
  obtain ⟨he0, he1⟩ := hE i h1 hi
  have hP : (0:ℝ) ≤ Fintype.card Pat3 := Nat.cast_nonneg _

  have hD1 : ∀ w', len w' + Kl ≤ 4 * Kl * (D.r + 1 - (i - 1)) → len w' + Kl ≤ 4 * Kl * (D.r + 1) →
      Diag D Sg Φ w' i 1 ≤ (1 + D.e i) * (1 + ep1) * lsup D len Kl Sg Φ (i - 1) := by
    intro w' hb hbN
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La i 1) (Sg i 1)
    have a1 := hDC E H W D Sg Φ w' i 1 R hNZ le_rfl h1 hi hA13 hR1 hR2
    have a2 := hC1 E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ tr Pat1 pat1 c1 ep1 i w' R hNZ h1 hi hK hA13 hE
      hPo h72 hL1 hbN hR2
    have a3 : Slev D Sg Φ w' (i - 1) ≤ lsup D len Kl Sg Φ (i - 1) :=
      le_wsup len _ (fun w => Slev D Sg Φ w (i - 1)) w' (le_trans (Nat.le_add_right _ _) hb)
    have a4 : wsup len (len w' + Kl) (fun w'' => Slev D Sg Φ w'' (i - 1)) ≤ lsup D len Kl Sg Φ (i - 1) :=
      wsup_le len _ _ _ w' (Nat.le_add_right _ _) fun w'' hw'' =>
        le_wsup len _ (fun w => Slev D Sg Φ w (i - 1)) w'' (le_trans hw'' hb)
    calc Diag D Sg Φ w' i 1 ≤ _ := le_trans a1 a2
      _ ≤ (1 + D.e i) * (lsup D len Kl Sg Φ (i - 1) + ep1 * lsup D len Kl Sg Φ (i - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact add_le_add a3 (mul_le_mul_of_nonneg_left a4 hep1)
      _ = _ := by ring

  have hDs : ∀ s ∈ Icc 2 i, ∀ w', len w' + (s + 1) * Kl ≤ 4 * Kl * (D.r + 1 - (i - s)) →
      len w' + (s + 1) * Kl ≤ 4 * Kl * (D.r + 1) →
      Diag D Sg Φ w' i s ≤ (1 + D.e i) * bd4 s * lsup D len Kl Sg Φ (i - s) := by
    intro s hs w' hb hbN
    obtain ⟨hs2', hsi⟩ := Finset.mem_Icc.mp hs
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La i s) (Sg i s)
    have a1 := hDC E H W D Sg Φ w' i s R hNZ (by omega) hsi hi hA13 hR1 hR2
    have a2 := hCS E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ (bd4 s) i s w' R hNZ hs2' hsi hi hK hA13 hE
      (hs2 s hs).1 (h74 s hs) hbN hR2
    have a4 : wsup len (len w' + (s + 1) * Kl) (fun w'' => Slev D Sg Φ w'' (i - s)) ≤
        lsup D len Kl Sg Φ (i - s) :=
      wsup_le len _ _ _ w' (Nat.le_add_right _ _) fun w'' hw'' =>
        le_wsup len _ (fun w => Slev D Sg Φ w (i - s)) w'' (le_trans hw'' hb)
    exact le_trans (le_trans a1 a2)
      (mul_le_mul_of_nonneg_left a4 (mul_nonneg (by linarith) (hs2 s hs).1))

  have hSch : ∀ s ∈ Icc 1 i, ¬ (i = D.r + 1 ∧ s = 1) → ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → ∀ M : ℝ,
      (∀ w', len w' ≤ len w + Kl → Diag D Sg Φ w' i s ≤ M) →
      Ssplit D Sg Φ w i s ≤ (1 + Fintype.card Pat3 * ep3 s) * M := by
    intro s hs hnt w hw M hM
    obtain ⟨hs1', hsi⟩ := Finset.mem_Icc.mp hs
    have hl := hL3 s hs hnt
    have hep3s : 0 ≤ ep3 s := by simpa using hl.2 ∅ (by simp)
    have b1 := hOff E H W len Kl (4 * Kl * (D.r + 1)) D Sg Φ Pat3 (pat3 s) (c3 s) (ep3 s) i s w hNZ hs1' hsi hi
      hK hA2 (h73 s hs hnt) hl (bud_lift Kl D.r i (len w) h1 hi hw)
    have b2 : wsup len (len w + Kl) (fun w' => Diag D Sg Φ w' i s) ≤ M :=
      wsup_le len _ _ _ w (Nat.le_add_right _ _) hM
    have b3 := hM w (Nat.le_add_right _ _)
    have b4 := mul_le_mul_of_nonneg_left b2 (mul_nonneg hP hep3s)
    calc Ssplit D Sg Φ w i s ≤ _ := b1
      _ ≤ M + Fintype.card Pat3 * ep3 s * M := add_le_add b3 b4
      _ = _ := by ring
  have hd1 : ((1 + ep) * √(1 + D.e i)) ^ 2 = (1 + ep) ^ 2 * (1 + D.e i) := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]

  have key1 : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) →
      √(Ssplit D Sg Φ w i 1) ≤ (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) := by
    intro w hw
    have hd0 : 0 ≤ (1 + ep) * √(1 + D.e i) := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    by_cases htop : i = D.r + 1
    · have c1' := hTop E H W D Sg Φ w hNZ hA2
      rw [← htop] at c1'
      obtain ⟨q1, q2⟩ := bud_one Kl D.r i (len w) (len w) h1 hi hw (Nat.le_add_right _ _)
      have c2 := hD1 w q1 (le_trans q1 q2)
      rw [← c1'] at c2
      refine sqrt_le_of c2 (mul_nonneg (by linarith) (by linarith)) ?_ hd0
      rw [hd1]
      nlinarith
    · have hnt : ¬ (i = D.r + 1 ∧ (1:ℕ) = 1) := fun h => htop h.1
      have c2 := hSch 1 (Finset.mem_Icc.mpr ⟨le_rfl, h1⟩) hnt w hw _ (fun w' hw' => by
        obtain ⟨q1, q2⟩ := bud_one Kl D.r i (len w) (len w') h1 hi hw hw'
        exact hD1 w' q1 (le_trans q1 q2))
      rw [← mul_assoc] at c2
      refine sqrt_le_of c2 (mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))) ?_ hd0
      rw [hd1]
      nlinarith

  have keys : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → ∀ s ∈ Icc 2 i,
      √(Ssplit D Sg Φ w i s) ≤ a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    intro w hw s hs
    obtain ⟨hs2', hsi⟩ := Finset.mem_Icc.mp hs
    have hs' : s ∈ Icc 1 i := Finset.mem_Icc.mpr ⟨by omega, hsi⟩
    have hnt : ¬ (i = D.r + 1 ∧ s = 1) := fun h => by omega
    have hep3s : 0 ≤ ep3 s := by simpa using (hL3 s hs' hnt).2 ∅ (by simp)
    have c2 := hSch s hs' hnt w hw _ (fun w' hw' => by
      obtain ⟨q1, q2⟩ := bud_block Kl D.r i s (len w) (len w') hs2' hsi hi hw hw'
      exact hDs s hs w' q1 (le_trans q1 q2))
    rw [← mul_assoc] at c2
    refine sqrt_le_of c2 (mul_nonneg (by positivity) (mul_nonneg (by linarith) (hs2 s hs).1)) ?_
      (pow_nonneg ha _)
    rw [← pow_mul, mul_comm (s - 1) 2, ← mul_assoc]
    exact (hs2 s hs).2

  have hRHS0 : 0 ≤ (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    refine add_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg ha _) (Real.sqrt_nonneg _))
  have hw : ∀ w, len w ≤ 4 * Kl * (D.r + 1 - i) → √(Slev D Sg Φ w i) ≤
      (1 + ep) * √(1 + D.e i) * √(lsup D len Kl Sg Φ (i - 1)) +
        ∑ s ∈ Icc 2 i, a ^ (s - 1) * √(lsup D len Kl Sg Φ (i - s)) := by
    intro w hw
    have hPSD : PSDOn (PT Sg i) (D.K i) := hK.2 i hi _ (fun p hp => isPt_PT Sg hNZ i p hp)
    have h0 := hSplit E H W D Sg Φ w i hNZ h1 hPSD
    have hIcc : Icc 1 i = insert 1 (Icc 2 i) := by ext x; simp; omega
    rw [hIcc, Finset.sum_insert (by simp)] at h0
    exact le_trans h0 (add_le_add (key1 w hw) (Finset.sum_le_sum fun s hs => keys w hw s hs))
  rw [Real.sqrt_le_iff]
  refine ⟨hRHS0, ?_⟩
  by_cases hne : Nonempty {w // len w ≤ 4 * Kl * (D.r + 1 - i)}
  · unfold lsup wsup
    exact ciSup_le fun w => ((Real.sqrt_le_iff).1 (hw w.1 w.2)).2
  · unfold lsup wsup
    have := not_nonempty_iff.mp hne
    rw [Real.iSup_of_isEmpty]
    positivity
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
