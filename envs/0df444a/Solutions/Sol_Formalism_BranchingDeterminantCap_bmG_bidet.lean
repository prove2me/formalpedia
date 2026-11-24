-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_bidet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:04.209861+00:00
-- url     : https://prove2.me/submissions/72608f1b-5b1c-453f-b479-422b9675b860

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_mul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor0
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_minor1
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_cast
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shapeDeg_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shapeDeg_zero
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shapeDeg_anti
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_bidet_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_of_succ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_nuNext_last
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_base
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (lam : Fin n → ℕ), bmIL lam (shapeDeg sz) →
    ∃ G, bmLift R n lam (fun s => lam s - shapeDeg sz s) (bideterminant R sz hsz I) G := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I lam hIL
    have h0 : (shapeDeg sz : Fin n → ℕ) = 0 := bmG_shapeDeg_zero sz
    obtain ⟨G, hG⟩ := bmG_base R n lam (fun i => by
      have := (hIL i).2
      rw [h0] at this
      simpa using this)
    refine ⟨G, bmG_cast hG rfl ?_ ?_ rfl⟩
    · funext s; rw [h0]; simp
    · unfold bideterminant; simp
  | succ K ih =>
    intro sz hsz I lam hIL
    have hsg : ∀ t : Fin n, shapeDeg sz t =
        (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t :=
      bmG_shapeDeg_succ sz
    have hanti : Antitone (shapeDeg (fun k : Fin K => sz k.succ) : Fin n → ℕ) := bmG_shapeDeg_anti _
    by_cases hA : ∀ i : Fin n, i.val + 1 = sz 0 → nuNext lam i < shapeDeg sz i
    ·
      have hIL' : bmIL (fun t => lam t - (if t.val < sz 0 then 1 else 0))
          (shapeDeg (fun k : Fin K => sz k.succ)) := by
        intro t
        constructor
        · have h1 := (hIL t).1
          rw [hsg t] at h1
          show _ ≤ lam t - (if t.val < sz 0 then 1 else 0)
          split_ifs at h1 ⊢ <;> omega
        · by_cases ht : t.val + 1 < n
          · have h2 := (hIL t).2
            rw [bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]
            have h3 := hA t
            rw [bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl] at h2 h3
            rw [hsg t] at h2 h3
            show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 then 1 else 0) ≤ _
            by_cases h4 : t.val + 1 = sz 0
            · have h5 := h3 h4
              rw [if_neg (by omega)]
              rw [if_pos (by omega)] at h5
              omega
            · split_ifs at h2 ⊢ <;> omega
          · rw [bmG_nuNext_last _ t ht]; exact Nat.zero_le _
      obtain ⟨G', hG'⟩ := ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'
      refine ⟨_, bmG_cast (bmLift_mul (bmLift_minor0 R n (I 0) (hsz 0)) hG') ?_ ?_
        (bmG_bidet_succ R sz hsz I).symm rfl⟩
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, initW]
        split_ifs at h1 ⊢ <;> omega
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, Pi.zero_apply]
        rw [hsg t]
        split_ifs at h1 ⊢ <;> omega
    ·
      push Not at hA
      obtain ⟨i, hij, hle⟩ := hA
      have hi1 : 1 ≤ shapeDeg sz i := by rw [hsg i, if_pos (by omega)]; omega
      have hin : i.val + 1 < n := by
        by_contra hcon
        rw [bmG_nuNext_last lam i hcon] at hle
        omega
      have hs : sz 0 + 1 ≤ n := by omega
      have hlj : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) + 1 ≤ lam ⟨sz 0, hs⟩ := by
        rw [bmG_nuNext_of_succ lam i ⟨sz 0, hs⟩ hij.symm, hsg i, if_pos (by omega)] at hle
        have h5 : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) ≤
            shapeDeg (fun k : Fin K => sz k.succ) i := hanti (Fin.le_def.mpr (by simp; omega))
        omega
      have hIL' : bmIL (fun t => lam t - (if t.val < sz 0 + 1 then 1 else 0))
          (shapeDeg (fun k : Fin K => sz k.succ)) := by
        intro t
        constructor
        · have h1 := (hIL t).1
          rw [hsg t] at h1
          show _ ≤ lam t - (if t.val < sz 0 + 1 then 1 else 0)
          by_cases h4 : t.val = sz 0
          · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
            rw [h6]
            rw [if_pos (by simp)]
            omega
          · split_ifs at h1 ⊢ <;> omega
        · by_cases ht : t.val + 1 < n
          · have h2 := (hIL t).2
            rw [bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]
            rw [bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl] at h2
            rw [hsg t] at h2
            show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 + 1 then 1 else 0) ≤ _
            split_ifs at h2 ⊢ <;> omega
          · rw [bmG_nuNext_last _ t ht]; exact Nat.zero_le _
      obtain ⟨G', hG'⟩ := ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'
      refine ⟨_, bmG_cast (bmLift_mul (bmLift_minor1 R n (I 0) hs) hG') ?_ ?_
        (bmG_bidet_succ R sz hsz I).symm rfl⟩
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, initW]
        by_cases h4 : t.val = sz 0
        · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
          rw [h6]
          rw [if_pos (by simp)]
          omega
        · split_ifs at h1 ⊢ <;> omega
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, Pi.single_apply]
        rw [hsg t]
        by_cases h4 : t.val = sz 0
        · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
          rw [h6]
          rw [if_pos rfl, if_pos (by simp), if_neg (by simp)]
          omega
        · rw [if_neg (fun hh => h4 (by rw [hh]))]
          split_ifs at h1 ⊢ <;> omega
end Formalism.BranchingDeterminantCap
