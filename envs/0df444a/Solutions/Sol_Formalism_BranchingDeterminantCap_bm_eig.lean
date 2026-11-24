-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:19.600152+00:00
-- url     : https://prove2.me/submissions/51744b77-16c4-441d-826e-894cc07260bc

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_zW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_weight_lastW
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmZ_iter_inj
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_eigen
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_isWH
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_raise
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_weight
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_nil
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_top
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (G : BP R n)
    (hG : G ∈ dualWeyl R (n + 1) n lam) (hd : IsWeightedHomogeneous (lastW n) G d) (β : Fin n → ℤ)
    (hβ : zcomp R n β G ≠ 0) (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) :
    bmAdm lam d β ∧ ∀ u, bmCap R n u (zcomp R n β G) = ((bmChi lam β u : ℤ) : R) • zcomp R n β G := by
  classical
  constructor
  ·
    obtain ⟨m, hm⟩ : ∃ m, coeff m (zcomp R n β G) ≠ 0 := by
      by_contra hcon
      refine hβ (MvPolynomial.ext _ _ fun m => ?_)
      rw [coeff_zero]
      by_contra hm0
      exact hcon ⟨m, hm0⟩
    have hm' : Finsupp.weight (zW n) m = β ∧ coeff m G ≠ 0 := by
      unfold zcomp at hm
      rw [coeff_weightedHomogeneousComponent] at hm
      by_cases hw : Finsupp.weight (zW n) m = β
      · rw [if_pos hw] at hm
        exact ⟨hw, hm⟩
      · rw [if_neg hw] at hm
        exact absurd rfl hm
    obtain ⟨hmw, hmG⟩ := hm'
    have hβs : ∀ s, β s = (m (Fin.last n, s) : ℤ) := fun s => by rw [← hmw, bm_weight_zW]
    have hpos : ∀ s, 0 ≤ β s := fun s => by rw [hβs]; exact Int.natCast_nonneg _
    have hcol : ∀ t : Fin n, ∑ a : Fin (n + 1), m (a, t) = lam t :=
      colSums R (n + 1) n lam G hG m (mem_support_iff.2 hmG)
    refine ⟨hpos, ?_, fun i => ⟨?_, ?_⟩⟩
    · have h1 : Finsupp.weight (lastW n) m = d := hd hmG
      rw [bm_weight_lastW] at h1
      rw [← h1]
      unfold rowDeg
      push_cast
      exact Finset.sum_congr rfl fun s _ => hβs s
    · have : lamZ lam i.castSucc = (lam i : ℤ) := by
        unfold lamZ
        rw [dif_pos (by simp : (i.castSucc : Fin (n + 1)).val < n)]
        rfl
      rw [this]
      have := hpos i
      linarith
    · by_cases hi : i.val + 1 < n
      · have hz : lamZ lam i.succ = (lam ⟨i.val + 1, hi⟩ : ℤ) := by
          unfold lamZ
          rw [dif_pos (by simpa using hi : (i.succ : Fin (n + 1)).val < n)]
          rfl
        rw [hz]
        by_contra hcon
        have hcon := not_le.mp hcon
        set j : Fin n := ⟨i.val + 1, hi⟩ with hjdef
        have hij : i < j := by
          rw [Fin.lt_def]; simp [hjdef]
        obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β i := ⟨(β i).toNat, Int.toNat_of_nonneg (hpos i)⟩
        have hnil := bmD_nil lam G hG i j hij k (by rw [hk]; linarith)
        have htop := (bmD_top G β hmax i j rfl k).2.2
        rw [hnil, map_zero] at htop
        exact hβ (bmZ_iter_inj R n j i (ne_of_gt hij) k β _ (bmD_zcomp_isWH β G) (le_of_eq hk)
          htop.symm)
      · have hz : lamZ lam i.succ = 0 := by
          unfold lamZ
          rw [dif_neg (by simpa using hi : ¬ (i.succ : Fin (n + 1)).val < n)]
        rw [hz]
        show (0 : ℤ) ≤ (lam i : ℤ) - β i
        rw [hβs, ← hcol i]
        have : m (Fin.last n, i) ≤ ∑ a : Fin (n + 1), m (a, i) :=
          Finset.single_le_sum (f := fun a : Fin (n + 1) => m (a, i)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ (Fin.last n))
        have h2 : ((m (Fin.last n, i) : ℕ) : ℤ) ≤ ((∑ a : Fin (n + 1), m (a, i) : ℕ) : ℤ) := by
          exact_mod_cast this
        linarith
  · intro u
    unfold bmCap bmChi
    exact capDet_eigen (bmEL R n) u (zcomp R n β G) (fun s => (lam s : ℤ) - β s)
      (fun l j hlj => bmD_raise lam G hG β hmax l j hlj) (fun s => bmD_weight lam G hG β s)
end Formalism.BranchingDeterminantCap
