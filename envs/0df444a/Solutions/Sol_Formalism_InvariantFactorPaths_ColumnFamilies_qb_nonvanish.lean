-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_nonvanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:27.840393+00:00
-- url     : https://prove2.me/submissions/2fff1e22-aa4e-4bb9-be8b-ff987bb19e83

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_key_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_indep_ext
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_indepF
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (F : Type) [Field F] (a : qb_Idx CF → F)
    (nu : Fin n → ℤ) (hmax : ∀ x, a x ≠ 0 → DomLE nu (CF.mu x.1) → CF.mu x.1 = nu)
    (h0 : qb_ev M F nu (∑ x, a x • qb_vecF CF F x) = 0) : ∀ x, CF.mu x.1 = nu → a x = 0 := by
  rw [← qb_evL_apply, map_sum] at h0
  simp only [map_smul, qb_evL_apply] at h0
  let f : CF.J → GLCoord F n := fun j => ∑ I : {I : TIdx (CF.mu j) // StdT I}, a ⟨j, I⟩ • mapCoord F (brk (CF.mu j) I.1)
  have h2 : ∀ (x : qb_Idx CF) (i : M.ι), (a x • qb_ev M F nu (qb_vecF CF F x)) i =
      if CF.mu x.1 = nu then (CF.ph x.1 i (canT (CF.mu x.1)) : GLCoord F n) *
        (a x • mapCoord F (brk (CF.mu x.1) x.2.1)) else 0 := by
    intro x i
    split_ifs with hx
    · subst hx
      rw [Pi.smul_apply, qb_vecF_def, qb_key_eq, mul_smul_comm]
    · by_cases hax : a x = 0
      · rw [hax, zero_smul]; rfl
      · rw [qb_vecF_def, qb_key_zero CF F x.1 x.2.1 nu (fun hle => hx (hmax x hax hle)), smul_zero]; rfl
  have h3 : ∀ i, ∑ j : {j : CF.J // CF.mu j = nu}, ((CF.ph j.1 i (canT (CF.mu j.1)) : ℤ) : F) • f j.1 = 0 := by
    intro i
    have h4 := congrFun h0 i
    rw [Finset.sum_apply, Pi.zero_apply] at h4
    simp only [h2] at h4
    rw [Fintype.sum_sigma] at h4
    rw [← sum_subtype (univ.filter fun j => CF.mu j = nu) (by simp)
      (fun j => ((CF.ph j i (canT (CF.mu j)) : ℤ) : F) • f j), sum_filter]
    refine Eq.trans ?_ h4
    refine sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp only [f, Algebra.smul_def, map_intCast, mul_sum]
    · simp
  have h5 := qb_indep_ext (k := F) _ (qb_indepF CF F nu) (fun j => f j.1) h3
  rintro ⟨j, I⟩ hj
  exact Fintype.linearIndependent_iff.1 (hA n (CF.mu j) (CF.dom j) F) (fun I => a ⟨j, I⟩) (h5 ⟨j, hj⟩) I
end Formalism.InvariantFactorPaths.ColumnFamilies
