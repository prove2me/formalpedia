-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.cap_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:05.8438+00:00
-- url     : https://prove2.me/submissions/98eae355-3c1b-4ff9-ad74-8a4f21686eb2

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_interlace_antitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ} (h : Interlace lam sg)
    (i j : Fin n) (v : ℤ) (hv : v ∈ (rset lam sg i).erase (sg i)) :
    ((v - (i : ℤ)) - (sg j - (j : ℤ))) ≠ 0 ∧
    |((v - (i : ℤ)) - (sg j - (j : ℤ)))| ≤ lam 0 - lam (Fin.last n) + (n : ℤ) - 1 := by
  have hA := interlace_antitone h
  have hv' := Finset.mem_of_mem_erase hv
  have hne : v ≠ sg i := Finset.ne_of_mem_erase hv
  unfold rset at hv'
  rw [Finset.mem_Icc] at hv'
  obtain ⟨hv1, hv2⟩ := hv'
  have hv3 : v ≤ lam i.castSucc := le_trans hv2 (min_le_left _ _)
  have hlo : lam (Fin.last n) ≤ v := le_trans (hA (Fin.le_last _)) hv1
  have hhi : v ≤ lam 0 := le_trans hv3 (hA (Fin.zero_le _))
  have hs1 : lam (Fin.last n) ≤ sg j := le_trans (hA (Fin.le_last _)) (h j).2
  have hs2 : sg j ≤ lam 0 := le_trans (h j).1 (hA (Fin.zero_le _))
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  constructor
  · intro heq
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with hji | hji | hji
    · have h3 : lam i.castSucc ≤ lam j.succ :=
        hA (Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega))
      have h4 := (h j).2
      omega
    · have hij : j = i := Fin.ext hji
      subst hij
      exact hne (by omega)
    · have h3 : lam j.castSucc ≤ lam i.succ :=
        hA (Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega))
      have h4 := (h j).1
      omega
  · rw [abs_le]
    constructor <;> omega
end Formalism.BranchingDeterminantCap
