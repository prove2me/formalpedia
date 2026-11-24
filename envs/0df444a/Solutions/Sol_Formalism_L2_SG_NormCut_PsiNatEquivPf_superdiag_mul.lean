-- Prove2me | solution 1 for Formalism.L2.SG.NormCut.PsiNatEquivPf.superdiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:47.225935+00:00
-- url     : https://prove2.me/submissions/fa6f5b11-29aa-4b18-9f17-3a3cc6b6d196

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCorePsiNatEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut Formalism.L2.SG.NormCut.PsiNatEquivPf
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace Formalism.L2.SG.NormCut.PsiNatEquivPf
theorem _root_.solution {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by
  obtain ⟨hA1, hA0⟩ := hA
  obtain ⟨hB1, hB0⟩ := hB

  have key : ∀ i j : Fin k, (j : ℕ) = (i : ℕ) + 1 → (A * B) i j = A i j + B i j := by
    intro i j hij
    have hij' : i < j := by
      rw [Fin.lt_iff_val_lt_val]
      omega
    rw [Matrix.mul_apply, Finset.sum_eq_add i j (ne_of_lt hij')]
    · rw [hA1 i, hB1 j, one_mul, mul_one, add_comm]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc.1 with h | h
      · rw [hA0 i c h, zero_mul]
      · have h' : j < c := by
          have h1 : (i : ℕ) < c := h
          have h2 : (c : ℕ) ≠ j := fun e => hc.2 (Fin.ext e)
          rw [Fin.lt_iff_val_lt_val]
          omega
        rw [hB0 c j h', mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [superdiag]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · exact key i j h
  · rw [add_zero]
end Formalism.L2.SG.NormCut.PsiNatEquivPf
