-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.sUp_blkM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:19.006313+00:00
-- url     : https://prove2.me/submissions/5b3fedc9-7d42-4c16-a2a4-550cad98be00

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
section GlobalTheory
variable {K : Type} [CommRing K] {a s N : ℕ}
variable (hN : N = a + s) (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin a) (Fin s) K)
    (C C' : Matrix (Fin s) (Fin a) K) (D D' : Matrix (Fin s) (Fin s) K)
end GlobalTheory
section Phi
variable {K : Type} [CommRing K] (R : Subring K)
end Phi
section Simple
variable {K : Type} [CommRing K] {a s N : ℕ}
private lemma sUp_lemma {n : ℕ} (x : Matrix (Fin n) (Fin n) K) :
    sUp x = ∑ j : Fin n, ∑ i : Fin n, if (i : ℕ) = j + 1 then x j i else 0 := by
  unfold sUp
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j + 1, h⟩]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro e
      exact hi (Fin.ext e)
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro e
    have := i.2
    omega
end Simple
section Lists
variable {K : Type} [CommRing K]
end Lists
section Cls
variable {K : Type} [CommRing K] (R : Subring K) {ι κ μ : Type}
end Cls
section Grp
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
end Grp
section PhiInv
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
end PhiInv
section Pert
variable {K : Type} [CommRing K] (R : Subring K)
end Pert
section Sum
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
end Sum
section Fin
variable {K : Type} [CommRing K] (R : Subring K)
end Fin
end Formalism.FourierDecayAlt.P.TwoBlockPoint
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] {a s N : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (hN : N = a + s) (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin a) (Fin s) K)
    (C : Matrix (Fin s) (Fin a) K) (D : Matrix (Fin s) (Fin s) K) :
    sUp (blkM hN A B C D) = sUp A + sUp D + cornU B := by
  rw [sUp_lemma, sUp_lemma, sUp_lemma]
  simp only [← (eN hN).sum_comp, Fintype.sum_sum_type, eN_inl, eN_inr, blkM_ll, blkM_lr, blkM_rl,
    blkM_rr, Finset.sum_add_distrib]
  have hC : ∀ (j : Fin s) (i : Fin a), (if (i : ℕ) = a + j + 1 then C j i else 0) = 0 := by
    intro j i
    have := i.2
    rw [if_neg (by omega)]
  have hB : ∀ (j : Fin a) (i : Fin s),
      (if a + (i : ℕ) = j + 1 then B j i else 0) = (if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = a then B j i else 0) := by
    intro j i
    have := j.2
    simp only [show (a + (i : ℕ) = j + 1) ↔ ((i : ℕ) = 0 ∧ (j : ℕ) + 1 = a) by omega]
  have hD : ∀ (j i : Fin s),
      (if a + (i : ℕ) = a + j + 1 then D j i else 0) = (if (i : ℕ) = j + 1 then D j i else 0) := by
    intro j i
    simp only [show (a + (i : ℕ) = a + j + 1) ↔ ((i : ℕ) = j + 1) by omega]
  simp only [hB, hC, hD, Finset.sum_const_zero, add_zero, zero_add]
  unfold cornU
  abel
end Formalism.FourierDecayAlt.P.TwoBlockPoint
