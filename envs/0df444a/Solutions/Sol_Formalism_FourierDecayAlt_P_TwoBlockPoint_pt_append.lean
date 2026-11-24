-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.pt_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:58.55911+00:00
-- url     : https://prove2.me/submissions/0f56be55-3037-484c-b3bb-1dd8cc850a18

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_revIn_append_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_revIn_append_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blk_append_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blk_append_ge
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
end Simple
section Lists
variable {K : Type} [CommRing K]
private lemma blk_lt_lemma : ∀ (l : List ℕ) (j : ℕ), j < l.sum → blk l j < l.length := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    simp only [blk, List.length_cons]
    by_cases h : j < x
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have := ih (j - x) (by omega)
      omega
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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (l l' : List ℕ) (T T₁ T₂ : ℕ → Kˣ) (h₁ : ∀ b, b < l.length → T b = T₁ b)
    (h₂ : ∀ b, b < l'.length → T (l.length + b) = T₂ b) (hN : (l ++ l').sum = l.sum + l'.sum) :
    pt (l ++ l') T = blkM hN (pt l T₁) 0 0 (pt l' T₂) := by
  ext x y
  obtain ⟨p, rfl⟩ := (eN hN).surjective x
  obtain ⟨q, rfl⟩ := (eN hN).surjective y
  rcases p with i | i <;> rcases q with j | j
  · rw [blkM_ll]
    simp only [pt, eN_inl]
    rw [revIn_append_lt l' l i i.2, blk_append_lt l' l i i.2, h₁ _ (blk_lt_lemma l i i.2)]
  · rw [blkM_lr]
    simp only [pt, eN_inl, eN_inr]
    rw [revIn_append_lt l' l i i.2]
    have := revIn_lt_lemma_2 l i i.2
    simp [show ¬ (l.sum + (j : ℕ) = revIn l i) by omega]
  · rw [blkM_rl]
    simp only [pt, eN_inl, eN_inr]
    rw [revIn_append_ge l' l i]
    have := j.2
    simp [show ¬ ((j : ℕ) = l.sum + revIn l' i) by omega]
  · rw [blkM_rr]
    simp only [pt, eN_inr]
    rw [revIn_append_ge l' l i, blk_append_ge l' l i, h₂ _ (blk_lt_lemma l' i i.2)]
    simp only [Nat.add_left_cancel_iff]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
