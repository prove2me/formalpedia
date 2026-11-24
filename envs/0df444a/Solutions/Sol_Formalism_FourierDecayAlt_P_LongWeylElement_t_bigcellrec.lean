-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.t_bigcellrec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:45.228931+00:00
-- url     : https://prove2.me/submissions/b2357d21-bce7-4cfe-adce-f6b58a9afcb0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_weylMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res


section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
namespace Formalism.FourierDecayAlt.P.LongWeylElement
section PartL
end PartL
section PartW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
private lemma matrix_apply_congr_of_eq {n m : ℕ} (μ : Matrix (Fin n) (Fin m) ℂ) {a b c d : ℕ} {ha : a < n} {hb : b < m}
    {hc : c < n} {hd : d < m} (h1 : a = c) (h2 : b = d) : μ ⟨a, ha⟩ ⟨b, hb⟩ = μ ⟨c, hc⟩ ⟨d, hd⟩ := by
  subst h1
  subst h2
  rfl
end PartW
section PartU
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end PartU
section PartF
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
end PartF
section PartG
section General
variable {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']
end General
end PartG
section PartM
variable {k r r' : ℕ}
end PartM
section PartK
variable {k r r' : ℕ}
attribute [local instance] sfHeis
end PartK
section PartS
variable {k r r' : ℕ}
end PartS
end Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : BigCellRec := by
  intro k r' c μ
  ext i j
  rw [weylMatrix_mul_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [if_pos h0, lev_out_row _ (iL k r') j (Or.inr rfl)]
    simp only [bigCell, esI, iL, a0, Fin.ext_iff, Fin.val_mk, h0]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
  · by_cases hL : i.val = 2 * (1 + r') + k
    · rw [if_neg h0, if_pos hL, lev_out_row _ (iZ k r') j (Or.inl rfl)]
      simp only [bigCell, esI, iZ, a0, Fin.ext_iff, Fin.val_mk, hL]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
    · rw [if_neg h0, if_neg hL]
      have hmi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1 := by omega
      by_cases hmj : 1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1
      · rw [lev_mid _ i j hmi hmj]
        dsimp only [bigCell, esI, Fin.val_mk]
        by_cases hA : j.val < 1 + r'
        · have hA' : j.val - 1 < r' := by omega
          simp only [hA, hA', dite_true]
          simp only [Fin.ext_iff, Fin.val_mk]
          split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
        · have hA' : ¬ (j.val - 1 < r') := by omega
          by_cases hB : j.val ≤ 1 + r' + k
          · have hB' : j.val - 1 ≤ r' + k := by omega
            simp only [hA, hA', hB, hB', dite_true, dite_false]
            split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
          · have hB' : ¬ (j.val - 1 ≤ r' + k) := by omega
            simp only [hA, hA', hB, hB', dite_true, dite_false]
            split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
      · rw [lev_mn k r' _ i j hmi hmj]
        simp only [bigCell, esI, Fin.ext_iff, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
end Formalism.FourierDecayAlt.P.LongWeylElement
