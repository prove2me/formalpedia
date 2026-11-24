-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.levi_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:08:01.214747+00:00
-- url     : https://prove2.me/submissions/fc4c0a2a-8e2e-4554-8b72-743a21b632f6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_eq_three_block_of_coordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end herm
private lemma ιLev_apply_tkF (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (tkF k r') q = if q.val = 0 then 1 else 0 := by
  have hq := q.isLt
  simp only [ιLev, tkF, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega
private lemma ιLev_apply_tkL (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (tkL k r') q = if q.val = 2 * (1 + r') + k then 1 else 0 := by
  have hq := q.isLt
  simp only [ιLev, tkL, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega
private lemma ιLev_levPos_apply (g : Mat k r') (i : Fin (2 * r' + k + 1)) (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) q =
      if h : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1 then g i ⟨q.val - 1, by omega⟩ else 0 := by
  have hi := i.isLt
  have hq := q.isLt
  have c1 : 1 ≤ i.val + 1 ∧ i.val + 1 < 2 * r' + k + 1 + 1 := by omega
  simp only [ιLev, levPos, Fin.val_mk, c1, and_self, ↓reduceDIte]
  by_cases hc : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hc, dif_pos hc]
    exact congrFun (congrArg g (Fin.ext (by simp only [Fin.val_mk]; omega))) _
  · rw [dif_neg hc, dif_neg hc]
private lemma ιLev_levPos_levPos (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  have hj := j.isLt
  have c : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
    simp only [levPos, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_pos c]
  exact congrArg (g i) (Fin.ext (by simp only [levPos, Fin.val_mk]; omega))
private lemma ιLev_levPos_tkF_eq_zero (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (tkF k r') = 0 := by
  have c : ¬ (1 ≤ (tkF k r').val ∧ (tkF k r').val < 2 * r' + k + 1 + 1) := by simp only [tkF, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_neg c]
private lemma ιLev_levPos_tkL_eq_zero (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (tkL k r') = 0 := by
  have c : ¬ (1 ≤ (tkL k r').val ∧ (tkL k r').val < 2 * r' + k + 1 + 1) := by simp only [tkL, Fin.val_mk]; omega
  rw [ιLev_levPos_apply, dif_neg c]
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
section
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 B2x8
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section dj
variable {k r : ℕ}
end dj
end Formalism.FourierDecayAlt.P.B2x8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x8
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (g₁ : Mat k r') (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g₁ *ᵥ mk3 k r' a y b = mk3 k r' a (g₁ *ᵥ y) b := by
  have hN0 : 2 * (1 + r') + k ≠ 0 := by omega
  have hN0' : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN : ∀ j : Fin (2 * r' + k + 1), j.val + 1 ≠ 2 * (1 + r') + k := fun j => by have := j.isLt; omega
  have hN' : ∀ j : Fin (2 * r' + k + 1), 2 * (1 + r') + k ≠ j.val + 1 := fun j => by have := j.isLt; omega
  have hL : ¬ (2 * (1 + r') + k < 2 * r' + k + 1 + 1) := by omega
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    simp only [ιLev_apply_tkF]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0]
  · intro j
    rw [tk_mulVec, ιLev_levPos_tkF_eq_zero, ιLev_levPos_tkL_eq_zero]
    simp only [ιLev_levPos_levPos, zero_mul, zero_add, add_zero]
    rfl
  · rw [tk_mulVec]
    simp only [ιLev_apply_tkL]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0', hN]
end Formalism.FourierDecayAlt.P.B2x8
