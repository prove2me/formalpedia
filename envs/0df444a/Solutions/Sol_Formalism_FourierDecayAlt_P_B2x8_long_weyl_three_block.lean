-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.long_weyl_three_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:02.034579+00:00
-- url     : https://prove2.me/submissions/77d65ec6-ecfd-4885-a9b5-204b4f5d1ff3

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
private lemma w0_tkF_apply_eq_ite_star_inv (c : ℂ) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (tkF k r') q = if q.val = 2 * (1 + r') + k then (star c)⁻¹ else 0 := by
  have hN0 : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN0' : 2 * (1 + r') + k ≠ 0 := by omega
  by_cases h : q.val = 2 * (1 + r') + k
  · simp [w0, tkF, h]
  · simp [w0, tkF, h, hN0, hN0']
private lemma w0_tkL_apply_eq_ite (c : ℂ) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (tkL k r') q = if q.val = 0 then c else 0 := by
  have hN0 : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN0' : 2 * (1 + r') + k ≠ 0 := by omega
  by_cases h : q.val = 0
  · simp [w0, tkL, h, hN0, hN0']
  · simp [w0, tkL, h, hN0, hN0']
private lemma w0_levPos_apply_eq_ite_succ (c : ℂ) (i : Fin (2 * r' + k + 1)) (q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c (levPos k 1 r' i) q = if q.val = i.val + 1 then 1 else 0 := by
  have hi := i.isLt
  have hlt : i.val + 1 < 2 * (1 + r') + k := by omega
  have hne : i.val + 1 ≠ 2 * (1 + r') + k := by omega
  have hv : (levPos k 1 r' i).val = i.val + 1 := rfl
  have hq' : (levPos k 1 r' i = q) ↔ (q.val = i.val + 1) :=
    ⟨fun e => by rw [← e]; rfl, fun e => Fin.ext (by rw [hv, e])⟩
  by_cases h : q.val = i.val + 1
  · simp [w0, hv, hq', h, hlt, hne]
  · simp [w0, hv, hq', h, hlt, hne]
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
theorem _root_.solution (c a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    w0 k r' c *ᵥ mk3 k r' a y b = mk3 k r' ((conj c)⁻¹ * b) y (c * a) := by
  have hN0 : 2 * (1 + r') + k ≠ 0 := by omega
  have hN0' : (0 : ℕ) ≠ 2 * (1 + r') + k := by omega
  have hN : ∀ j : Fin (2 * r' + k + 1), j.val + 1 ≠ 2 * (1 + r') + k := fun j => by have := j.isLt; omega
  have hN' : ∀ j : Fin (2 * r' + k + 1), 2 * (1 + r') + k ≠ j.val + 1 := fun j => by have := j.isLt; omega
  have hL : ¬ (2 * (1 + r') + k < 2 * r' + k + 1 + 1) := by omega
  apply eq_three_block_of_coordinates
  · rw [tk_mulVec]
    simp only [w0_tkF_apply_eq_ite_star_inv]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0', hN] <;> rfl
  · intro j
    rw [tk_mulVec]
    simp only [w0_levPos_apply_eq_ite_succ]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN', Fin.val_inj]
  · rw [tk_mulVec]
    simp only [w0_tkL_apply_eq_ite]
    simp only [tkF, tkL, levPos, Fin.val_mk]
    simp [hN0]
end Formalism.FourierDecayAlt.P.B2x8
