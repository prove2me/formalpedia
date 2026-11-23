-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.orb_of_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:21.53845+00:00
-- url     : https://prove2.me/submissions/8e8ec9f0-1dcc-4bbc-ba77-75fbdd5f58b0

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_pt_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mem_intSub
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x7
section Supp
variable {K : Type} [CommRing K] (R : Subring K)
end Supp
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Ones
variable {K : Type} [CommRing K] (R : Subring K)
private theorem isInt_mul_hermitian_curvature {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : IsInt R A)
    (hB : IsInt R B) : IsInt R (A * B) := by
  intro a b
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ (fun k _ => R.mul_mem (hA a k) (hB k b))
end Ones
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Padic
variable (p : ℕ) [hp : Fact p.Prime]
end Padic
end Formalism.FourierDecayAlt.P.A5x7
end

set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (w : Point K) (hw : InGLR R w) (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h1 : p.1 ∈ intSub R (lowW K w.1 w.2)) (h2 : p.2 ∈ intSub R (upUniG K w.1.sum)) :
    IsInt R (orbZ w p) ∧ IsInt R (orbZ w p)⁻¹ ∧ orbZ w p * (orbZ w p)⁻¹ = 1 := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hV, hV'⟩ := (mem_intSub R _ p.1).1 h1
  obtain ⟨hU, hU'⟩ := (mem_intSub R _ p.2).1 h2
  have hVV : ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
      (((p.1 : GL (Fin w.1.sum) K)⁻¹ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = 1 :=
    Units.mul_inv _
  have hUU : ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
      (((p.2 : GL (Fin w.1.sum) K)⁻¹ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = 1 :=
    Units.mul_inv _
  have hO : orbZ w p = ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
      pt w.1 w.2 * ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := rfl
  have hX : orbZ w p *
      ((((p.2 : GL (Fin w.1.sum) K)⁻¹ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
        P.Phase.ptI w.1 w.2 *
        (((p.1 : GL (Fin w.1.sum) K)⁻¹ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)) = 1 := by
    rw [hO]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K), hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (pt w.1 w.2), P.Phase.pt_mul_ptI, Matrix.one_mul, hVV]
  have hinv := Matrix.inv_eq_right_inv hX
  refine ⟨?_, ?_, ?_⟩
  · rw [hO]
    exact isInt_mul_hermitian_curvature R (isInt_mul_hermitian_curvature R hV hw1) hU
  · rw [hinv, ← pt_inv w]
    exact isInt_mul_hermitian_curvature R (isInt_mul_hermitian_curvature R hU' hw2) hV'
  · rw [hinv]
    exact hX
end Formalism.FourierDecayAlt.P.A5x7
