-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.int_of_orb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:00.631777+00:00
-- url     : https://prove2.me/submissions/eabb1c93-d588-4e77-a7e0-8a5f8406e5b5

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_det_sub_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_lu_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_pt_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mem_intSub
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_ptI_mul_pt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_pt_mul_ptI
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_uniGroup
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
private theorem isInt_inv_of_det_eq_one {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A)
    (hd : A.det = 1) : IsInt R A⁻¹ := by
  intro a b
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, Matrix.adjugate_apply]
  have hM : IsInt R (A.updateRow b (Pi.single a 1)) := by
    intro i j
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
    · exact hA i j
  simpa using det_sub_mem R hM id id
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
    (hZ : IsInt R (orbZ w p)) :
    p.1 ∈ intSub R (lowW K w.1 w.2) ∧ p.2 ∈ intSub R (upUniG K w.1.sum) := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨hv, hmat, hhl, he⟩ := p.1.2
  have hu : IsUpUni ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := p.2.2
  have hZ' : IsInt R (((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
      pt w.1 w.2 * ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)) := hZ
  have hHU : IsInt R (hmat * ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)) := by
    have e : hmat * ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
        (pt w.1 w.2)⁻¹ * (((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
          pt w.1 w.2 * ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)) := by
      rw [he, pt_inv w, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.Phase.ptI_mul_pt, Matrix.one_mul]
    rw [e]
    exact isInt_mul_hermitian_curvature R hw2 hZ'
  obtain ⟨hH, hU⟩ := lu_int R hhl hu hHU
  have hV : IsInt R ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
    have e : ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
        pt w.1 w.2 * hmat * (pt w.1 w.2)⁻¹ := by
      rw [← he, pt_inv w, Matrix.mul_assoc, P.Phase.pt_mul_ptI, Matrix.mul_one]
    rw [e]
    exact isInt_mul_hermitian_curvature R (isInt_mul_hermitian_curvature R hw1 hH) hw2
  have hdV := ((Formalism.DoubleCosetMeasures.P.uniGroup K _ ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)
    ((p.1 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)).2.2.1 hv).2
  have hdU := ((Formalism.DoubleCosetMeasures.P.uniGroup K _ ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)
    ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K)).2.2.2 hu).2
  refine ⟨(mem_intSub R _ p.1).2 ⟨hV, ?_⟩, (mem_intSub R _ p.2).2 ⟨hU, ?_⟩⟩
  · rw [Matrix.coe_units_inv]
    exact isInt_inv_of_det_eq_one R hV hdV
  · rw [Matrix.coe_units_inv]
    exact isInt_inv_of_det_eq_one R hU hdU
end Formalism.FourierDecayAlt.P.A5x7
