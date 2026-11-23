-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:31.687478+00:00
-- url     : https://prove2.me/submissions/a70b2e54-c030-459b-85b4-fcbf8ef1871d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_apply
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



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) {v v' : Fin n → R}
    (h : (Submodule.Quotient.mk v : coker R Z) = Submodule.Quotient.mk v') :
    lamLin R Z v = lamLin R Z v' := by
  have h1 : v - v' ∈ latZ R Z := (Submodule.Quotient.eq _).1 h
  obtain ⟨y, hy⟩ := (Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).1 h1
  have h2 : lamLin R Z (v - v') = 0 := by
    rw [Formalism.DoubleCosetMeasures.P.lamLin_apply, ← hy, Matrix.mulVec_mulVec]
    by_cases hd : IsUnit Z.det
    · rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.lastCoord_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs
      · exact ⟨y j, (Formalism.DoubleCosetMeasures.P.coeLin_apply R y j).symm⟩
      · exact Submodule.zero_mem _
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]
      simp
  rw [map_sub, sub_eq_zero] at h2
  exact h2
end Formalism.FourierDecayAlt.P.A5x4
