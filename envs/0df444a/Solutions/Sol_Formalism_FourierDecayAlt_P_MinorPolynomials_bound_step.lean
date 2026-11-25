-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.bound_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:17:04.119015+00:00
-- url     : https://prove2.me/submissions/0d330532-9427-4880-813a-c3df21db03c0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_fo_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_dscal_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_qDbl_deg
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_qDl_deg
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_qGf_deg
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_degDP
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_cmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (e : CT k r nf × List (Mat k r)) :
    ∀ e' ∈ stepOne D X e, e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + 1 := by
  intro e' he'
  simp only [stepOne, dco, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he'
  rcases he' with ⟨t', ht', rfl⟩ | rfl
  · rcases ht' with ht' | ht'
    · have hes := dscal_es D X e.1 t' ht'
      refine ⟨?_, by simp [hes]⟩
      simp only [dscal, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at ht'
      rcases ht' with ((rfl | ⟨l, rfl⟩) | ⟨l, rfl⟩) | rfl
      · exact (PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (Nat.le_add_right _ _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qDbl_deg _ _ _)) _)
      · split_ifs
        · simp
        · exact (deg_cmul _ _ _).trans (Nat.add_le_add_left ((PI.UnitaryGroupMassFormula.UsCompose.degDP X _).trans (qGf_deg _ _)) _)
    · simp only [dfib, List.mem_ofFn] at ht'
      obtain ⟨i, rfl⟩ := ht'
      refine ⟨Nat.le_add_right _ _, ?_⟩
      simp only
      rw [fo_set]; omega
  · refine ⟨Nat.le_add_right _ _, by simp; omega⟩
end Formalism.FourierDecayAlt.P.MinorPolynomials
