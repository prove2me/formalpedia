-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:59.358844+00:00
-- url     : https://prove2.me/submissions/3a741b0e-0266-4d0f-9ddd-b9df1e97427b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) : (lu_M u).det = 1 := by
  classical
  have hT : (lu_M u).BlockTriangular (fun p : Pr n => p.1.1) := by
    intro p p' h
    have h' : p'.1.1 < p.1.1 := h
    simp only [lu_M]
    split_ifs
    · exact hu.1 h'
    · rfl
  rw [hT.det_fintype]
  refine Finset.prod_eq_one fun k _ => ?_
  have : (lu_M u).toSquareBlock (fun p : Pr n => p.1.1) k = 1 := by
    ext ⟨p, hp⟩ ⟨p', hp'⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, lu_M]
    have hp1 : p.1.1 = k := hp
    have hp2 : p'.1.1 = k := hp'
    by_cases h : p = p'
    · subst h
      simp [hu.2]
    · rw [Matrix.one_apply_ne (by simpa [Subtype.ext_iff] using h), if_neg]
      intro h2
      apply h
      apply Subtype.ext
      apply Prod.ext
      · rw [hp1, hp2]
      · exact h2.symm
  rw [this, Matrix.det_one]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
