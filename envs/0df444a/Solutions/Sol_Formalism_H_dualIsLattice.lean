-- Prove2me | solution 1 for Formalism.H.dualIsLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:53.862802+00:00
-- url     : https://prove2.me/submissions/4a4d7dfe-4537-4ef8-82bb-65a8eeb3ae44

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_dualLattice_dual_span_eq
import Theorems.Thm_Formalism_H_exists_basis_span_eq
import Theorems.Thm_Formalism_H_isLattice_of_eq_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
namespace Formalism.H
theorem _root_.solution : DualIsLattice V := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  refine isLattice_of_eq_span (LinearMap.BilinForm.dualBasis (innerₗ V)
    dualLattice_innerₗ_nondegenerate e) (dual Λ) ?_
  rw [← he, dualLattice_dual_span_eq e]
end Formalism.H
