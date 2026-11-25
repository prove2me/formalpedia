-- Prove2me | solution 1 for Formalism.H.dualDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:42.560831+00:00
-- url     : https://prove2.me/submissions/818bf9ed-f082-491a-8ace-aeb12a33f207

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
import Theorems.Thm_P2M_Formalism_H_inner__isSymm_d7d5f164fe07


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
theorem _root_.solution : DualDual V := by
  intro Λ _ _
  obtain ⟨ι, _, _, e, he⟩ := exists_basis_span_eq Λ
  rw [← he, dualLattice_dual_span_eq e, dualLattice_dual_span_eq,
    LinearMap.BilinForm.dualBasis_dualBasis _ innerₗ_isSymm]
end Formalism.H
