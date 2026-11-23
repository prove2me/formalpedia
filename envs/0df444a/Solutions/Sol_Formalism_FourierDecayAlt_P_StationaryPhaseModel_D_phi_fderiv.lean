-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:36.528655+00:00
-- url     : https://prove2.me/submissions/9b78e7b7-9b2f-476c-89a5-463201dc5be3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bilC_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_symm_dot
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : fderiv ℝ (D_phi d c H) = fun x => D_bilC d c H Γ hΓ hH x := by
  funext x
  have h1 := (((D_bilC d c H Γ hΓ hH).hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)).const_mul
    (1 / 2 : ℝ)
  rw [D_phi_eq d c H Γ hΓ hH]
  refine (HasFDerivAt.fderiv h1).trans ?_
  ext v
  simp only [_root_.smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply, id_eq, D_bilC_apply, smul_eq_mul]
  rw [D_symm_dot d H hs x v]
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
