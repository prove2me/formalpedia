-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.det_eight_at_good_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:37.260045+00:00
-- url     : https://prove2.me/submissions/308504ef-9dca-480f-860e-b79591ad06ec

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_det_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_monodromy_diagonal_inverse
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_ti_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_l_mul_t22_shift
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Mx7_modY1__87e636a5f50a
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_raising_lowering_commutator_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (hP : P.OK) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0)
    (h2 : ∀ π, xC P π (Y + 1 + 1) ≠ 0) : Det8 P Y := by
  obtain ⟨a21, a12, a11, _⟩ := hQN P hP Y h0
  obtain ⟨b21, b12, b11, _⟩ := hQN P hP (Y + 1) h1
  have a11' : t11 P Y = qC P Y • ti P (Y + 1) + t22 P Y * mA P Y * lA P Y := a11 h1
  have b11' : t11 P (Y + 1) = qC P (Y + 1) • ti P (Y + 1 + 1) + t22 P (Y + 1) * mA P (Y + 1) * lA P (Y + 1) := b11 h2
  have y3 := raising_lowering_commutator_alt hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv P hP (Y + 1)
    (by rw [add_sub_cancel_right]; exact h0) h1 h2
  rw [add_sub_cancel_right] at y3
  unfold Det8
  rw [a21, a12, a11', b21, b12, b11']
  exact det_abs _ _ _ _ _ _ _ _ _ _ _ (monodromy_diagonal_inverse hLF P Y h0).1 (monodromy_diagonal_inverse hLF P Y h0).2 (monodromy_diagonal_inverse hLF P (Y + 1) h1).1
    (monodromy_diagonal_inverse hLF P (Y + 1) h1).2 (ti_comm P _ _) (l_mul_t22_shift hSc hSh hR hLF hLN P Y h0 h1)
    (modY1' hSc hSh hR hLF hLNs P Y h0 h1) y3
end Formalism.FourierDecayAlt.P.Mx7
