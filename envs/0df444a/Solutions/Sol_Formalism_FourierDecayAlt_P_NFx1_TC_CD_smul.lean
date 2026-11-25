-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.CD.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:34.545503+00:00
-- url     : https://prove2.me/submissions/9c70f627-64dc-4cb5-8d67-c77ba5017f67

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx1_TC_diff_of_pres
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_csmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
namespace CD
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (hT : CD k r i T) (s : ℂ) :
    CD k r i (fun f x => s • T f x) := by
  refine ⟨fun U₀ Φ h => Qx3.sf_csmul s (hT.pres U₀ Φ h), ?_, ?_⟩
  · intro D hD f f₂ h x hx
    show s • T f x = s • T f₂ x
    rw [hT.loc D hD f f₂ h x hx]
  · intro U₀ hU₀ Φ h x hx hg v
    have h1 := diff_of_pres hT.pres h hx hg
    show fderiv ℝ (fun c' => s • T (Φ c') x.2) x.1 v = s • T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
    rw [show (fun c' => s • T (Φ c') x.2) = s • (fun c' => T (Φ c') x.2) from rfl,
      (h1.hasFDerivAt.const_smul s).fderiv, _root_.smul_apply, hT.comm U₀ hU₀ Φ h x hx hg v]
end CD
end Formalism.FourierDecayAlt.P.NFx1.TC
