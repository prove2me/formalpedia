-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.nab_SSs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:59.215276+00:00
-- url     : https://prove2.me/submissions/f8ed5e57-5119-48fd-b281-d3f12a5dc421

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_sc_SSs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm


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
theorem _root_.solution (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    nabA P * star (SS P l) = star (SS P l) * nabA P + zbA P * ggiA P * star (SS P l) := by
  obtain ⟨_, hz, _, _, hGi, hnab⟩ := hSG P
  have h := congrArg star (hN P l hl).2
  have hns : star (nabsA P) = nabA P := by rw [← hnab, star_star]
  simp only [star_mul, star_sub] at h
  rw [hns, hz, hGi] at h
  have cg : Commute (ggiA P) (star (SS P l)) := sc_SSs hSc P l _
  have cz : Commute (zbA P) (star (SS P l)) := sc_SSs hSc P l _
  have cc : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have c1 : star (SS P l) * (ggiA P * zbA P) = zbA P * ggiA P * star (SS P l) := by
    rw [(cg.mul_left cz).eq.symm, cc.eq]
  rw [c1] at h
  rw [h]; abel
end Formalism.FourierDecayAlt.P.Mx7
