-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.MW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:40.032802+00:00
-- url     : https://prove2.me/submissions/7b75241f-5b3c-4767-8c24-4a7e554a3776

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace LW
theorem _root_.solution (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (i j : Fin m) :
    LW R c (fun v : Fin m → K => MW (InverseBoundedFixedPoint.wv c v) i j) := by
  have hu : ∀ i j : Fin m, LW R c (fun v : Fin m → K => uW (InverseBoundedFixedPoint.wv c v) i j) := fun i j =>
    ((LW.wv hc i).mul (LW.wv hc j)).mul (LW.prod _ fun k => LW.wv hc k)
  have h2 : (2 : K) ∈ R := ofNat_mem R 2
  exact ((LW.ite _ ((LW.const h2).mul (LW.wv hc i))).add (LW.ite _ (hu i j))).add (LW.ite _ (hu j i))
end LW
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
