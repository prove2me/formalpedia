-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.RZ_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:25.746706+00:00
-- url     : https://prove2.me/submissions/2f1424da-d4b1-411d-8748-ab28f9062d42

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_hpart1_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_hpart2_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_rd_conj

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) (F : Mx k r → E) :
    RZ (Hpk k r) (g⁻¹ * Z * g) F g = LZ (Hpk k r) Z F g := by
  simp only [RZ, LZ, hpart1_conj hg, hpart2_conj hg, rd_conj hg]
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
