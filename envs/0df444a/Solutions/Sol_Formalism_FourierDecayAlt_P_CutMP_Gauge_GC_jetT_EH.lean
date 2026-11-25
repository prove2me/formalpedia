-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_EH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:17:34.961+00:00
-- url     : https://prove2.me/submissions/aef71c6c-8590-4fdd-a3ed-bedffd36de41

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_rd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hpart_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  have hl := Formalism.FourierDecayAlt.P.Qx2.hpart_lev (k := k) (r := r) (Fin.last r) a b
  exact jetT_add (jetT_rd hl.1 h) (jetT_smul Complex.I (jetT_rd hl.2 h))
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
