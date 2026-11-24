-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:44.225403+00:00
-- url     : https://prove2.me/submissions/78e8f2b3-539d-486c-8bc2-c09ec9af46d7

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellZetaMinors_dmin_sgs
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_sgs_eq
import Theorems.Thm_Formalism_QuantumDeterminants_gInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
omit [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {y : Mat k r} (hy : y ∈ Om k r D.z D.z') :
    sgs p y ∈ Om k r D.z D.z' := by
  refine ⟨sgs_GV D hp hy.1, fun l hl => ?_, ?_⟩
  · rw [BigCellZetaMinors.dmin_sgs D hp]; exact hy.2.1 l hl
  · obtain ⟨hs, hs'⟩ := sgs_S D hp
    show 0 < Gf k r D.z D.z' (sgs p y)
    rw [B5.sgs_eq, gInv k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' y]
    exact hy.2.2
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
