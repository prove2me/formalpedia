-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.om_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:10:32.529602+00:00
-- url     : https://prove2.me/submissions/4ea6dc66-6f80-461d-9098-dc9b17ae8470

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Sset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_omPlus_open
import Theorems.Thm_Formalism_QuantumDeterminants_dInv
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    IsStableOpen D (Om k r D.z D.z') := by
  refine ⟨⟨Q.OmPlus k r D.z D.z', PositiveOrbitOpen.omPlus_open D.z D.z', Set.inter_comm _ _⟩, ?_⟩
  intro s hs s' hs' g hg
  refine ⟨BetaSesquilinearity.gv_mul (BetaSesquilinearity.gv_mul (BetaSesquilinearity.Sset_sub hs) hg.1) (BetaSesquilinearity.Sset_sub hs'), fun l hl => ?_, ?_⟩
  · rw [dInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g l]; exact hg.2.1 l hl
  · show 0 < Gf k r D.z D.z' (s * g * s')
    rw [gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]; exact hg.2.2
end Formalism.FourierDecayAlt.P.JFxG
