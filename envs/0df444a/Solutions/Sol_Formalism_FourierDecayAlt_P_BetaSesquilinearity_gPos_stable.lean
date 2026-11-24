-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.gPos_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:46.172709+00:00
-- url     : https://prove2.me/submissions/ed5ec240-0518-4c03-9333-40d8a35d4e80

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Sset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont
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
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : IsStableOpen D (GPos D) := by
  refine ⟨⟨{g | 0 < Gf k r D.z D.z' g}, isOpen_lt continuous_const (Gf_cont _ _), ?_⟩, ?_⟩
  · ext g; simp only [GPos, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  · intro s hs s' hs' g hg
    refine ⟨gv_mul (gv_mul (Sset_sub hs) hg.1) (Sset_sub hs'), ?_⟩
    rw [gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]
    exact hg.2
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
