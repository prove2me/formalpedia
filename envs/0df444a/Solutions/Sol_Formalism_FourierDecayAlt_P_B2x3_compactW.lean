-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.compactW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:39.621993+00:00
-- url     : https://prove2.me/submissions/4b260dfe-2edc-4161-ba6b-3d7ac97e21e4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_linv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_col_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_EmT_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_herm_wb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : CompactW := by
  intro k r z hz hT
  set zb := (Em k r)ᵀ *ᵥ z with hzb
  have hT' : (star zb ⬝ᵥ (Hb k *ᵥ zb)).re < 0 := by
    rw [hzb, ← herm_wb z hz]
    unfold Tz at hT
    linarith
  obtain ⟨R, hR⟩ := col_bound zb hT'
  have hK0 : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) => Set.pi Set.univ fun _ : Fin (k + 1) =>
      Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK := hK0.image (emb_cont (k := k) (r := r))
  refine IsCompact.of_isClosed_subset hK (closedW k r z).closed ?_
  intro g hg
  obtain ⟨a, ha, hag⟩ := (uwb_iff g).mp ⟨hg.1, hg.2.1⟩
  have hfix : a *ᵥ zb = zb := by
    have e : a = (Em k r)ᵀ * g * Em k r := by rw [← hag, emb_linv]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzb, Em_EmT_mulVec z hz, hg.2.2]
  refine ⟨a, ?_, hag⟩
  intro i _ j _
  rw [mem_closedBall_zero_iff]
  exact hR a ha hfix i j
end Formalism.FourierDecayAlt.P.B2x3
