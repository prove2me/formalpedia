-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.cVv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:37.790573+00:00
-- url     : https://prove2.me/submissions/1e89ffe7-f6be-485e-b6d8-cf4237f315a0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sdata_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_good_QL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_rc_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hCA : ChainAll) (hR : ResMem) (hRG : ResGFam) (hFO : FamOps) (hTP : TPreservesFF)
    (hLL : TLinLoc) : CVv := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y hz hz' hD J hJ c hc g hg hgD
  have hS := sdata_self hR hz hz' hD i
  have h1 := hCA Wp Wq k r z z' π π' i D Y 0 0 hz hz' hD J hJ c hc g hg hgD
  have hop : ∀ l q, (famData π π' hS).Good (crd (opL l q)) := fun l q => good_op hFO hz hz' hS l q
  have hM : ∀ a b, (famData π π' hS).Good (QL k r z z' i Y a b) := fun a b => good_QL hTP hLL hz hz' hS Y a b
  have hΦ : resG k r i J ∈ (famData π π' hS).G := hRG Wp Wq k r z z' π π' D hz hz' hD J hJ i
  have h2 := rc_eq hop Y i.val (QL k r z z' i Y) hM hΦ
  have h3 := (cutP_eq_iff _ _).1 h2 c hc g hg hgD
  simp only [Fin.sum_univ_two] at h3 ⊢
  exact h1.trans h3
end Formalism.FourierDecayAlt.P.Qx6
