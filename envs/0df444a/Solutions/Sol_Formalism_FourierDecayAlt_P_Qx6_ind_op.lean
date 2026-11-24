-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.ind_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:17:43.33072+00:00
-- url     : https://prove2.me/submissions/406a5c2d-2d62-4fc9-954b-540fe5be1f82

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmX
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX


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
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {i : ℕ} (j : Fin r) (hj : j.val < i) (q : Fin 6) {Φ : Fn k r E} (h : Ind i Φ) :
    Ind i (crd (opL j q) Φ) := by
  intro c hc c' hc' hcc
  funext g
  refine opL_shift j q hc hc' (hcc j hj) ?_
  have hcont : Continuous (fun x : Fin r → ℂ => x + (c - c')) := by fun_prop
  have h1 : ∀ᶠ x in 𝓝 c', x + (c - c') ∈ OmX r :=
    hcont.continuousAt.preimage_mem_nhds ((Qx3.isOpen_OmX r).mem_nhds (by simpa using hc))
  filter_upwards [h1, (Qx3.isOpen_OmX r).mem_nhds hc'] with x hx1 hx2
  rw [h x hx2 _ hx1 (fun a ha => by simp [hcc a ha])]
end Formalism.FourierDecayAlt.P.Qx6
