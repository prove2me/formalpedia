-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.near_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:59:18.847327+00:00
-- url     : https://prove2.me/submissions/4228fdc7-daf6-4e5f-b1ed-9dc60c493ed2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable {L : Fin (r + 1)} {Dc Dc₀ : (Fin r → ℂ) → Set (Mx k r)}
variable {S : Set (Fin r → ℂ)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {Dc : (Fin r → ℂ) → Set (Mx k r)} (ho : IsOpen (UU Dc)) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hgD : g ∈ Dc c) (l : Fin r) :
    ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ OmX r ∧ g ∈ Dc (Function.update c l s) := by
  have hmem : ((c, g) : XX k r) ∈ UU Dc := And.intro hc hgD
  have hcont2 : Continuous (fun c' : Fin r → ℂ => ((c', g) : XX k r)) := by fun_prop
  have h1 : ∀ᶠ c' in 𝓝 c, c' ∈ OmX r ∧ g ∈ Dc c' := hcont2.continuousAt.eventually_mem (ho.mem_nhds hmem)
  have hcont : Continuous (fun s : ℂ => Function.update c l s) := by
    first
      | exact continuous_const.update l continuous_id
      | fun_prop
      | exact (continuous_update l).comp (continuous_const.prodMk continuous_id)
  have ht : Filter.Tendsto (fun s : ℂ => Function.update c l s) (𝓝 (c l)) (𝓝 c) := by
    simpa using hcont.tendsto (c l)
  exact ht.eventually h1
end Formalism.FourierDecayAlt.P.Qx6
