-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.near_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:53.849749+00:00
-- url     : https://prove2.me/submissions/76b335ad-e006-4426-96ad-a3b1d9807cd5

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

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
    {g : Mx k r} (hgD : g ∈ Dc c) : ∀ᶠ c' in 𝓝 c, c' ∈ OmX r ∧ g ∈ Dc c' := by
  have hmem : ((c, g) : XX k r) ∈ UU Dc := And.intro hc hgD
  have hcont : Continuous (fun c' : Fin r → ℂ => ((c', g) : XX k r)) := by fun_prop
  exact hcont.continuousAt.eventually_mem (ho.mem_nhds hmem)
end Formalism.FourierDecayAlt.P.Qx6
