-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.fam_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:07.481719+00:00
-- url     : https://prove2.me/submissions/7894737a-5054-41c5-a923-4b623c2f0635

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' L Dc Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r L) (hgD : g ∈ Dc c) : DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  obtain ⟨hs, -⟩ := h
  obtain ⟨U, F, hU, hxU, hF, hFe⟩ := hs (c, g) (And.intro hc hgD) hg
  have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => ((c', g) : (Fin r → ℂ) × Mx k r)) c := by fun_prop
  have h1 : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hd : DifferentiableAt ℝ (fun c' => F (c', g)) c := h1.comp c hpair
  refine hd.congr_of_eventuallyEq ?_
  have hcont : Continuous (fun c' : Fin r → ℂ => ((c', g) : (Fin r → ℂ) × Mx k r)) := by fun_prop
  have hev : ∀ᶠ c' in 𝓝 c, ((c', g) : (Fin r → ℂ) × Mx k r) ∈ U := hcont.continuousAt.eventually_mem (hU.mem_nhds hxU)
  exact hev.mono fun c' hc' => hFe (c', g) hc' hg
end Formalism.FourierDecayAlt.P.Qx6
