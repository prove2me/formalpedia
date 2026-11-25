-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.l_hasDeriv_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:22.469348+00:00
-- url     : https://prove2.me/submissions/56c2798b-2bd5-4aa6-bec6-23fa10508d68

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_lev
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {f F : Mx k r → E} {U : Set (Mx k r)} (hU : IsOpen U) {g X : Mx k r}
    (hgU : g ∈ U) (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (hF : DifferentiableAt ℝ F g)
    (he : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  have hc := lcurve_hasDeriv X g
  have h1 := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (lcurve_zero X g).symm
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) =ᶠ[𝓝 0]
      (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) := by
    have hU' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * g ∈ U := by
      apply hc.continuousAt.preimage_mem_nhds
      have h0 := hU.mem_nhds hgU
      rw [← lcurve_zero X g] at h0
      exact h0
    filter_upwards [hU'] with t ht
    exact he _ ht (lcurve_lev hg hX t)
  exact h1.congr_of_eventuallyEq hev
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
