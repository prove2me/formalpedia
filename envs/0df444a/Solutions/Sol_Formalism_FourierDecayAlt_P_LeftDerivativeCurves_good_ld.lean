-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.good_ld
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:21.430526+00:00
-- url     : https://prove2.me/submissions/260f7067-922b-4745-911c-d95ec10286cd

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_ld_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_ld_lin
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
theorem _root_.solution (hD : IsOpen D) {X : Mx k r} (hX : inLieLev k r i X) :
    Good k r i D (fun f : Mx k r → E => LdV X f) := by
  refine ⟨fun f hf => ld_smooth hf hX, fun f f₂ h x hx => ?_, fun f f₂ s hf hf₂ x hx => ld_lin hf hf₂ s hx hX⟩
  show deriv _ 0 = deriv _ 0
  apply Filter.EventuallyEq.deriv_eq
  have hc := (lcurve_hasDeriv X x).continuousAt
  have hD' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), NormedSpace.exp ((t : ℂ) • X) * x ∈ D := by
    apply hc.preimage_mem_nhds
    have h0 := hD.mem_nhds hx.2
    rw [← lcurve_zero X x] at h0
    exact h0
  filter_upwards [hD'] with t ht
  exact h _ ⟨lcurve_lev hx.1 hX t, ht⟩
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
