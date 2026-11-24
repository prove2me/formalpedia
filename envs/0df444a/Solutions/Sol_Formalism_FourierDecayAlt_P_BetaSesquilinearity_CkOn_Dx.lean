-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:53:59.126717+00:00
-- url     : https://prove2.me/submissions/93808c3b-eb81-4bc7-a29d-0f65631539f7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dirL_apply

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
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {m : ℕ∞} {x : Bool × Mat k r} (hx : inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn (m + 1) UU f) : CkOn m UU (Dx x f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (dirL x h), hU, hgU, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hU (by push_cast; exact le_rfl)
    exact h1.clm_apply (dirL x).contDiff.contDiffOn
  · intro h hh hhG
    have hd : DifferentiableAt ℝ f' h :=
      (hc.differentiableOn (by push_cast; simp)).differentiableAt (hU.mem_nhds hh)
    show Dx x f h = fderiv ℝ f' h (dirL x h)
    rw [Dx_eq, dirL_apply]
    exact (Dx_hasDerivAt hx hU hh hhG hd hff).deriv
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
