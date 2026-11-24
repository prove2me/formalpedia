-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.op_smulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:43.807082+00:00
-- url     : https://prove2.me/submissions/79f9c937-7423-4c31-91c0-dc47d7273344

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {f : Mat k r → ℂ} {H : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) (hg : g ∈ GV k r) :
    op b X (fun g => f g • H g) g = op b X f g • H g + f g • op b X H g := by
  have h1 := (ckOn_diff 0 b hf hX hg).hasDerivAt
  have h2 := (ckOn_diff 0 b hH hX hg).hasDerivAt
  have h3 := h1.smul h2
  simp only [cv_zero] at h3
  show deriv (fun t : ℝ => f (cv b X t g) • H (cv b X t g)) 0 = _
  rw [show (fun t : ℝ => f (cv b X t g) • H (cv b X t g)) =
    ((fun t => f (cv b X t g)) • fun t => H (cv b X t g)) from rfl, h3.deriv]
  exact add_comm _ _
end Formalism.FourierDecayAlt.P.ListSumSplittings
