-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.op_listSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:56.815684+00:00
-- url     : https://prove2.me/submissions/89330c20-69f3-4b68-9e5b-d05e919b6f63

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_cv


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution {b : Bool} {X : Mat k r} (hX : inLie k r X) :
    ∀ (L : List (ℝ × (Mat k r → E))), (∀ p ∈ L, CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.2) →
      ∀ g ∈ GV k r, op b X (fun g' => (L.map fun p => p.1 • p.2 g').sum) g =
        (L.map fun p => p.1 • op b X p.2 g).sum := by
  intro L hL g hg
  have key : ∀ L' : List (ℝ × (Mat k r → E)), (∀ p ∈ L', CkOn ((1 : ℕ) : ℕ∞) (GV k r) p.2) →
      HasDerivAt (fun t : ℝ => (L'.map fun p => p.1 • p.2 (cv b X t g)).sum)
        ((L'.map fun p => p.1 • op b X p.2 g).sum) 0 := by
    intro L'
    induction L' with
    | nil =>
      intro _
      simpa using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons p L' ih =>
      intro h
      have h1 := hasDerivAt_cv (h p (by simp)) hX hg b 0
      rw [cv_zero] at h1
      simp only [List.map_cons, List.sum_cons]
      exact (h1.const_smul p.1).add (ih fun q hq => h q (by simp [hq]))
  exact (key L hL).deriv
end Formalism.FourierDecayAlt.P.ListSumInequalities
