-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:14:18.709893+00:00
-- url     : https://prove2.me/submissions/332bfb3f-e4e3-4dff-bf8e-b82c025308c5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx

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
theorem _root_.solution {m : ℕ∞} {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {UU : Set (Mat k r)}
    {f : Mat k r → E} (hf : CkOn (m + w.length) UU f) : CkOn m UU (Dw w f) := by
  induction w generalizing m with
  | nil =>
    show CkOn m UU f
    simpa using hf
  | cons x w ih =>
    have h1 : CkOn (m + 1 + w.length) UU f := by
      have e : m + 1 + (w.length : ℕ∞) = m + ((x :: w).length : ℕ∞) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
      rw [e]; exact hf
    exact CkOn_Dx (hw x (by simp)) (ih (fun y hy => hw y (by simp [hy])) h1)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
