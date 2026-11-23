-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_bidet_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:54.424783+00:00
-- url     : https://prove2.me/submissions/94ebcfb2-862c-437a-bf13-7463c44a6031

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (R : Type) [CommRing R] {r n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n)
    (I : ∀ i, Fin (sz i) → Fin r) : bideterminant R sz hsz I = ∏ i, satMinor R r n ⟨sz i, I i⟩ := by
  unfold bideterminant
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [satMinor, hsz i]
end Formalism.DworkPowerSeriesWeights
