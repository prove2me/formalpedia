-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_minorProd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:55.572902+00:00
-- url     : https://prove2.me/submissions/684ab5f5-024b-4b92-94d4-c5c4b6fc5dd8

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
theorem _root_.solution (K : Type) [CommRing K] (d N0 C : ℕ) (s : ZMod d) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (A : ∀ c, Fin (p c) → Fin N0) :
    minorProd (fun (i a : Fin N0) => (X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K)) p hp A =
      rename (satEmb d N0 s) (bideterminant K p hp A) := by
  unfold minorProd bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [satEmb, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  rfl
end Formalism.DworkPowerSeriesWeights
