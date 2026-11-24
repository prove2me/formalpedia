-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.hom_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:53.888803+00:00
-- url     : https://prove2.me/submissions/fa87cb0d-d488-4fcb-bfc3-fabe7cf8804a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_hom_intCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution {σ R : Type*} [CommRing R] {n : ℕ} (w : σ → ℕ) (up : Bool)
    (Kf : Form (MvPolynomial σ R) n) (Xv : Fin n → MvPolynomial σ R) (d e : ℕ)
    (hK : ∀ J, IsWeightedHomogeneous w (Kf J) d) (hX : ∀ m, IsWeightedHomogeneous w (Xv m) e)
    (J : Finset (Fin n)) : IsWeightedHomogeneous w (stepF up Kf Xv J) (d + e) := by
  unfold stepF
  split
  · unfold wedgeF
    refine IsWeightedHomogeneous.sum _ _ _ fun m _ => ?_
    have := ((hom_intCast (R := R) w (sg J m)).mul (hK (J.erase m))).mul (hX m)
    rwa [zero_add] at this
  · unfold contrF
    refine IsWeightedHomogeneous.sum _ _ _ fun m _ => ?_
    have := ((hom_intCast (R := R) w (sg J m)).mul (hX m)).mul (hK (insert m J))
    rwa [zero_add, add_comm] at this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
