-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.wlist_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:39.473252+00:00
-- url     : https://prove2.me/submissions/ad2bf055-dfb5-4434-84a1-aff77748eed4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_w1_commute_of_mem_Glev

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (i : Fin (r + 1)) (c : Fin r → ℂ) (L : List (Fin r)) (hL : ∀ a ∈ L, a.val < i.val)
    {g : Mx k r} (hg : g ∈ Glev k r i) :
    (L.map fun a => w1 k r a (c a)).prod * g = g * (L.map fun a => w1 k r a (c a)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a.succ ≤ i := by
      rw [Fin.le_def, Fin.val_succ]
      exact hL a List.mem_cons_self
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih fun b hb => hL b (List.mem_cons_of_mem _ hb),
      ← Matrix.mul_assoc, w1_commute_of_mem_Glev a (c a) (glev_mono ha hg), Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.Qx3
