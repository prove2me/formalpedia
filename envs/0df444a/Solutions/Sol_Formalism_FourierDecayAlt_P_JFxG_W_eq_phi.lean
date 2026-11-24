-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.W_eq_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:39.344668+00:00
-- url     : https://prove2.me/submissions/f96e5b99-3937-4c41-9372-e62d74743e88

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_phi_contDiffAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_hasDerivAt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxG
theorem _root_.solution {F F' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U)
    (hff : ∀ x ∈ U, x ∈ GV k r → F x = F' x) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) →
      ∀ x ∈ U, x ∈ GV k r → W (List.ofFn fun i => (bs i, Xs i)) F x = Phi F' j bs (Xs, x) := by
  intro j
  induction j with
  | zero => intro bs Xs _ x hx hxG; exact hff x hx hxG
  | succ j ih =>
    intro bs Xs hXs x hx hxG
    rw [List.ofFn_succ, W_cons]
    have hd : DifferentiableAt ℝ (fun g => Phi F' j (fun i => bs i.succ) ((fun i => Xs i.succ), g)) x :=
      ((phi_contDiffAt F' hU hF j _ ((fun i => Xs i.succ), x) hx).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (hasDerivAt_ext (bs 0) hU hx hxG hd (fun h hh hhG => ih _ _ (fun i => hXs i.succ) h hh hhG)
      (hXs 0)).deriv
end Formalism.FourierDecayAlt.P.JFxG
