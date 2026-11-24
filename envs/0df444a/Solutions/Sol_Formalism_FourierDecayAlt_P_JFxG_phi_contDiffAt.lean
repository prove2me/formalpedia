-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxG.phi_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:22.351846+00:00
-- url     : https://prove2.me/submissions/6aab7a82-f510-48fb-941e-9f4b359e6866

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_vf_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_top_add_one_le

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
theorem _root_.solution (F' : Mat k r → E) {U : Set (Mat k r)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F' U) :
    ∀ (j : ℕ) (bs : Fin j → Bool) (q : (Fin j → Mat k r) × Mat k r), q.2 ∈ U → ContDiffAt ℝ ∞ (Phi F' j bs) q := by
  intro j
  induction j with
  | zero =>
    intro bs q hq
    exact (hF.contDiffAt (hU.mem_nhds hq)).comp q contDiffAt_snd
  | succ j ih =>
    intro bs q hq
    have hsh : ContDiff ℝ ∞ (fun p : ((Fin (j + 1) → Mat k r) × Mat k r) × Mat k r =>
        ((fun i : Fin j => p.1.1 i.succ), p.2)) :=
      (contDiff_pi.2 fun (i : Fin j) => (contDiff_apply ℝ (Mat k r) i.succ).comp (contDiff_fst.comp contDiff_fst)).prodMk
        contDiff_snd
    have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (p : (Fin (j + 1) → Mat k r) × Mat k r) (g : Mat k r) =>
        Phi F' j (fun i => bs i.succ) ((fun i => p.1 i.succ), g)) (q, q.2) :=
      (ih (fun i => bs i.succ) ((fun i => q.1 i.succ), q.2) hq).comp (q, q.2) hsh.contDiffAt
    have h2 := ContDiffAt.fderiv h1 contDiffAt_snd top_add_one_le
    have h3 : ContDiff ℝ ∞ (fun p : (Fin (j + 1) → Mat k r) × Mat k r => vf (bs 0) (p.1 0) p.2) :=
      vf_contDiff (bs 0) ((contDiff_apply ℝ (Mat k r) 0).comp contDiff_fst) contDiff_snd
    exact h2.clm_apply h3.contDiffAt
end Formalism.FourierDecayAlt.P.JFxG
