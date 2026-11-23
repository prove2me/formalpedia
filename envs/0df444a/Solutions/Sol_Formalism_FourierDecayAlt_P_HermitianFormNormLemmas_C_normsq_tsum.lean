-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C.normsq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.840631+00:00
-- url     : https://prove2.me/submissions/0b974de6-b7a8-43e7-bc97-f337996a09c1

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_C_summable_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
variable {ι V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
theorem _root_.solution (a : ι → V) (ha : Summable (fun i => ‖a i‖)) :
    ‖∑' i, a i‖ ^ 2 = ∑' p : ι × ι, (inner ℂ (a p.1) (a p.2) : ℂ).re := by
  have hS : HasSum a (∑' i, a i) := ha.of_norm.hasSum
  have hP : Summable (fun p : ι × ι => (inner ℂ (a p.1) (a p.2) : ℂ).re) :=
    Complex.reCLM.summable (summable_pairs a ha)
  have hfib : ∀ i, HasSum (fun j => (inner ℂ (a i) (a j) : ℂ).re)
      (inner ℂ (a i) (∑' j, a j) : ℂ).re := by
    intro i
    have h2 := Complex.reCLM.hasSum ((innerSL ℂ (a i)).hasSum hS)
    simpa using h2
  have hout : HasSum (fun i => (inner ℂ (a i) (∑' j, a j) : ℂ).re)
      (inner ℂ (∑' j, a j) (∑' j, a j) : ℂ).re := by
    have h2 : HasSum (fun i => (inner ℂ (∑' j, a j) (a i) : ℂ).re)
        (inner ℂ (∑' j, a j) (∑' j, a j) : ℂ).re := by
      simpa using Complex.reCLM.hasSum ((innerSL ℂ (∑' j, a j)).hasSum hS)
    have he : (fun i => (inner ℂ (a i) (∑' j, a j) : ℂ).re)
        = fun i => (inner ℂ (∑' j, a j) (a i) : ℂ).re := by
      funext i
      rw [← inner_conj_symm, Complex.conj_re]
    rw [he]
    exact h2
  have heq := hout.unique (hP.hasSum.prod_fiberwise hfib)
  rw [← heq]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.C
