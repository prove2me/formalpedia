-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.iteratedDeriv_vec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:18.767833+00:00
-- url     : https://prove2.me/submissions/c9570a08-7740-4afc-a069-c96ecac0469e

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type}
    (S : Finset ι) (a : ι → H) (q : ℕ) : ∀ (P : ι → ℝ[X]),
    iteratedDeriv q (fun s : ℝ => ∑ k ∈ S, (P k).eval s • a k) =
      fun s : ℝ => ∑ k ∈ S, (derivative^[q] (P k)).eval s • a k := by
  induction q with
  | zero => intro P; simp
  | succ q ih =>
    intro P
    rw [iteratedDeriv_succ, ih P]
    funext s
    have : HasDerivAt (fun s : ℝ => ∑ k ∈ S, (derivative^[q] (P k)).eval s • a k)
        (∑ k ∈ S, (derivative (derivative^[q] (P k))).eval s • a k) s := by
      apply HasDerivAt.fun_sum
      intro k _
      exact ((derivative^[q] (P k)).hasDerivAt s).smul_const (a k)
    rw [this.deriv]
    simp only [Function.iterate_succ_apply']
end Formalism.FourierDecayAlt.P.Markov
