-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.interval_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:37.126887+00:00
-- url     : https://prove2.me/submissions/a1fcd5da-af61-4e50-a005-e36a8ac20777

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_interval_one

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
theorem _root_.solution (hA : Formalism.FourierDecayAlt.E.AMarkov) (d : ℕ) (t₀ L : ℝ) (hL : 0 < L) (q : ℕ) :
    ∀ (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → (∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) →
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |(derivative^[q] P).eval t| ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M := by
  induction q with
  | zero => intro P M _ hP t ht; simpa using hP t ht
  | succ q ih =>
    intro P M hd hP t ht
    rw [Function.iterate_succ_apply]
    have h1 := interval_one hA P d t₀ L M hL hd hP
    have h2 := ih P.derivative ((2 * (d : ℝ) ^ 2 / L) * M)
      ((natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hd)) h1 t ht
    calc _ ≤ _ := h2
      _ = _ := by ring
end Formalism.FourierDecayAlt.P.Markov
