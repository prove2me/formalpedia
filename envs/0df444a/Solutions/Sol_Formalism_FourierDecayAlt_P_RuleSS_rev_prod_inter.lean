-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.rev_prod_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:19.975232+00:00
-- url     : https://prove2.me/submissions/7c13cec0-6150-4cd6-8df4-920cba4b68a9

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {M : Type} [Monoid M] (d : M) :
    ∀ (n : ℕ) (f g : Fin n → M), (∀ i, f i * d = d * g i) →
      (List.ofFn f).reverse.prod * d = d * (List.ofFn g).reverse.prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
      rw [List.ofFn_succ, List.ofFn_succ, List.reverse_cons, List.reverse_cons, List.prod_append,
        List.prod_append, List.prod_singleton, List.prod_singleton, mul_assoc, h 0, ← mul_assoc,
        solution d n (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ), mul_assoc]
end Formalism.FourierDecayAlt.P.RuleSS
