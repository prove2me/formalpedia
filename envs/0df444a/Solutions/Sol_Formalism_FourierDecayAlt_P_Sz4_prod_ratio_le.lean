-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.prod_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:38.917802+00:00
-- url     : https://prove2.me/submissions/679c3408-d502-44ba-a06d-0ba174a0b98b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (s : Finset ℕ) (f g : ℕ → ℝ) (ε : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (hf : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i ≤ (1 + ε) * g i) :
    ∏ i ∈ s, f i / g i ≤ Real.exp ((s.card : ℝ) * ε) := by
  calc ∏ i ∈ s, f i / g i ≤ ∏ _i ∈ s, Real.exp ε := by
        refine Finset.prod_le_prod (fun i hi => (div_pos (hf i hi) (hg i hi)).le) fun i hi => ?_
        rw [div_le_iff₀ (hg i hi)]
        refine (h i hi).trans (mul_le_mul_of_nonneg_right ?_ (hg i hi).le)
        rw [add_comm]; exact Real.add_one_le_exp ε
    _ = Real.exp ((s.card : ℝ) * ε) := by rw [Finset.prod_const, Real.exp_nat_mul]
end Formalism.FourierDecayAlt.P.Sz4
