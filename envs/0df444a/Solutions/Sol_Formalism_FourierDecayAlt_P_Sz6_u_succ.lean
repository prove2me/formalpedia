-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.u_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:32.880596+00:00
-- url     : https://prove2.me/submissions/be337df1-1fbe-4fa4-8e31-b035c4bf5f6a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6
namespace Formalism.FourierDecayAlt.P.Sz6
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (hnt : ¬ (c.top = true ∧ i + 1 = c.k)) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
  have n1 : ¬ (i + 1 = 1) := by omega
  by_cases hk : i + 1 = c.k
  · have ht : ¬ (c.top = true) := fun ht => hnt ⟨ht, hk⟩
    have hik : i = c.k - 1 := by omega
    have hiR : (i : ℝ) = (c.k : ℝ) - 1 := by
      have : ((i + 1 : ℕ) : ℝ) = (c.k : ℝ) := by rw [hk]
      push_cast at this; linarith
    have hd : de i = 0 := by rw [hik]; exact hw.2
    simp only [Cfg.u, if_neg n1, if_pos hk, Cfg.ulast, if_neg ht, Cfg.v, hiR, hd]
    ring
  · simp only [Cfg.u, if_neg n1, if_neg hk, Nat.add_sub_cancel]
end Formalism.FourierDecayAlt.P.Sz6
