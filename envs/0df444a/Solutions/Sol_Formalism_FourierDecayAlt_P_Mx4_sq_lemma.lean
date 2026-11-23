-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.sq_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:52.735465+00:00
-- url     : https://prove2.me/submissions/1bc3776b-2a12-4af5-b50f-3820ef40fd35

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (a b a' b' d : ℝ) (h1 : a * (d - 1) = b' * (d + 1)) (h2 : a' * (d + 1) = b * (d - 1))
    (hd : 2 ≤ d ∨ d ≤ -2) :
    Real.sqrt a * Real.sqrt b * (d - 1) = Real.sqrt a' * Real.sqrt b' * (d + 1) ∧
      Real.sqrt a' * Real.sqrt a = Real.sqrt b' * Real.sqrt b := by
  have hm : d - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
  obtain ⟨t, htd⟩ : ∃ t, t = (d + 1) / (d - 1) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htd]
    rcases hd with h | h
    · exact div_pos (by linarith) (by linarith)
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  have ht2 : t * (d - 1) = d + 1 := by rw [htd]; exact div_mul_cancel₀ _ hm
  have ea : a = b' * t := by rw [htd, ← mul_div_assoc, eq_div_iff hm]; exact h1
  have eb : b = a' * t := by rw [htd, ← mul_div_assoc, eq_div_iff hm]; exact h2.symm
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [ea, eb, Real.sqrt_mul' _ ht.le, Real.sqrt_mul' _ ht.le]
  constructor
  · linear_combination (Real.sqrt a' * Real.sqrt b' * (d - 1)) * hs + (Real.sqrt a' * Real.sqrt b') * ht2
  · ring
end Formalism.FourierDecayAlt.P.Mx4
