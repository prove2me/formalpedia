-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.positionsBefore_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:19.269597+00:00
-- url     : https://prove2.me/submissions/65b822ff-c8fc-4e8d-bfad-2822c867371e

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
namespace Formalism.FourierDecayAlt.P
namespace Sz6
theorem _root_.solution (H1 : PositionBefore) (H2 : ProdOneAddTwoDivLeSqrt) : PositionsBefore := by
  intro c de de' Y l h hw hw' hl hlk hY
  have hk4 : (4:ℝ) ≤ c.k := by exact_mod_cast h.hk
  have step1 : ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i ≤
      ∏ i ∈ Ico 1 l, (fun j : ℕ => (1 + 2 / (4 * (j : ℝ) - 1))) (l - i) := by
    apply prod_le_prod
    · intro i hi
      rw [mem_Ico] at hi
      have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by rintro ⟨_, h2⟩; omega
      simp only [Cfg.rho, if_neg hnt]; positivity
    · intro i hi
      rw [mem_Ico] at hi
      have := H1 c de de' Y l i h hw hw' hi.1 hi.2 hlk hY
      simp only [Nat.cast_sub hi.2.le]; exact this
  have step2 := Finset.prod_Ico_reflect (fun j : ℕ => (1 + 2 / (4 * (j : ℝ) - 1))) 1 (m := l) (n := l) (by omega)
  rw [step2] at step1
  have a1 : l + 1 - l = 1 := by omega
  have a2 : l + 1 - 1 = l := by omega
  rw [a1, a2] at step1
  refine step1.trans ?_
  obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 := ⟨l - 1, by omega⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
    have : (1:ℝ) ≤ Real.sqrt c.k := by rw [Real.one_le_sqrt]; linarith
    linarith
  · have e : Ico 1 (p + 1) = Icc 1 p := by ext x; simp only [mem_Ico, mem_Icc]; omega
    rw [e]
    refine (H2 p hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : p ≤ c.k)
end Sz6
end Formalism.FourierDecayAlt.P
