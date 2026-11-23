-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.memS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:54.164844+00:00
-- url     : https://prove2.me/submissions/993d256d-ebdd-4f5b-a9e1-a3ffc2d4193c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped nonZeroDivisors
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution (hX : XIsLamOne) (b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s) (hbs : b + s ≤ G.r + 2) :
    (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) ∈
      G.thrSet C de de' T T' l := by
  refine ⟨b, hb, by omega, ?_⟩
  rcases Nat.eq_or_lt_of_le hs with h1 | h1
  · subst h1
    rcases Nat.eq_or_lt_of_le hb with h2 | h2
    · subst h2
      left
      refine ⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]; simp [sp]
    · right; left
      refine ⟨h2, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]
      have : b ≠ 1 := by omega
      simp [sp, this]
  · right; right; left
    refine ⟨s, h1, by omega, Finset.prod_congr rfl fun w _ => ?_⟩
    have : s ≠ 1 := by omega
    simp [sp, this]
end Formalism.FourierDecayAlt.P.Jx7
