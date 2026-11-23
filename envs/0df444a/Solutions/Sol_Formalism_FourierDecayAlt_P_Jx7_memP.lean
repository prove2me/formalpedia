-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.memP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:45.289119+00:00
-- url     : https://prove2.me/submissions/689ec9ae-187e-4f18-b975-239824395aef

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
theorem _root_.solution (b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ G.r + 1) :
    (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) ∈
      G.thrSet C de de' T T' l :=
  ⟨b, hb, hbs, Or.inr (Or.inr (Or.inr rfl))⟩
end Formalism.FourierDecayAlt.P.Jx7
