-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.pow_apply_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:49.028237+00:00
-- url     : https://prove2.me/submissions/c182b7d8-7508-4647-a238-c73e1a38070b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {S M : Type} [Field S] [AddCommGroup M] [Module S M]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
theorem _root_.solution (f : Module.End S M) (μ : S) (x : M) (hx : f x = μ • x) (k : ℕ) :
    (f ^ k) x = μ ^ k • x := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    show f ((f ^ n) x) = _
    rw [ih, map_smul, hx, smul_smul, ← pow_succ]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
