-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.supI_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:01.278687+00:00
-- url     : https://prove2.me/submissions/30565731-dc2a-43f3-9f29-ca45c8202564

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
theorem _root_.solution (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.supI de de' T T' l w := by
  unfold Sz.Glob.supI
  apply Real.sSup_nonneg
  rintro x ⟨Y, -, rfl⟩
  show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y
  unfold Sz.Cfg.be Sz.Cfg.core
  positivity
end Formalism.FourierDecayAlt.P.Jx7
