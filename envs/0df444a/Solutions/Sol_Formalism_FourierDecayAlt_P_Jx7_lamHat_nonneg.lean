-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.lamHat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:45.151442+00:00
-- url     : https://prove2.me/submissions/2cc897b7-9857-4ca0-84f8-9eb7cd82e0eb

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_N_nonneg

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
theorem _root_.solution (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (x : ℝ)
    (hx : 0 ≤ x) : 0 ≤ Sz.lamHat b s C G.ka G.N G.lenI G.g x := by
  unfold Sz.lamHat
  have h2 := N_nonneg G
  positivity
end Formalism.FourierDecayAlt.P.Jx7
