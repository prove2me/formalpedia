-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.786465+00:00
-- url     : https://prove2.me/submissions/28479af7-e723-45f7-9cc9-e3791ca53a5f

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
theorem _root_.solution (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (r : ℝ) (κ : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => (r : ℂ) * κ h h') = r * D.N0 ε k w Y κ := by
  simp only [Data.N0, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul, mul_div_assoc]
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
