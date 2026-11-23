-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:52.641223+00:00
-- url     : https://prove2.me/submissions/345e39f6-4487-42bc-9b62-e0f5df314c07

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
theorem _root_.solution (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (κ κ' : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => κ' h h' - κ h h') = D.N0 ε k w Y κ' - D.N0 ε k w Y κ := by
  simp only [Data.N0, sub_mul, Finset.sum_sub_distrib, Complex.sub_re, sub_div]
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
