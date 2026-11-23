-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.657015+00:00
-- url     : https://prove2.me/submissions/0f0bb6cc-6539-4ffe-b375-f5d126e80fb4

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
theorem _root_.solution (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) {ι : Type} (T : Finset ι)
    (κ : ι → Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => ∑ t ∈ T, κ t h h') = ∑ t ∈ T, D.N0 ε k w Y (κ t) := by
  simp only [Data.N0, Finset.sum_mul, ← Finset.sum_div, ← Complex.re_sum]
  congr 2
  calc _ = ∑ h ∈ Y, ∑ t ∈ T, ∑ h' ∈ Y, κ t h h' * D.gram ε k w h h' :=
        Finset.sum_congr rfl (fun h _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
