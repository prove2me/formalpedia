-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.Wb_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:07.490048+00:00
-- url     : https://prove2.me/submissions/48426f1f-8d8e-4df2-81b2-4133a1fea3b2

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
theorem _root_.solution {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
