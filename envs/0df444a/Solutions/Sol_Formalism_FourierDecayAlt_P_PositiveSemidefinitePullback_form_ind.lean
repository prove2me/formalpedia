-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.form_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:49.516557+00:00
-- url     : https://prove2.me/submissions/9d87ea18-5392-4481-b455-9240e81b663a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_sum_mul_ind
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_star_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (k : α → α → ℂ) :
    ((Matrix.of fun x y : Y => k x y) *ᵥ ind Y A) ⬝ᵥ star (ind Y A) = ∑ p ∈ A, ∑ q ∈ A, k p q := by
  rw [star_ind]
  simp only [dotProduct, mulVec, of_apply]
  have h1 : ∀ p : Y, ∑ q : Y, k p q * ind Y A q = ∑ q ∈ A, k p q :=
    fun p => sum_mul_ind Y A hA (fun q => k p q)
  simp only [h1]
  exact sum_mul_ind Y A hA (fun p => ∑ q ∈ A, k p q)
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
