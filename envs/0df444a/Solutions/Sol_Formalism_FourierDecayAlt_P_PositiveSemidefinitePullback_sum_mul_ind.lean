-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.sum_mul_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.098807+00:00
-- url     : https://prove2.me/submissions/a1b6d6a7-4660-4044-8753-631f82480fac

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback

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
theorem _root_.solution {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (g : α → ℂ) :
    ∑ q : Y, g q * ind Y A q = ∑ q ∈ A, g q := by
  have h := Finset.sum_coe_sort Y (fun q => g q * (if q ∈ A then (1 : ℂ) else 0))
  simp only [ind]
  rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
