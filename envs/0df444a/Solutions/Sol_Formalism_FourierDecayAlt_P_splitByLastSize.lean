-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.splitByLastSize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:15.8568+00:00
-- url     : https://prove2.me/submissions/9211c6fc-2a55-415d-ac86-0da8c57f4559

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_sqrt_form_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_form_ind
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_sum_ind_Xs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.SplitBySize := by
  intro E W _ D hG hK T ε hε i hi w
  have hM : PSDOn (T.X i) (fun p q => D.Kr i p q * D.gram ε i w p q) :=
    psd_mul (hK.1 i _) (hG ε hε i w _)
  have h := sqrt_form_sum_le _ hM (Icc 1 i) (fun s => ind (T.X i) (Xs T i s))
  have h2 : ∀ s, Xs T i s ⊆ T.X i := fun s => Finset.filter_subset _ _
  rw [sum_ind_Xs T hi, form_ind (T.X i) (T.X i) (Finset.Subset.refl _)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  simp only [fun s => form_ind (T.X i) (Xs T i s) (h2 s)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  exact h
end Formalism.FourierDecayAlt.P
