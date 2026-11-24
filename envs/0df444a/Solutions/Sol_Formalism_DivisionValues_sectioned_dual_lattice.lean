-- Prove2me | solution 1 for Formalism.DivisionValues.sectioned_dual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.474627+00:00
-- url     : https://prove2.me/submissions/8798a241-cd83-4ca4-9965-ce377fdd9448

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_dual_comap
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_hstar
import Theorems.Thm_P2M_Formalism_DivisionValues_exponent_index_lattice_herm_entry__3ab095fa8450
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_herm_cut
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_E_inj
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_Pr_surj
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_isSymm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_nondeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : CutDualLat := by
  intro K _ _ _ n d H hH hdet E Pr hO A hA
  have hs := hform_isSymm H (herm_entry' hH)
  exact dual_comap (hform H) hs (hform_nondeg H hs hdet.ne_zero) (hform (Eᴴ * H * E))
    (hform_isSymm _ (herm_entry' (herm_cut hH E))) hstar (Matrix.mulVecLin E) (Matrix.mulVecLin Pr)
    (adj hH hO) (E_inj hO) (Pr_surj hO) A hA
end Formalism.DivisionValues
