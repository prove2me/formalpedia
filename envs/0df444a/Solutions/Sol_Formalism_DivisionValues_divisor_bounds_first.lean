-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_bounds_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.834486+00:00
-- url     : https://prove2.me/submissions/370f333e-73db-4fb8-b54f-7ae9a6b9eb4f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_E_inj
import Theorems.Thm_Formalism_DivisionValues_sectioned_dual_lattice
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_cutLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_matLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mulVec_osmul
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_cut_isLattice

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
theorem _root_.solution : BoundsI := by
  intro K _ _ _ n' n H' hH hdet E Pr hO A B hA s hs G hG
  refine ⟨cut_isLattice E (E_inj hO) A hA, ?_⟩
  intro x hx
  rw [sectioned_dual_lattice K n' n H' hH hdet E Pr hO A hA] at hx
  obtain ⟨y, hy, rfl⟩ := (mem_matLat Pr _ x).mp hx
  rw [mem_cutLat]
  have h1 := hG _ (hs y hy)
  convert h1 using 1
  rw [mulVec_osmul, mulVec_osmul, Matrix.mulVec_mulVec, Nat.cast_mul, smul_smul]
end Formalism.DivisionValues
