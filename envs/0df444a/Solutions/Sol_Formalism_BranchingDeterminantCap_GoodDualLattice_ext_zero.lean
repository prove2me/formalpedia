-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.GoodDualLattice.ext_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:24.491996+00:00
-- url     : https://prove2.me/submissions/43856987-6a96-429a-8fa3-670663d802c8

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Theorems.Thm_Formalism_BranchingDeterminantCap_GoodDualLattice_denom

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
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.GoodDualLattice
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
omit [IsDedekindDomain R] [StarRing K]
namespace Formalism.BranchingDeterminantCap.GoodDualLattice
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι K V) (A : Submodule R V) (hb : ∀ i, b i ∈ A)
    (D : A →ₗ[R] K) (hD : ∀ i, D ⟨b i, hb i⟩ = 0) (a : A) : D a = 0 := by
  obtain ⟨d, n, hd, hdn⟩ := denom (R := R) b (a : V)
  have h1 : d • a = ∑ i, n i • (⟨b i, hb i⟩ : A) := by
    apply Subtype.ext
    simp [hdn]
  have h2 : d • D a = 0 := by
    rw [← map_smul, h1, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hD, smul_zero]
  have hd' : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  rw [Algebra.smul_def] at h2
  exact (mul_eq_zero.mp h2).resolve_left hd'
end Formalism.BranchingDeterminantCap.GoodDualLattice
