-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.dual_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:18.683899+00:00
-- url     : https://prove2.me/submissions/6d0b899e-0672-4cf3-beca-0922c9151b6d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

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
open Formalism.DivisionValues.exponent_index_lattice
variable {R K V W : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution (hV : V →ₗ⋆[K] V →ₗ[K] K) (hW : W →ₗ⋆[K] W →ₗ[K] K) (E : W →ₗ[K] V)
    (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z)) (A : Submodule R V) :
    Formalism.HermitianLatticesTheory.dual hW (A.map (P.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).comap (E.restrictScalars R) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map,
    LinearMap.coe_restrictScalars, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, adj]
end Formalism.DivisionValues.exponent_index_lattice
