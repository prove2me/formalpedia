-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.dual_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:11.409655+00:00
-- url     : https://prove2.me/submissions/2155c203-b351-4744-8d7a-5ccc0e5357a4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_dual_map
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_map_isLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


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
theorem _root_.solution [IsDedekindDomain R] [IsFractionRing R K] [FiniteDimensional K V]
    [FiniteDimensional K W] (hV : V →ₗ⋆[K] V →ₗ[K] K) (hVs : hV.IsSymm) (hVn : hV.Nondegenerate)
    (hW : W →ₗ⋆[K] W →ₗ[K] K) (hWs : hW.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (E : W →ₗ[K] V) (P : V →ₗ[K] W) (adj : ∀ x z, hW (P x) z = hV x (E z))
    (hE : Function.Injective E) (hP : Function.Surjective P)
    (A : Submodule R V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual hW (A.comap (E.restrictScalars R)) =
      (Formalism.HermitianLatticesTheory.dual hV A).map (P.restrictScalars R) := by
  obtain ⟨hL, hdd, -⟩ := Formalism.HermitianLatticesTheory.dualLattice R K V hV hVs hVn hstar A hA
  have h1 := dual_map (R := R) hV hW E P adj (Formalism.HermitianLatticesTheory.dual hV A)
  rw [hdd] at h1
  have hsep : hW.SeparatingRight := by
    intro z hz
    apply hE
    rw [map_zero]
    apply hVn.2
    intro x
    rw [← adj]
    exact hz _
  have hWn : hW.Nondegenerate := by
    refine ⟨fun x hx => hsep x fun y => ?_, hsep⟩
    rw [← hWs.eq x y, hx y, map_zero]
  have hBP := map_isLattice (R := R) P hP _ hL
  rw [← h1]
  exact (Formalism.HermitianLatticesTheory.dualLattice R K W hW hWs hWn hstar _ hBP).2.1
end Formalism.DivisionValues.exponent_index_lattice
