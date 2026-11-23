-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationLatticeField.valLatF_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:03.251934+00:00
-- url     : https://prove2.me/submissions/9199f0a4-5340-431a-85c6-a0eb4474edcf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


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
open exponent_index_lattice ValuationLatticeField
open Formalism.DivisionValues.ValuationLatticeField
namespace Formalism.DivisionValues.ValuationLatticeField
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} {Cl V : Type} [Fintype Cl] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (I : (Fin n → K) →ₗ[K] (Cl → V))
    (hI : Function.Injective I) (N : Cl → Submodule (𝓞 K) V) (hN : ∀ c, Submodule.IsLattice K (N c)) :
    Submodule.IsLattice K (valLatF I N) := by
  classical
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (I.restrictScalars (𝓞 K)) hI
    exact (Submodule.fg_pi fun c => (hN c).fg).of_le (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro z _
    have hz : ∀ c, ∃ s ∈ nonZeroDivisors (𝓞 K), s • I z c ∈ N c := by
      intro c
      have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) (N c) (hN c).span_eq_top
      have : I z c ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) (N c) := by rw [htop]; trivial
      exact this
    choose s hs hsz using hz
    have hS : ∏ c, s c ∈ nonZeroDivisors (𝓞 K) := Submonoid.prod_mem _ fun c _ => hs c
    have hs0 : (algebraMap (𝓞 K) K (∏ c, s c)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hS
    have hmem : (∏ c, s c) • z ∈ valLatF I N := by
      rw [mem_valLatF]
      intro c
      have e : I ((∏ c, s c) • z) c = (∏ c' ∈ Finset.univ.erase c, s c') • (s c • I z c) := by
        rw [smul_smul, mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ c),
          LinearMap.map_smul_of_tower, Pi.smul_apply]
      rw [e]
      exact (N c).smul_mem _ (hsz c)
    have : z = (algebraMap (𝓞 K) K (∏ c, s c))⁻¹ • ((∏ c, s c) • z) := by
      rw [← algebraMap_smul K (∏ c, s c) z, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end Formalism.DivisionValues.ValuationLatticeField
