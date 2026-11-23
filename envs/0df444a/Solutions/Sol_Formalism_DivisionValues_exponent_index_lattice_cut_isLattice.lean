-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.cut_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:03.651542+00:00
-- url     : https://prove2.me/submissions/354cd208-de90-4bd7-a1b4-09789df6cb9d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_cutLat
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mulVec_osmul

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
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective (Matrix.mulVecLin E)) (A : Submodule (𝓞 K) (Fin n → K))
    (hA : Submodule.IsLattice K A) : Submodule.IsLattice K (cutLat E A) := by
  refine ⟨?_, ?_⟩
  · have hN : IsNoetherian (𝓞 K) A := isNoetherian_of_fg_of_noetherian A hA.fg
    apply Submodule.fg_of_fg_map_injective ((Matrix.mulVecLin E).restrictScalars (𝓞 K)) hE
    exact isNoetherian_submodule.mp hN _ (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro z _
    have hv : E.mulVec z ∈ Submodule.span K (A : Set (Fin n → K)) := by
      rw [hA.span_eq_top]
      trivial
    rw [IsLocalization.mem_span_iff (M := nonZeroDivisors (𝓞 K))] at hv
    obtain ⟨y, hy, r, hr⟩ := hv
    rw [Submodule.span_eq] at hy
    have hmem : (r : 𝓞 K) • z ∈ cutLat E A := by
      rw [mem_cutLat, mulVec_osmul, hr, ← smul_assoc,
        Algebra.smul_def (r : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) r), IsLocalization.mk'_spec', map_one,
        one_smul]
      exact hy
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors r.2
    have hz : z = (algebraMap (𝓞 K) K r)⁻¹ • ((r : 𝓞 K) • z) := by
      rw [← algebraMap_smul K (r : 𝓞 K) z, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end Formalism.DivisionValues.exponent_index_lattice
