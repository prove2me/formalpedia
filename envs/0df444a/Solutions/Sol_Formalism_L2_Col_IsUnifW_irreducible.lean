-- Prove2me | solution 1 for Formalism.L2.Col.IsUnifW.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:35.130811+00:00
-- url     : https://prove2.me/submissions/503476f5-7a02-4bd0-b0ad-2c2ec407780e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.L2.Col
namespace IsUnifW
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {ϖ : 𝓞 K} (h : IsUnifW w ϖ) :
    Irreducible (algebraMap (𝓞 K) (Ow w) ϖ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  have hm : IsLocalRing.maximalIdeal (Ow w) = Ideal.span {π} := hπ.maximalIdeal_eq
  have h1 : algebraMap (𝓞 K) (Ow w) ϖ ∈ IsLocalRing.maximalIdeal (Ow w) := by
    simpa using (algebraMap_mem_maximalIdeal_pow_iff w ϖ 1).2 (by simpa using h.1)
  have h2 : algebraMap (𝓞 K) (Ow w) ϖ ∉ IsLocalRing.maximalIdeal (Ow w) ^ 2 :=
    fun h' => h.2 ((algebraMap_mem_maximalIdeal_pow_iff w ϖ 2).1 h')
  have h0 : algebraMap (𝓞 K) (Ow w) ϖ ≠ 0 := fun h' => h2 (h' ▸ Ideal.zero_mem _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rcases n with _ | _ | n
  · exfalso
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 (hu ▸ u.isUnit)
  · rw [hu, zero_add, pow_one]
    exact (irreducible_units_mul u).2 hπ
  · exfalso
    apply h2
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu]
    exact ⟨u * π ^ n, by ring⟩
end IsUnifW
end Formalism.L2.Col
