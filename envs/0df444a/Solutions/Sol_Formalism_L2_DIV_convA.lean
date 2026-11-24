-- Prove2me | solution 1 for Formalism.L2.DIV.convA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.304713+00:00
-- url     : https://prove2.me/submissions/62fa0154-d6b3-4284-9837-cc1d6d8b84bd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
import Theorems.Thm_Formalism_L2_DIV_schur_scalar

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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Representation
namespace Formalism.L2.DIV
theorem _root_.solution {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (φ : G → k)
    (hφ : ∀ g s, φ (g * s * g⁻¹) = φ s) (u : G) :
    (∑ s, φ s * ρ.character (s * u)) * (finrank k V : k) = (∑ s, φ s * ρ.character s) * ρ.character u := by
  set T : V →ₗ[k] V := ∑ s, φ s • ρ s with hTdef
  have hT : ∀ g v, T (ρ g v) = ρ g (T v) := by
    intro g v
    simp only [hTdef, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [← Equiv.sum_comp (MulAut.conj g).toEquiv]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : φ ((MulAut.conj g).toEquiv s) = φ s := by simpa [MulAut.conj_apply] using hφ g s
    rw [e1]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [MulAut.conj_apply]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ s, φ s * ρ.character (s * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace k V (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [character, Module.End.mul_eq_comp]
    rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, character, map_mul]
  have h2 := h1 1
  simp only [mul_one, char_one] at h2
  rw [h1 u, h2]
  ring
end Formalism.L2.DIV
