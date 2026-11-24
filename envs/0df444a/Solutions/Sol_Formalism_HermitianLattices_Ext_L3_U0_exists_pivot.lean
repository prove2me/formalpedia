-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:46.549875+00:00
-- url     : https://prove2.me/submissions/c4d42570-fc95-4c4d-bb51-79b1e1f3f37d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_mem_spanS
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_smul_mem_spanS
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mul_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_dv_of_not_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_trace_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_isUnitIn_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_add_dv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {n : ℕ}
    (x : Fin (n + 1) → V) (hx : ∀ i j, h (x i) (x j) ∈ S)
    (hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))) :
    ∃ i₀ : Fin (n + 1), ∃ r ∈ spanS S (x ∘ i₀.succAbove), IsUnitIn S (h (x i₀ + r) (x i₀ + r)) := by
  obtain ⟨i, j, hij⟩ := hnd
  by_cases h1 : IsUnitIn S (h (x i) (x i))
  · exact ⟨i, 0, Submodule.zero_mem _, by simpa using h1⟩
  by_cases h2 : IsUnitIn S (h (x j) (x j))
  · exact ⟨j, 0, Submodule.zero_mem _, by simpa using h2⟩
  have d1 := dv_of_not_unit hπ (hx i i) (hs.eq _ _) h1
  have d2 := dv_of_not_unit hπ (hx j j) (hs.eq _ _) h2
  have hne : j ≠ i := by
    rintro rfl
    exact hij d1
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  obtain ⟨s, hsS, hs1⟩ := exists_trace_mul hS hπ (hx i j) hij S.one_mem (star_one K)
  refine ⟨i, s • x j, smul_mem_spanS hsS (by rw [← hk]; exact mem_spanS (x ∘ i.succAbove) k), ?_⟩
  have hji : h (x j) (x i) = star (h (x i) (x j)) := (hs.eq _ _).symm
  have e : h (x i + s • x j) (x i + s • x j) =
      1 + (star s * s * h (x j) (x j) + h (x i) (x i)) := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hji,
      starRingEnd_apply, RingHom.id_apply]
    simp only [star_mul'] at hs1
    linear_combination hs1
  rw [e]
  exact unit_add_dv hπ isUnitIn_one
    ((d2.mul_left (S.mul_mem (hS.star_mem _ hsS) hsS)).add d1)
end Formalism.HermitianLattices.Ext.L3.U0
