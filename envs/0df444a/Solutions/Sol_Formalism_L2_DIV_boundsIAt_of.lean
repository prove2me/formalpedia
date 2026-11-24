-- Prove2me | solution 1 for Formalism.L2.DIV.boundsIAt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:55.325795+00:00
-- url     : https://prove2.me/submissions/b7fa83ff-e6b5-49b1-b117-43e20bd0612b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_dual_iff
import Theorems.Thm_Formalism_L2_DIV_hform_smul
import Theorems.Thm_Formalism_DivisionValues_bounds_class_field_fixed
import Theorems.Thm_Formalism_DivisionValues_orthogonal_projection_exists
import Theorems.Thm_Formalism_L2_DIV_CSD_I_injective
import Theorems.Thm_Formalism_L2_DIV_CSD_I_onto
import Theorems.Thm_Formalism_L2_DIV_CSD_isClassSum


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
namespace Formalism.L2.DIV
theorem _root_.solution (h : BoundsIHyps) : BoundsIAt := by
  intro K _ _ _ v0 hv0 S s hS hpos G _ _ r hr X hX P ψ
  obtain ⟨hp, he, hint, hdel⟩ := h K v0 hv0 S hpos G r hr X hX P ψ
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0
    (by intro x y _; exact Subsingleton.elim _ _)
  obtain ⟨hl1, hl2, hl3⟩ := bounds_class_field_fixed K S.dim (S.BaseDimension r X P ψ) S.H hH hdet (S.V0E r X P ψ)
    (S.goodPartProjection r X P ψ) hp S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_injective S.I_onto
    S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_le hS.del_stable G (S.actMat r)
    (fun t => (goodAt X P ψ).coeff t) (Fintype.card G * Nat.card P) he hint hdel
  refine ⟨hl1, hl2, ?_⟩
  intro x hx
  have hP : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hx' : ((Nat.card P : K)⁻¹ • x) ∈
      Formalism.HermitianLatticesTheory.dual (hform ((S.V0E r X P ψ)ᴴ * S.H * S.V0E r X P ψ)) (cutLat (S.V0E r X P ψ) (valLatF S.I S.Nab)) := by
    rw [mem_dual_iff]
    intro y hy
    have := (mem_dual_iff _ _ _).1 hx y hy
    rwa [CSD.goodPartHermitianForm, hform_smul] at this
  have h4 := hl3 _ hx'
  have e : ((Fintype.card G * Nat.card P * s : ℕ) : 𝓞 K) • ((Nat.card P : K)⁻¹ • x) =
      ((Fintype.card G * s : ℕ) : 𝓞 K) • x := by
    rw [← algebraMap_smul K, ← algebraMap_smul K (((Fintype.card G * s : ℕ) : 𝓞 K)), smul_smul]
    congr 1
    simp only [map_natCast, map_mul, Nat.cast_mul]
    field_simp
  rw [e] at h4
  exact h4
end Formalism.L2.DIV
