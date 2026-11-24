-- Prove2me | solution 1 for Formalism.L2.DIV.lvlDualLe_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.5698+00:00
-- url     : https://prove2.me/submissions/0558f641-4704-4623-bf9c-c7871e4e2feb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_mem_dual_iff
import Theorems.Thm_Formalism_L2_DIV_hform_smul
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_valLatF_isLattice
import Theorems.Thm_Formalism_DivisionValues_class_sum_dual_le_fixed
import Theorems.Thm_Formalism_DivisionValues_orthogonal_projection_exists
import Theorems.Thm_Formalism_DivisionValues_projection_integral
import Theorems.Thm_Formalism_DivisionValues_sectioned_dual_lattice
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
theorem _root_.solution (h1 : CutOrthProj) (h2 : LvlIdemSpec) (h3 : ActLat) : LvlDualLe := by
  intro K _ _ _ v0 hv0 S s hS hpos G _ _ r hr P ψ y hy
  obtain ⟨hg, -⟩ := h2 K v0 hv0 G P ψ
  obtain ⟨hp, he⟩ := h1 K v0 hv0 S hpos G r hr (lvlIdem P ψ) hg.idem hg.selfAdj
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0
    (by intro x y _; exact Subsingleton.elim _ _)
  have hA : Submodule.IsLattice K S.nabLat := ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat
  have hP : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hy' : ((Nat.card P : K)⁻¹ • y) ∈
      Formalism.HermitianLatticesTheory.dual (hform ((S.cutE r (lvlIdem P ψ))ᴴ * S.H * S.cutE r (lvlIdem P ψ)))
        (cutLat (S.cutE r (lvlIdem P ψ)) S.nabLat) := by
    rw [mem_dual_iff]
    intro z hz
    have := (mem_dual_iff _ _ _).1 hy z hz
    rwa [CSD.lvlH, hform_smul] at this
  rw [sectioned_dual_lattice K S.dim _ S.H hH hdet _ _ hp S.nabLat hA] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  have hz' : (s : 𝓞 K) • z ∈ S.delLat :=
    class_sum_dual_le_fixed K S.dim S.H S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_onto
      S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_stable z hz
  have h5 := projection_integral K S.dim G (S.actMat r) (fun t => (lvlIdem P ψ).coeff t) (Nat.card P)
    hg.integral S.delLat (fun t => (h3 K S G r hr t).2) _ hz'
  show (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) ∈ S.delLat
  have e : (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) =
      (Nat.card P : 𝓞 K) • (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t).mulVec ((s : 𝓞 K) • z) := by
    have e1 : (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t) = S.cutE r (lvlIdem P ψ) * S.cutPr r (lvlIdem P ψ) :=
      he.symm
    have e2 : y = (Nat.card P : K) • (S.cutPr r (lvlIdem P ψ)).mulVec z := by
      have : (S.cutPr r (lvlIdem P ψ)).mulVec z = (Nat.card P : K)⁻¹ • y := hzy
      rw [this, smul_smul, mul_inv_cancel₀ hP, one_smul]
    rw [e1, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [e2]
    simp only [← algebraMap_smul K ((s : 𝓞 K)), ← algebraMap_smul K ((Nat.card P : 𝓞 K)), map_natCast,
      Matrix.mulVec_smul]
    rw [smul_comm]
  rw [e]
  exact h5
end Formalism.L2.DIV
