-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.actMat_mul_lvlIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:53.860141+00:00
-- url     : https://prove2.me/submissions/78df3b41-decc-4249-a02a-af2c854a8544

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_eq_lift
import Theorems.Thm_Formalism_L2_DIV_group_action_matrix_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
private theorem single_mul_lvlIdem_lemma {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    (P : Subgroup G) (ψ : P →* Kˣ) (h : P) :
    MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, Finset.smul_sum]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  first
  | rw [MonoidAlgebra.smul_single']
  | rw [MonoidAlgebra.smul_single, smul_eq_mul]
  congr 1
  rw [mul_inv_rev, map_mul, Units.val_mul]
  have e : ((ψ h : Kˣ) : K) * ((ψ h⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  calc (Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K)
      = (Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K) * (((ψ h : Kˣ) : K) * ((ψ h⁻¹ : Kˣ) : K)) := by
        rw [e, mul_one]
    _ = _ := by ring
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
end Formalism.L2.DIV.Test
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Formalism.L2.DIV.CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) (k : P) :
    S.actMat r (k : G) * S.gaMat r (lvlIdem P ψ) = ((ψ k : Kˣ) : K) • S.gaMat r (lvlIdem P ψ) := by
  have e1 : S.actMat r (k : G) = S.gaMat r (MonoidAlgebra.single (k : G) 1) := by
    rw [S.gaMat_eq_lift r, MonoidAlgebra.lift_single, one_smul]
    rfl
  rw [e1, ← (group_action_matrix_hom K S G r).2, single_mul_lvlIdem_lemma, S.gaMat_eq_lift r, S.gaMat_eq_lift r,
    map_smul]
end Formalism.L2.DIV.CSD
