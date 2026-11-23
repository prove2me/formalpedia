-- Prove2me | solution 1 for Formalism.L2.DIV.single_mul_lvlIdem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:53.416852+00:00
-- url     : https://prove2.me/submissions/db7174a5-9880-471f-b374-4a2784474886

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) (h : P) :
    MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ := by
  exact CSD.single_mul_lvlIdem_lemma P ψ h
end Formalism.L2.DIV
