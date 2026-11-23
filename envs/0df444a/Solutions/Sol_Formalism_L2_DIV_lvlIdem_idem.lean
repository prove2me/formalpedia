-- Prove2me | solution 1 for Formalism.L2.DIV.lvlIdem_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:47.366002+00:00
-- url     : https://prove2.me/submissions/7ae90bf9-4216-46c5-be5b-6e6034050750

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_single_mul_lvlIdem

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution [CharZero K] (P : Subgroup G) (ψ : P →* Kˣ) :
    lvlIdem P ψ * lvlIdem P ψ = lvlIdem P ψ := by
  classical
  conv_lhs => arg 1; unfold lvlIdem
  rw [Finset.sum_mul]
  have e : ∀ h : P, MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) * lvlIdem P ψ =
      (Nat.card P : K)⁻¹ • lvlIdem P ψ := by
    intro h
    have hs : MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) =
        ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • MonoidAlgebra.single (h : G) (1 : K) := by
      first
      | rw [MonoidAlgebra.smul_single', mul_one]
      | rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, smul_mul_assoc, single_mul_lvlIdem, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]
end Formalism.L2.DIV
