-- Prove2me | solution 1 for Formalism.L2.DIV.Test.aug_lvlIdem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:48.757798+00:00
-- url     : https://prove2.me/submissions/d04b7eed-1b05-4989-8b7d-e55c1f5225c3

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
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (P : Subgroup G) : aug K G (lvlIdem P (1 : P →* Kˣ)) = 1 := by
  classical
  unfold lvlIdem aug
  rw [map_sum]
  have e : ∀ h : P, (MonoidAlgebra.lift K K G (1 : G →* K)) (MonoidAlgebra.single (h : G)
      ((Nat.card P : K)⁻¹ * (((1 : P →* Kˣ) h⁻¹ : Kˣ) : K))) = (Nat.card P : K)⁻¹ := by
    intro h
    rw [MonoidAlgebra.lift_single]
    simp
  rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
end Formalism.L2.DIV.Test
