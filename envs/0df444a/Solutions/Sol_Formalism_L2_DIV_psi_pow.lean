-- Prove2me | solution 1 for Formalism.L2.DIV.psi_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:28.896063+00:00
-- url     : https://prove2.me/submissions/ddb8bea6-790d-49cf-8e0b-d4fadec68fa7

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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : ((ψ h : Kˣ) : K) ^ Nat.card P = 1 := by
  have h1 : h ^ Nat.card P = 1 := by
    first
    | exact pow_card_eq_one'
    | exact pow_natCard_eq_one
    | simp
  have h2 : (ψ h) ^ Nat.card P = 1 := by rw [← map_pow, h1, map_one]
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
end Formalism.L2.DIV
