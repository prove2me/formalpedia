-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.gaMat_lvlIdem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:37.912634+00:00
-- url     : https://prove2.me/submissions/2757f3ec-28a8-4b5f-bd72-417b9319528a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_eq_lift

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
open Formalism.L2.DIV.CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
open Classical
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (P : Subgroup G) (ψ : P →* Kˣ) :
    S.gaMat r (lvlIdem P ψ) =
      ∑ h : P, ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • S.actMat r (h : G) := by
  rw [S.gaMat_eq_lift r]
  unfold lvlIdem
  rw [map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.lift_single]
  rfl
end Formalism.L2.DIV.CSD
