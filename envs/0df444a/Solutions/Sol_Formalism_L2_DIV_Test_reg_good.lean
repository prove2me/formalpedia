-- Prove2me | solution 1 for Formalism.L2.DIV.Test.reg_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:35.08096+00:00
-- url     : https://prove2.me/submissions/8f88aa9d-0977-42f3-bb26-7eeb9fc3c6d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_Test_mem_dual_one

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
theorem _root_.solution : (regCSD K G).Good 1 where
  symm := ⟨fun x y => by
    show starRingEnd K (star x * y) = star y * x
    rw [starRingEnd_apply, star_mul', star_star, mul_comm]⟩
  nondeg := by
    constructor
    · intro x hx
      have := hx 1
      simpa using this
    · intro y hy
      have := hy 1
      simpa using this
  inv := fun c γ x y => rfl
  nab_lat := fun c => ⟨by
    show (1 : Submodule (𝓞 K) K).FG
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, by
    show Submodule.span K (((1 : Submodule (𝓞 K) K) : Set K)) = ⊤
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : K) ∈ Submodule.span K (((1 : Submodule (𝓞 K) K) : Set K)) :=
      Submodule.subset_span (Submodule.one_le.mp le_rfl)
    simpa using Submodule.smul_mem _ x h1⟩
  del_le := fun c => le_rfl
  del_stable := fun c γ y hy => hy
  s_pos := Nat.one_pos
  dual_le := fun c y hy => by
    rw [Nat.cast_one, one_smul]
    exact (mem_dual_one K y).mp hy
  del_dual := fun c y hy => by
    rw [Nat.cast_one, one_smul]
    exact (mem_dual_one K y).mpr hy
end Formalism.L2.DIV.Test
