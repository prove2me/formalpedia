-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.one_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:41.722405+00:00
-- url     : https://prove2.me/submissions/0eaaf3ac-29c0-4e29-a926-8c0148eb90ff

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Theorems.Thm_Formalism_L2_DIV_CSD_mem_dual_one

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] : (one K).Good 1 where
  symm := by
    refine ⟨fun (x y : K) => ?_⟩
    show starRingEnd K (star x * y) = star y * x
    rw [starRingEnd_apply, star_mul', star_star, mul_comm]
  nondeg := by
    constructor
    · intro (x : K) hx
      have h1 : star x * (1 : K) = 0 := hx (1 : K)
      have h2 : x = (0 : K) := by simpa using h1
      exact h2
    · intro (y : K) hy
      have h1 : star (1 : K) * y = 0 := hy (1 : K)
      have h2 : y = (0 : K) := by simpa using h1
      exact h2
  inv := by intro c γ x y; rfl
  nab_lat := by
    intro c
    show Submodule.IsLattice K (1 : Submodule (𝓞 K) K)
    refine ⟨by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, ?_⟩
    rw [eq_top_iff]
    intro x _
    have : x = x • (1 : K) := by simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.one_le.mp le_rfl))
  del_le := fun _ => le_rfl
  del_stable := by intro c γ y hy; exact hy
  s_pos := Nat.one_pos
  dual_le := by
    intro c (y : K) hy
    have h1 : y ∈ (1 : Submodule (𝓞 K) K) := (mem_dual_one y).mp hy
    exact Submodule.smul_mem _ _ h1
  del_dual := by
    intro c (y : K) hy
    have h1 : y ∈ Formalism.HermitianLatticesTheory.dual (pairOne K) (1 : Submodule (𝓞 K) K) := (mem_dual_one y).mpr hy
    exact Submodule.smul_mem _ _ h1
end Formalism.L2.DIV.CSD
