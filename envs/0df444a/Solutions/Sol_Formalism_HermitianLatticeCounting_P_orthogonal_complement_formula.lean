-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.960329+00:00
-- url     : https://prove2.me/submissions/6586c1d4-dd79-42b2-89f4-65e156a836c8

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : PerpCompl := by
  intro K U _ _ _ _ σ hσ B hR hL r A A' hU hA hA' hsup
  have mem : ∀ (S : Submodule K U) (x : U), x ∈ perpR B S ↔ ∀ a ∈ S, B a x = 0 := by
    intro S x; simp [perpR, Submodule.mem_iInf]
  have lower : ∀ S : Submodule K U, finrank K S = r + 1 → r + 1 ≤ finrank K (perpR B S) := by
    intro S hS
    let bs := Module.finBasisOfFinrankEq K S hS
    let Φ : U →ₗ[K] (Fin (r + 1) → K) :=
      { toFun := fun x i => σ (B (bs i : U) x)
        map_add' := by intro x y; ext i; simp
        map_smul' := by intro k x; ext i; simp [hσ] }
    have hker : LinearMap.ker Φ = perpR B S := by
      ext x; rw [LinearMap.mem_ker, mem]; constructor
      · intro h a ha
        have hi : ∀ i, B (bs i : U) x = 0 := by
          intro i
          have h2 : σ (B (bs i : U) x) = 0 := congrFun h i
          exact (map_eq_zero σ).mp h2
        have h3 : a = ∑ i, (bs.repr ⟨a, ha⟩ i) • (bs i : U) := by
          have h4 := congrArg (S.subtype) (bs.sum_repr ⟨a, ha⟩)
          rw [map_sum] at h4
          simpa only [map_smul, Submodule.subtype_apply] using h4.symm
        rw [h3]; simp [hi]
      · intro h; ext i
        show σ (B (bs i : U) x) = 0
        rw [h _ (bs i).2, map_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have hr : finrank K (LinearMap.range Φ) ≤ r + 1 := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    rw [hker] at h1; omega
  have hinf : perpR B A ⊓ perpR B A' = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨h1, h2⟩ := hx
    have h1' := (mem A x).mp h1
    have h2' := (mem A' x).mp h2
    refine (Submodule.mem_bot K).mpr (hR x fun y => ?_)
    have hy : y ∈ A ⊔ A' := by rw [hsup]; trivial
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hy
    simp [h1' a ha, h2' a' ha']
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (perpR B A) (perpR B A')
  rw [hinf, finrank_bot, add_zero] at hs
  have hle := Submodule.finrank_le (perpR B A ⊔ perpR B A')
  have l1 := lower A hA
  have l2 := lower A' hA'
  refine ⟨by omega, by omega, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr ?_⟩⟩
  exact Submodule.eq_top_of_finrank_eq (by omega)
end Formalism.HermitianLatticeCounting.P
