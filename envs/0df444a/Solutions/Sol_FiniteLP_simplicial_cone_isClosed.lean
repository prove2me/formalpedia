-- Prove2me | solution 1 for FiniteLP.simplicial_cone_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:42.65481+00:00
-- url     : https://prove2.me/submissions/5c3b5760-c353-4e1f-b29f-d85781d82147

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution {κ ι : Type*} [Fintype κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : EuclideanSpace ℝ ι |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by
  classical
  set L : (s → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
    ∑ k : s, LinearMap.smulRight (LinearMap.proj k) (v k) with hL_def
  have hLval : ∀ c : s → ℝ, L c = ∑ k : s, c k • v k := by
    intro c
    simp [hL_def, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    rw [hLval] at hm
    funext k; exact Fintype.linearIndependent_iff.mp hli m hm k
  have hclosedmap : IsClosedMap L :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot_of_injective hLinj)).isClosedMap
  have hO : IsClosed {c : s → ℝ | ∀ k, 0 ≤ c k} := by
    have : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext c; simp
    rw [this]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (continuous_apply k))
  have hclosed := hclosedmap _ hO
  convert hclosed using 1
  ext y
  constructor
  · rintro ⟨c, hc0, hcoff, rfl⟩
    refine ⟨fun k : s => c k, fun k => hc0 _, ?_⟩
    rw [hLval, ← Finset.sum_attach s (fun j => c j • v j)]
    rfl
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro k; dsimp only; split_ifs with h
      · exact hc0 _
      · exact le_refl 0
    · intro k hk; simp [hk]
    · rw [hLval, ← Finset.sum_attach s (fun j => (if h : j ∈ s then c ⟨j, h⟩ else 0) • v j)]
      apply Finset.sum_congr rfl
      intro k _
      simp [k.2]
end FiniteLP
