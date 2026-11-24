-- Prove2me | solution 1 for BSLambda.exists_apply_eq_and_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:53.965115+00:00
-- url     : https://prove2.me/submissions/0867832f-742d-4e6a-8fe5-a4777f1fd4d7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_apply_ne_of_adj_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Input V → ℝ} (hu : u ≠ 0) (hev : adj g *ᵥ u = μ • u) (β : Bool) :
    ∃ a : Input V, g a = β ∧ u a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hu (funext fun a ↦ show u a = (0 : ℝ) from ?_)
  by_cases hga : g a = β
  · exact hcon a hga
  · -- Every neighbour `y` of `a` has `g y ≠ g a`, hence `g y = β`, hence `u y = 0`.
    have hβ : (!g a) = β := (Bool.eq_not_of_ne (Ne.symm hga)).symm
    have hzero : ∑ y : Input V, adj g a y * u y = 0 :=
      Finset.sum_eq_zero fun y _ ↦ by
        rcases eq_or_ne (adj g a y) 0 with hy | hy
        · rw [hy, zero_mul]
        · rw [hcon y ((Bool.eq_not_of_ne (apply_ne_of_adj_ne_zero g hy).symm).trans hβ), mul_zero]
    exact (mul_eq_zero.mp ((congrFun hev a).symm.trans hzero)).resolve_left hμ
end BSLambda
