-- Prove2me | solution 1 for FriedmannDiscounted.discounted_bellman
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:39:18.603032+00:00
-- url     : https://prove2.me/submissions/bf92d9e4-bc5a-4a7a-bf47-50094492aed5

import Definitions.Def_friedmann_payoff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

set_option autoImplicit false

section Mod_discounted_bellman
set_option autoImplicit false

namespace FriedmannDiscounted

open scoped BigOperators
open Matrix

lemma transition_mulVec {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    (transition G σ τ *ᵥ x) v = x (if G.arena.owner v = false then σ v else τ v) := by
  classical
  dsimp [transition, mulVec, dotProduct]
  simp

lemma one_sub_discount_transition_mulVec {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (σ τ : V → V) (x : V → ℚ) (v : V) :
    ((1 - G.discount • transition G σ τ) *ᵥ x) v =
      x v - G.discount * x (if G.arena.owner v = false then σ v else τ v) := by
  rw [sub_mulVec, one_mulVec, Pi.sub_apply, ← transition_mulVec G σ τ x v]
  congr 1
  dsimp [mulVec, dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma isUnit_det_one_sub_discount_transition {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    IsUnit (1 - G.discount • transition G σ τ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  rcases Matrix.exists_mulVec_eq_zero_iff.mpr hdet with ⟨x, hxne, hx⟩
  have hfp : ∀ v, x v = G.discount * x (if G.arena.owner v = false then σ v else τ v) := by
    intro v
    have hv := congrFun hx v
    rw [Pi.zero_apply, one_sub_discount_transition_mulVec] at hv
    linarith
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra hempty
    apply hxne
    ext v
    exact False.elim (hempty ⟨v, Finset.mem_univ v⟩)
  set M := Finset.univ.sup' hne (fun v => |x v|)
  have hM : ∀ v, |x v| ≤ M := fun v => Finset.le_sup' (fun u => |x u|) (Finset.mem_univ v)
  obtain ⟨v₀, _, hv₀⟩ := Finset.exists_mem_eq_sup' hne (fun v => |x v|)
  have hβ0 : 0 < G.discount := hG.2.1
  have hβ1 : G.discount < 1 := hG.2.2
  by_cases hMpos : 0 < M
  · have hstep : |x v₀| = G.discount * |x (if G.arena.owner v₀ = false then σ v₀ else τ v₀)| := by
      rw [hfp v₀, abs_mul, abs_of_pos hβ0]
    have hle : G.discount * |x (if G.arena.owner v₀ = false then σ v₀ else τ v₀)| ≤ G.discount * M :=
      mul_le_mul_of_nonneg_left (hM _) (le_of_lt hβ0)
    have hlt : G.discount * M < 1 * M :=
      mul_lt_mul_of_pos_right hβ1 hMpos
    linarith
  · apply hxne
    ext v
    have h1 : |x v| ≤ 0 := le_trans (hM v) (not_lt.mp hMpos)
    exact abs_nonpos_iff.mp h1

theorem discounted_bellman {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    (∀ v, playValue G σ τ v = G.reward v + G.discount *
      playValue G σ τ (if G.arena.owner v = false then σ v else τ v)) ∧
    ∀ x : V → ℚ,
      (∀ v, x v = G.reward v + G.discount *
        x (if G.arena.owner v = false then σ v else τ v)) → x = playValue G σ τ := by
  have hunit := isUnit_det_one_sub_discount_transition G hG σ τ
  set A := 1 - G.discount • transition G σ τ
  constructor
  · intro v
    have hmul : A *ᵥ playValue G σ τ = G.reward := by
      unfold playValue
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv A hunit, one_mulVec]
    have hv := congrFun hmul v
    rw [one_sub_discount_transition_mulVec] at hv
    linarith
  · intro x hx
    have hmul : A *ᵥ x = G.reward := by
      ext v
      rw [one_sub_discount_transition_mulVec]
      linarith [hx v]
    unfold playValue
    rw [← hmul, mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, one_mulVec]

end FriedmannDiscounted

end Mod_discounted_bellman

open FriedmannDiscounted in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ τ : V → V) :
    (∀ v, playValue G σ τ v = G.reward v + G.discount *
      playValue G σ τ (if G.arena.owner v = false then σ v else τ v)) ∧
    ∀ x : V → ℚ,
      (∀ v, x v = G.reward v + G.discount *
        x (if G.arena.owner v = false then σ v else τ v)) → x = playValue G σ τ := by
  first
    | exact FriedmannDiscounted.discounted_bellman
    | (apply FriedmannDiscounted.discounted_bellman <;> assumption)
