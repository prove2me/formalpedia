-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_30
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:41:24.386246+00:00
-- url     : https://prove2.me/submissions/af9cc567-a69a-4007-b21b-3215013f014f

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

open CategoryTheory CategoryTheory.Limits Opposite ConcreteSheaves.Quasitopos

universe u
variable {D : Type u} [SmallCategory D]

lemma omega_map {T : D} {X Y : D} (g : Y ⟶ X) (φ : (omegaPresheaf T).obj (op X)) :
    (omegaPresheaf T).map g.op φ = fun d => φ (d ≫ g) := rfl

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    IsDSpace K T (omegaPresheaf T) := by
  refine ⟨?_, ?_⟩
  · intro E R hR x hx
    have key : ∀ {Y1 : D} (f1 : Y1 ⟶ E) (h1 : R f1) (a : T ⟶ Y1)
        {Y2 : D} (f2 : Y2 ⟶ E) (h2 : R f2) (b : T ⟶ Y2), a ≫ f1 = b ≫ f2 →
        (x f1 h1 : (T ⟶ Y1) → Bool) a = (x f2 h2 : (T ⟶ Y2) → Bool) b := by
      intro Y1 f1 h1 a Y2 f2 h2 b hab
      have := congrFun (hx a b h1 h2 hab) (𝟙 T)
      rw [omega_map, omega_map] at this
      simpa using this
    choose Y f hf y hy using hK.jointlySurj R hR
    let t : (omegaPresheaf T).obj (op E) := fun d => (x (f d) (hf d) : (T ⟶ Y d) → Bool) (y d)
    refine ⟨t, ?_, ?_⟩
    · intro Z g hg
      rw [omega_map]
      funext d'
      exact key _ _ _ g hg d' (by rw [hy])
    · intro t' ht'
      funext d
      have e := congrFun (ht' (f d) (hf d)) (y d)
      rw [omega_map] at e
      change (t' : (T ⟶ E) → Bool) (y d ≫ f d) = _ at e
      rw [hy] at e
      exact e
  · intro E φ ψ h
    funext d
    have := congrFun (congrFun h d) (𝟙 T)
    change (φ : (T ⟶ E) → Bool) (𝟙 T ≫ d) = (ψ : (T ⟶ E) → Bool) (𝟙 T ≫ d) at this
    simpa using this
