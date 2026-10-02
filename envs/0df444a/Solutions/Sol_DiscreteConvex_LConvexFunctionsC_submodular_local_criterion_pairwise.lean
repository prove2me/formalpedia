-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.submodular_local_criterion_pairwise
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:22:10.564821+00:00
-- url     : https://prove2.me/submissions/c8af9633-fbac-45f7-9276-3d7e47c10a72

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR

set_option autoImplicit false

namespace SubmodCexD2

open DiscreteConvex.LConvexFunctionsC

/-- The two incomparable points `(1,-1)` and `(-1,1)`. -/
noncomputable def a : Fin 2 → ℝ := ![1, -1]
noncomputable def b : Fin 2 → ℝ := ![-1, 1]

open Classical in
/-- `0` on `{a, b}`, `⊤` elsewhere. -/
noncomputable def g (p : Fin 2 → ℝ) : WithTop ℝ := if p = a ∨ p = b then 0 else ⊤

theorem mem_dom (p : Fin 2 → ℝ) : p ∈ DomR g ↔ (p = a ∨ p = b) := by
  show g p ≠ ⊤ ↔ _
  unfold g
  split_ifs with h
  · simp [h]
  · simp [h]

theorem anti (x y : Fin 2 → ℝ) (hx : x ∈ DomR g) (hy : y ∈ DomR g) (hxy : x ≤ y) : x = y := by
  rw [mem_dom] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · have := hxy 0
    simp [a, b] at this
    linarith
  · have := hxy 1
    simp [a, b] at this
    linarith
  · rfl

theorem ordc : (DomR g).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  have hxy : x = y := anti x y hx hy (le_trans hz.1 hz.2)
  subst hxy
  have : z = x := le_antisymm hz.2 hz.1
  rw [this]; exact hx

theorem off (p : Fin 2 → ℝ) (hp : p ∈ DomR g) (u : Fin 2) (lam : ℝ) (hlam : 0 < lam) :
    g (fun w => p w + lam * (if w = u then 1 else 0)) = ⊤ := by
  by_contra h
  have hq : (fun w => p w + lam * (if w = u then 1 else 0)) ∈ DomR g := h
  have hle : p ≤ (fun w => p w + lam * (if w = u then 1 else 0)) := by
    intro w
    show p w ≤ p w + lam * (if w = u then 1 else 0)
    split_ifs <;> nlinarith
  have heq := congrFun (anti _ _ hp hq hle) u
  simp at heq
  linarith

theorem off2 (p : Fin 2 → ℝ) (hp : p ∈ DomR g) (u v : Fin 2) (lam mu : ℝ) (hmu : 0 < mu) :
    g (fun w => p w + lam * (if w = u then 1 else 0)) +
        g (fun w => p w + mu * (if w = v then 1 else 0)) = ⊤ := by
  rw [off p hp v mu hmu]
  exact WithTop.add_top _

theorem hpair : ∀ u v : Fin 2, u ≠ v → ∀ p ∈ DomR g, ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
      g (fun w => p w + lam * (if w = u then 1 else 0)) +
        g (fun w => p w + mu * (if w = v then 1 else 0)) ≥
      g p + g (fun w => p w + lam * (if w = u then 1 else 0) + mu * (if w = v then 1 else 0)) := by
  intro u v _ p hp lam mu hlam hmu
  rcases hlam.lt_or_eq with hl | hl
  · rw [off p hp u lam hl, WithTop.top_add]
    exact le_top
  rcases hmu.lt_or_eq with hm | hm
  · rw [off2 p hp u v lam mu hm]
    exact le_top
  subst hl; subst hm
  simp

theorem not_sbfr : ¬ SBFR g := by
  intro h
  have h1 := h a b
  have ha : g a = 0 := by unfold g; simp
  have hb : g b = 0 := by unfold g; simp
  have hs : g (a ⊔ b) = ⊤ := by
    unfold g
    rw [if_neg]
    rintro (h' | h')
    · have := congrFun h' 1
      simp [a, b] at this
      norm_num at this
    · have := congrFun h' 0
      simp [a, b] at this
      norm_num at this
  rw [ha, hb, hs, WithTop.top_add] at h1
  simp at h1

end SubmodCexD2

open Classical in
open scoped Pointwise in
open DiscreteConvex.LConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℝ) → WithTop ℝ)
    (hint : (DomR g).OrdConnected)
    (hpair : ∀ u v : V, u ≠ v → ∀ p ∈ DomR g, ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
      g (fun w => p w + lam * (if w = u then 1 else 0)) +
        g (fun w => p w + mu * (if w = v then 1 else 0)) ≥
      g p + g (fun w => p w + lam * (if w = u then 1 else 0) + mu * (if w = v then 1 else 0))),
    SBFR g) := by
  intro H
  exact SubmodCexD2.not_sbfr (H SubmodCexD2.g SubmodCexD2.ordc SubmodCexD2.hpair)
