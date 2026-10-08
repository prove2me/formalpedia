-- Prove2me | solution 1 for FiniteMagmaE677.linear_extension_e255
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T07:06:05.968725+00:00
-- url     : https://prove2.me/submissions/b5d4bbc7-335c-4896-830c-6c8c1f648235

import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Prod
import Definitions.Def_FiniteMagmaE677
import Definitions.Def_LinearExtension_opP
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

universe u v

open LinearExtension

/-!
# No counterexamples via linear extension

Let `G` be a finite magma satisfying E677 *and* E255, `M` a finite abelian group, and
suppose the componentwise operation

`(x, s) ⋄ (y, t) = (x ⋄_G y, α_{x,y} s + β_{x,y} t + c_{x,y})`

(with additive endomorphisms `α, β : G → G → (M →+ M)` and constants `c : G → G → M`)
satisfies E677. Then it also satisfies E255 — the blueprint Chapter 13 "no
counterexamples via linear extension" lemma.

Proof: fix `(y, t)`. Since `G` satisfies 255, `x := ((y ⋄ y) ⋄ y)` fixes `y`. The fiber
map `α_{x,y}` is injective: if `α_{x,y} s = α_{x,y} s'`, the left translations
`L_{(x,s)}` and `L_{(x,s')}` agree on the `y`-fiber `{y} × M`, and
`L_{(x,s)}(y,0) = L_{(x,s')}(y,0) =: q₀` because the second coordinate of that product
only involves `α_{x,y} s`. In the base, `E677(y,x)` with `x ⋄ y = y` and injectivity of
`L_x` give `y ⋄ (y ⋄ x) = y`, so the composite `L_{(y,0)} ∘ L_{q₀}` inside the E677
identity at `((y,0),(x,·))` lands in the `y`-fiber, where the two outer translations
agree. Comparing the identities for `s` and `s'` and cancelling the three injective left
translations `L_{(x,s')}`, `L_{(y,0)}`, `L_{q₀}` yields `(x,s) = (x,s')`, i.e. `s = s'`.

An injective self-map of the finite group `M` is surjective, so some `s` solves
`α_{x,y} s = t - β_{x,y} t - c_{x,y}`, and `(x,s)` is a fixer of `(y,t)`; fixer
uniqueness then gives E255 at `(y,t)`.
-/



private theorem lin_ext {G : Type u} [Fintype G] (opG : G → G → G)
    (hG : FiniteMagmaE677.E677 opG) (hG255 : FiniteMagmaE677.E255 opG)
    {M : Type v} [AddCommGroup M] [Fintype M]
    (α β : G → G → (M →+ M)) (c : G → G → M)
    (h : FiniteMagmaE677.E677 (opP opG α β c)) :
    FiniteMagmaE677.E255 (opP opG α β c) := by
  classical
  haveI : Fintype (G × M) := inferInstance
  have hinjL : ∀ v w w' : G × M, opP opG α β c v w = opP opG α β c v w' → w = w' :=
    fun v w w' heq =>
      (FiniteMagmaE677.left_bijective (opP opG α β c) h v).1 heq
  -- base identity: opG x y = y implies opG y (opG y x) = y
  have hbase : ∀ x y : G, opG x y = y → opG y (opG y x) = y := by
    intro x y hxy
    have e := hG y x
    rw [hxy] at e
    refine (FiniteMagmaE677.left_bijective opG hG x).1 ?_
    calc opG x (opG y (opG y x)) = y := e.symm
      _ = opG x y := hxy.symm
  -- injectivity of the fiber map at a base fixer: the three-cancellation argument
  have key : ∀ x y : G, opG x y = y → ∀ s s' : M, α x y s = α x y s' → s = s' := by
    intro x y hxy s s' hα
    have hbase' := hbase x y hxy
    -- the two left translations agree on the y-fiber
    have hfiber : ∀ m : M, opP opG α β c (x, s) (y, m) = opP opG α β c (x, s') (y, m) := by
      intro m
      simp only [opP_apply]
      exact Prod.ext rfl (by rw [hα])
    -- the E677 identities, inner value identified via fiber agreement
    have I := h (y, (0:M)) (x, s)
    have II := h (y, (0:M)) (x, s')
    rw [hfiber (0:M)] at I
    -- I  : (y,0) = L_{(x,s)} (L_{(y,0)} (L_{q} (x,s)))   with q = L_{(x,s')}(y,0)
    -- II : (y,0) = L_{(x,s')} (L_{(y,0)} (L_{q} (x,s')))
    -- middle composite lands in the y-fiber (for the two inner arguments used)
    have hCy : ∃ Cy : M, opP opG α β c (y, (0:M))
        (opP opG α β c (opP opG α β c (x, s') (y, (0:M))) (x, s)) = (y, Cy) := by
      refine ⟨(opP opG α β c (y, (0:M))
        (opP opG α β c (opP opG α β c (x, s') (y, (0:M))) (x, s))).2, ?_⟩
      refine Prod.ext ?_ rfl
      simp only [opP_apply]
      rw [hxy, hbase']
    obtain ⟨Cy, hCy⟩ := hCy
    rw [hCy] at I
    -- swap the outer translation using fiber agreement
    have I' : (y, (0:M)) = opP opG α β c (x, s') (y, Cy) :=
      I.trans (hfiber Cy)
    -- cancel L_{(x,s')}
    have step1 : (y, Cy) = opP opG α β c (y, (0:M))
        (opP opG α β c (opP opG α β c (x, s') (y, (0:M))) (x, s')) :=
      hinjL (x, s') _ _ (I'.symm.trans II)
    -- cancel L_{(y,0)}
    have step2 : opP opG α β c (opP opG α β c (x, s') (y, (0:M))) (x, s)
        = opP opG α β c (opP opG α β c (x, s') (y, (0:M))) (x, s') :=
      hinjL (y, (0:M)) _ _ (by rw [← step1, hCy])
    -- cancel L_{q0}
    exact congrArg Prod.snd (hinjL _ _ _ step2)
  -- main argument
  intro e
  obtain ⟨y, t⟩ := e
  have hfix := hG255 y
  have hxy : opG (opG (opG y y) y) y = y := hfix.symm
  have hinjα : Function.Injective (fun m : M => α (opG (opG y y) y) y m) :=
    fun m m' hm => key _ y hxy m m' hm
  haveI : Finite M := Finite.of_fintype M
  have hsurjα : Function.Surjective (fun m : M => α (opG (opG y y) y) y m) :=
    Finite.injective_iff_surjective.mp hinjα
  obtain ⟨s, hs⟩ := hsurjα (t - β _ y t - c _ y)
  have hfixer : opP opG α β c (opG (opG y y) y, s) (y, t) = (y, t) := by
    simp only [opP_apply, hxy, hs]
    abel
  have huniq := FiniteMagmaE677.fixer_unique (opP opG α β c) h (y, t)
    (opG (opG y y) y, s) hfixer
  rw [← huniq]
  exact hfixer.symm

theorem solution {G : Type u} [Fintype G] (opG : G → G → G)
    (hG : FiniteMagmaE677.E677 opG) (hG255 : FiniteMagmaE677.E255 opG)
    {M : Type v} [AddCommGroup M] [Fintype M]
    (α β : G → G → (M →+ M)) (c : G → G → M)
    (h : FiniteMagmaE677.E677 (LinearExtension.opP opG α β c)) :
    FiniteMagmaE677.E255 (LinearExtension.opP opG α β c) :=
  lin_ext opG hG hG255 α β c h
