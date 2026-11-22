-- Prove2me | solution 1 for CoDecompFO.lemma_5_16
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:07:28.624181+00:00
-- url     : https://prove2.me/submissions/89accb48-2670-468a-b839-87162afcba29

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- Lemma 5.16 at every level `m`, for every assignment `l` and every number `k` of head points. -/
theorem l516_aux {σ : Sig} (G : Type) [σ.lang.Structure G] (k : ℕ)
    (ψ : σ.lang.BoundedFormula Empty k) :
    ∀ (m : ℕ) (l : List G),
      AltSat (G := G) ψ m l ↔
        ∃ H : HTh σ G k m, IsInducedTotal σ k m l H ∧ AllHyp ψ m H := by
  intro m
  induction m with
  | zero =>
    intro l
    constructor
    · intro h
      refine ⟨({atomsOf σ k l} : Set (Set (σ.Atom k))), rfl, ?_⟩
      intro N hN
      have hN' : N = atomsOf σ k l := hN
      rw [hN']
      exact h
    · rintro ⟨H, hH, hA⟩
      have hH' : H = ({atomsOf σ k l} : Set (Set (σ.Atom k))) := hH
      exact hA (atomsOf σ k l) (by rw [hH']; exact Set.mem_singleton _)
  | succ m ih =>
    intro l
    constructor
    · intro h
      have h' : ∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y]) := h
      choose y hy using h'
      have h2 : ∀ x, ∃ H : HTh σ G k m,
          IsInducedTotal σ k m (l ++ [x, y x]) H ∧ AllHyp ψ m H := fun x => (ih _).1 (hy x)
      choose Hx hI hA using h2
      let H0 : G → Set (Set (G × HTh σ G k m)) := fun x => {{(y x, Hx x)}}
      refine ⟨H0, ?_, ?_⟩
      · show ∀ x : G, (H0 x).Nonempty ∧ ∀ p ∈ H0 x, p.Nonempty ∧
          ∀ c ∈ p, IsInducedTotal σ k m (l ++ [x, c.1]) c.2
        intro x
        refine ⟨⟨_, Set.mem_singleton _⟩, ?_⟩
        intro p hp
        have hp' : p = {(y x, Hx x)} := hp
        subst hp'
        refine ⟨⟨_, Set.mem_singleton _⟩, ?_⟩
        intro c hc
        have hc' : c = (y x, Hx x) := hc
        subst hc'
        exact hI x
      · show ∀ x', ∀ p ∈ H0 x', ∀ c ∈ p, AllHyp ψ m c.2
        intro x p hp c hc
        have hp' : p = {(y x, Hx x)} := hp
        subst hp'
        have hc' : c = (y x, Hx x) := hc
        subst hc'
        exact hA x
    · rintro ⟨H, hI, hA⟩
      have hI' : ∀ x : G, (H x).Nonempty ∧ ∀ p ∈ H x, p.Nonempty ∧
          ∀ c ∈ p, IsInducedTotal σ k m (l ++ [x, c.1]) c.2 := hI
      have hA' : ∀ x', ∀ p ∈ H x', ∀ c ∈ p, AllHyp ψ m c.2 := hA
      show ∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y])
      intro x
      obtain ⟨⟨p, hp⟩, hI2⟩ := hI' x
      obtain ⟨⟨c, hc⟩, hI3⟩ := hI2 p hp
      exact ⟨c.1, (ih _).2 ⟨c.2, hI3 c hc, hA' x p hp c hc⟩⟩

end CoDecompFO

theorem solution {σ : CoDecompFO.Sig} (G : Type) [σ.lang.Structure G] (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : CoDecompFO.IsMatrix ψ) :
    CoDecompFO.AltSat (G := G) ψ ℓ [] ↔
      ∃ H : CoDecompFO.HTh σ G (2 * ℓ) ℓ,
        CoDecompFO.IsInducedTotal σ (2 * ℓ) ℓ [] H ∧ CoDecompFO.AllHyp ψ ℓ H :=
  CoDecompFO.l516_aux G (2 * ℓ) ψ ℓ []
