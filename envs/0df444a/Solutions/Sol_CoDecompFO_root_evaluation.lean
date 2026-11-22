-- Prove2me | solution 1 for CoDecompFO.root_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:07:36.624171+00:00
-- url     : https://prove2.me/submissions/6b76f46a-6f5a-4731-8708-7fe75e508766

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

theorem root_eval_aux {σ : Sig} (G P : Type) [σ.lang.Structure G] (π : G → P) (k : ℕ)
    (ψ : σ.lang.BoundedFormula Empty k) :
    ∀ (m : ℕ) (l : List G),
      AltSat (G := G) ψ m l ↔ eval ψ m (push π m (ind σ k m (Strat.full G m) l)) := by
  intro m
  induction m with
  | zero =>
    intro l
    simp [AltSat, eval, push, ind, HTh.hyps]
  | succ m ih =>
    intro l
    simp only [AltSat, eval, push, ind, Strat.full]
    constructor
    · intro h x' p hp
      obtain ⟨x, p0, hx, hp0, rfl⟩ := hp
      rw [Set.mem_singleton_iff] at hp0
      subst hp0
      obtain ⟨y, hy⟩ := h x
      refine ⟨(π y, push π m (ind σ k m (Strat.full G m) (l ++ [x, y]))), ?_, ?_⟩
      · exact ⟨(y, ind σ k m (Strat.full G m) (l ++ [x, y])), ⟨(y, Strat.full G m), ⟨y, rfl⟩, rfl⟩, rfl⟩
      · exact (ih _).1 hy
    · intro h x
      obtain ⟨c, hc, hev⟩ := h (π x) _ ⟨x, _, rfl, rfl, rfl⟩
      obtain ⟨c0, ⟨c1, ⟨y, rfl⟩, rfl⟩, rfl⟩ := hc
      exact ⟨y, (ih _).2 hev⟩

end CoDecompFO

theorem solution {σ : CoDecompFO.Sig} (G P : Type) [σ.lang.Structure G] (π : G → P) (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : CoDecompFO.IsMatrix ψ) :
    CoDecompFO.AltSat (G := G) ψ ℓ [] ↔
      CoDecompFO.eval ψ ℓ (CoDecompFO.push π ℓ (CoDecompFO.ind σ (2 * ℓ) ℓ (CoDecompFO.Strat.full G ℓ) [])) :=
  CoDecompFO.root_eval_aux G P π (2 * ℓ) ψ ℓ []
