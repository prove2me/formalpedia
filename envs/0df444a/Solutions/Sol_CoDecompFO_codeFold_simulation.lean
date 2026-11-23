-- Prove2me | solution 1 for CoDecompFO.codeFold_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:05.911769+00:00
-- url     : https://prove2.me/submissions/8f9b0b98-5c3d-4579-b67d-a6dbc139129c

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

open FirstOrder
open CoDecompFO

/-- Local numeric implementations of the induced table and of the reduced pullback lift to a
simulation of the whole bottom-up computation. -/
theorem solution (σ : Sig) (φ : σ.lang.Sentence) (w C : ℕ)
    (leaf join : List ℕ → ℕ)
    (code : ∀ {n : ℕ}, HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ) → ℕ)
    (hleaf : ∀ B : Bag σ,
      code (ind (sigmaEq σ) (2 * quantCount φ) (quantCount φ)
        (Strat.full (Fin B.withEq.n) (quantCount φ)) []) =
        leaf (frame [encF φ, encBag B]))
    (hjoin : ∀ (A D K : Bag σ) (g : Fin D.n → Fin K.n) (h : Fin A.n → Fin K.n)
      (H : HTh (sigmaEq σ) (Fin A.n) (2 * quantCount φ) (quantCount φ))
      (Hc : HTh (sigmaEq σ) (Fin D.n) (2 * quantCount φ) (quantCount φ)),
      code (push (Fib.snd : Fib g h → Fin A.n) (quantCount φ) (pb g h (quantCount φ) Hc H)) =
        join (frame [encF φ, encBag A, encBag D, encBag K,
          List.ofFn (fun x => (h x).val), List.ofFn (fun x => (g x).val),
          [code H], [code Hc] ]))
    (hcode : ∀ (n : ℕ) (H : HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ)),
      n ≤ w → code H ≤ C) :
    ∀ (T : CoDecomp σ), width T ≤ w →
      ∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
        T.CodeFold r (encF φ) leaf join t S v →
        v ≤ C ∧ ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag t).n)
          (2 * quantCount φ) (quantCount φ),
          T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) t S H ∧ code H = v := by
  intro T hTw r t S v hfold
  induction hfold with
  | base t =>
      refine ⟨?_, ind (sigmaEq σ) (2 * quantCount φ) (quantCount φ)
        (Strat.full (Fin (T.withEq.bag t).n) (quantCount φ)) [],
        CoDecomp.IsFold.leaf (T := T.withEq) (r := r) t, ?_⟩
      · rw [← hleaf (T.bag t)]
        exact hcode _ _ ((Finset.le_sup (f := fun t => (T.bag t).n) (Finset.mem_univ t)).trans hTw)
      · exact hleaf (T.bag t)
  | @step t S e he v vc htop hnot hchild iht ihc =>
      rcases iht with ⟨hv, H, Hfold, rfl⟩
      rcases ihc with ⟨hvc, Hc, Hcfold, rfl⟩
      refine ⟨?_, push (Fib.snd :
          Fib (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) →
            Fin (T.withEq.bag t).n) (quantCount φ)
        (pb (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem)
          (quantCount φ) Hc H),
        CoDecomp.IsFold.join (T := T.withEq) (r := r) t S e he H Hc Hfold hnot Hcfold, ?_⟩
      · calc
          join (frame [encF φ, encBag (T.bag t), encBag (T.bag (T.child e t)), encBag (T.adh e),
              List.ofFn (fun x => (T.edgeMap e t he.top_mem x).val),
              List.ofFn (fun x => (T.edgeMap e (T.child e t) he.child_mem x).val),
              [code H], [code Hc] ]) =
              code (push (Fib.snd :
                Fib (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) →
                  Fin (T.bag t).n) (quantCount φ)
                (pb (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem)
                  (quantCount φ) Hc H)) :=
            (hjoin (T.bag t) (T.bag (T.child e t)) (T.adh e)
              (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) H Hc).symm
          _ ≤ C := hcode _ _
            ((Finset.le_sup (f := fun t => (T.bag t).n) (Finset.mem_univ t)).trans hTw)
      · exact hjoin (T.bag t) (T.bag (T.child e t)) (T.adh e)
          (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) H Hc
