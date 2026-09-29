-- Prove2me | solution 1 for BertsekasDP.label_correcting_invariant
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:16:33.56532+00:00
-- url     : https://prove2.me/submissions/9f3cf73d-d36f-4d55-ae52-045bb482c689

import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_BertsekasLCState

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace DPInvariantProof
variable {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)

lemma walk_append {a i j : V} {l : List V}
    (h : BertsekasIsWalkFrom G a i l) (hij : (i,j) ∈ G.arcs) :
    BertsekasIsWalkFrom G a j (l ++ [j]) := by
  rcases h with ⟨hne,hchain,hhead,hlast⟩
  refine ⟨by simp, hchain.append (by simp) ?_, ?_, by simp⟩
  · intro x hx y hy
    simp only [hlast, Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst x
    subst y
    exact hij
  · simpa [List.head?_append, hhead]

lemma length_cons (a b : V) (l : List V) :
    BertsekasWalkLength G (a :: b :: l) = G.length a b + BertsekasWalkLength G (b :: l) := by
  simp [BertsekasWalkLength]

lemma length_append {i j : V} {l : List V} (hne : l ≠ []) (hlast : l.getLast? = some i) :
    BertsekasWalkLength G (l ++ [j]) = BertsekasWalkLength G l + G.length i j := by
  induction l with
  | nil => simp at hne
  | cons a l ih =>
    cases l with
    | nil =>
      have hai : a = i := by simpa using hlast
      subst a
      simp [BertsekasWalkLength]
    | cons b l =>
      have ht := ih (by simp) (by simpa using hlast)
      simp only [List.cons_append] at ht
      simp only [List.cons_append, length_cons] at ⊢
      rw [ht]
      ring

def valid (σ : BertsekasLCState V) : Prop :=
  (∀ j : V, σ.label j = ⊤ ∨ ∃ l, BertsekasIsWalkFrom G G.s j l ∧
    σ.label j = (BertsekasWalkLength G l : EReal)) ∧
  (σ.upper = ⊤ ∨ ∃ l, BertsekasIsWalkFrom G G.s G.t l ∧
    σ.upper = (BertsekasWalkLength G l : EReal))

lemma initial_valid : valid G (BertsekasLCInit G) := by
  constructor
  · intro j
    by_cases hj : j = G.s
    · subst j
      right
      refine ⟨[G.s], ?_, ?_⟩
      · simp [BertsekasIsWalkFrom]
      · simp [BertsekasLCInit, BertsekasWalkLength]
    · left; simp [BertsekasLCInit, hj]
  · left; rfl

lemma child_valid (i j : V) (σ : BertsekasLCState V) (hσ : valid G σ) :
    valid G (BertsekasLCProcessChild G i σ j) := by
  classical
  unfold BertsekasLCProcessChild
  split
  · rename_i hc
    have hfinite : σ.label i ≠ ⊤ := by
      intro ht
      have hh := hc.2
      simp [ht] at hh
    obtain ⟨l,hl,he⟩ := (hσ.1 i).resolve_left hfinite
    have hwalk := walk_append G hl hc.1
    have hlen := length_append G hl.1 hl.2.2.2 (j := j)
    constructor
    · intro v
      by_cases hv : v = j
      · subst v
        right
        refine ⟨l ++ [j], hwalk, ?_⟩
        simpa [he, hlen, EReal.coe_add]
      · simpa [Function.update_of_ne hv] using hσ.1 v
    · by_cases hj : j = G.t
      · right
        refine ⟨l ++ [j], ?_, ?_⟩
        · simpa [hj] using hwalk
        · have hlen' := hlen
          rw [hj] at hlen'
          simp [hj, he, hlen', EReal.coe_add]
      · simpa [hj] using hσ.2
  · exact hσ

lemma fold_valid (i : V) (js : List V) (σ : BertsekasLCState V) (hσ : valid G σ) :
    valid G (js.foldl (BertsekasLCProcessChild G i) σ) := by
  induction js generalizing σ with
  | nil => exact hσ
  | cons j js ih => exact ih _ (child_valid G i j σ hσ)

lemma step_valid {σ σ' : BertsekasLCState V} (hσ : valid G σ)
    (hstep : BertsekasLCStep G σ σ') : valid G σ' := by
  obtain ⟨i, hi, js, hperm, rfl⟩ := hstep
  exact fold_valid G i js _ hσ

end DPInvariantProof

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V) (σ : BertsekasLCState V)
    (hreach : Relation.ReflTransGen (BertsekasLCStep G) (BertsekasLCInit G) σ) :
    (∀ j : V, σ.label j = ⊤ ∨
      ∃ l, BertsekasIsWalkFrom G G.s j l ∧
        σ.label j = (BertsekasWalkLength G l : EReal)) ∧
    (σ.upper = ⊤ ∨
      ∃ l, BertsekasIsWalkFrom G G.s G.t l ∧
        σ.upper = (BertsekasWalkLength G l : EReal)) := by
  induction hreach with
  | refl => exact DPInvariantProof.initial_valid G
  | tail hreach hstep ih => exact DPInvariantProof.step_valid G ih hstep

#print axioms solution
