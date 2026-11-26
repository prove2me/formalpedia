-- Prove2me | solution 1 for FixedMachinePrec.lemma_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:12.36644+00:00
-- url     : https://prove2.me/submissions/c056065a-dff1-4dd3-aec2-8d7903796b77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FixedMachinePrec_bucket_pass_closed
import Theorems.Thm_FixedMachinePrec_pass_trace_certificate

open FixedMachinePrec

private theorem chain_reaches {E : ℕ → ℕ → Prop} {i j : ℕ} (rest : List ℕ)
    (hc : (i :: rest).IsChain E) (hl : (i :: rest).getLast? = some j) : Relation.ReflTransGen E i j := by
  induction rest generalizing i with
  | nil => have hij : i = j := by simpa using hl
           subst j
           exact .refl
  | cons x xs ih =>
    obtain ⟨hix, htail⟩ := List.isChain_cons_cons.mp hc
    exact Relation.ReflTransGen.head hix (ih htail (by simpa using hl))

theorem solution {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (Fcut : Finset (Finset (Fin N))) (W : Finset (Fin N))
    (lk : Finset (Fin N) → Bool) :
    let st := buildStates prec m Fcut W
    let E : ℕ → ℕ → Prop := fun i j => edge st lk i j = true
    let initial : ℕ → Prop := fun i => ∃ a, st[i]? = some a ∧ lk a.L = true
    (∀ j < st.length,
      ((reachPass st lk).1 j = true ↔ ∃ i, initial i ∧ Relation.ReflTransGen E i j)) ∧
    (∀ j < st.length, (reachPass st lk).1 j = true →
      let path := tracePath (reachPass st lk).2 st.length j
      ∃ i₁ rest, path = i₁ :: rest ∧ initial i₁ ∧ (reachPass st lk).2 i₁ = .start ∧
        path.getLast? = some j ∧ path.IsChain E) := by
  dsimp only
  let st := buildStates prec m Fcut W
  obtain ⟨hinit,hclosed⟩ := bucket_pass_closed m prec hm Fcut W lk
  refine ⟨?_, fun j hj h => pass_trace_certificate st lk j hj h⟩
  intro j hj
  constructor
  · intro h
    obtain ⟨i,rest,ep,hi,_,hl,hc⟩ := pass_trace_certificate st lk j hj h
    rw [ep] at hc hl
    exact ⟨i,hi,chain_reaches rest hc hl⟩
  · rintro ⟨i,⟨a,ha,hL⟩,path⟩
    have start := hinit i a ha hL
    clear hj
    induction path with
    | refl => exact start
    | tail path e ih => exact hclosed _ _ ih e
