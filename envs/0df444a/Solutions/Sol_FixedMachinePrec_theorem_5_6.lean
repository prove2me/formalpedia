-- Prove2me | solution 1 for FixedMachinePrec.theorem_5_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:11.939583+00:00
-- url     : https://prove2.me/submissions/3533d7f0-1d95-4cb8-94c4-0fe6fc645a72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FixedMachinePrec_lemma_5_5
import Theorems.Thm_FixedMachinePrec_reconstruct_certified_path

open FixedMachinePrec

private theorem fold_invariant {α β : Type*} (P : β → Prop) (f : β → α → β) (hs : ∀ b a, P b → P (f b a)) (xs : List α) (b : β) (hb : P b) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons _ _ ih => exact ih _ (hs _ _ hb)

theorem solution {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (F Fcut : Finset (Finset (Fin N))) (hF0 : ∅ ∈ F)
    (hFJ : Finset.univ ∈ F) (X : Finset (Fin N)) (S : List (Finset (Fin N)))
    (hX : evaluateFamily prec m F Fcut X = some S) :
    IsFullSchedule prec m X S := by
  let Sound : Table N → Prop := fun tab => ∀ X S, tab X = some S → IsFullSchedule prec m X S
  have step (tab : Table N) (W) (hs : Sound tab) : Sound (processParent prec m F Fcut tab W) := by
    let st := buildStates prec m Fcut W
    let lk := fun X => (lookup F tab X).isSome
    unfold processParent
    dsimp only
    split
    · exact hs
    · rename_i t he
      have ht := List.mem_of_find?_eq_some he
      have htest := List.find?_some he
      have hmark : (reachPass st lk).1 t = true := (Bool.and_eq_true_iff.mp htest).1
      have hlast : ∃ a, st[t]? = some a ∧ lk a.R = true := by
        have hh := (Bool.and_eq_true_iff.mp htest).2
        change (match st[t]? with | some a => lk a.R | none => false) = true at hh
        split at hh <;> simp_all
      have hcert := (lemma_5_5 m hm prec hprec Fcut W lk).2 t (List.mem_range.mp ht) hmark
      obtain ⟨i,rest,ep,hi,_,hl,hc⟩ := hcert
      have good := reconstruct_certified_path m prec hm F Fcut W tab hs (reachPass st lk).2 t hlast ⟨i,rest,ep,hi,hl,hc⟩
      intro Y S' hY
      by_cases e : Y = W
      · subst Y
        simp only [Function.update_self, Option.some.injEq] at hY
        exact hY ▸ good
      · exact hs _ _ (by simpa [Function.update_of_ne e] using hY)
  apply (show Sound (evaluateFamily prec m F Fcut) from ?_) X S hX
  unfold evaluateFamily
  apply fold_invariant Sound
  · intro b a h
    split
    · exact h
    · exact step b a h
  · intro Y R h
    dsimp only at h
    split at h <;> simp_all [IsFullSchedule]
