-- Prove2me | solution 1 for FixedMachinePrec.theorem_5_9
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:12.727647+00:00
-- url     : https://prove2.me/submissions/9ec85c53-9c3b-40e5-8538-112eca58e280

import Theorems.Thm_FixedMachinePrec_accepted_gaps_accept_parent

open FixedMachinePrec

private theorem empty_row {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F) : evaluateFamily prec m F C ∅ = some [] := by
  unfold evaluateFamily
  generalize listByCardCode F = rows
  suffices h : ∀ tab : Table N, tab ∅ = some [] →
      (rows.foldl (fun tab W => if W = ∅ ∨ ¬ m ∣ W.card then tab else processParent prec m F C tab W) tab) ∅ = some [] by
    apply h; simp [h0]
  induction rows with
  | nil => exact fun _ h => h
  | cons W rows ih =>
    intro tab htab
    simp only [List.foldl_cons]
    apply ih
    split
    · exact htab
    · rename_i h
      have hn : (∅ : Finset (Fin N)) ≠ W := Ne.symm (fun e => h (Or.inl e))
      unfold processParent
      dsimp only
      generalize List.find? _ _ = o
      cases o <;> simp [Function.update_of_ne hn, htab]

theorem solution {N : ℕ} (m : ℕ) (hm : 1 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (F Fcut : Finset (Finset (Fin N))) (hF0 : ∅ ∈ F)
    (hFJ : Finset.univ ∈ F) :
    (∀ W : Finset (Fin N), Described prec m F Fcut W →
      (evaluateFamily prec m F Fcut W).isSome = true) ∧
    (Described prec m F Fcut Finset.univ →
      (evaluateFamily prec m F Fcut Finset.univ).isSome = true) := by
  have hempty := empty_row m prec F Fcut hF0
  suffices h : ∀ W, Described prec m F Fcut W → (evaluateFamily prec m F Fcut W).isSome = true by
    exact ⟨h, h Finset.univ⟩
  intro W hw
  induction hw with
  | empty => simp [hempty]
  | node W hw hn S hs marks hk hi hr hc _ ih =>
    apply accepted_gaps_accept_parent m prec hm hprec F Fcut hF0 W hw hn S hs marks hk hi hr hc
    intro A ha
    by_cases he : A = ∅
    · subst A; simp [hempty]
    · exact ih A ha (Finset.nonempty_iff_ne_empty.mpr he)
