-- Prove2me | solution 1 for FixedMachinePrec.theorem_5_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:24:12.753865+00:00
-- url     : https://prove2.me/submissions/e8022c69-d37d-4fe6-aaea-5f16d6584c17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FixedMachinePrec_bounded_gap_witness_family

open FixedMachinePrec


theorem solution {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (rank : Fin N → ℕ) (hrank : IsTopoRank prec rank)
    (hfeas : ∃ S : List (Finset (Fin N)), IsFullSchedule prec m Finset.univ S) :
    Described prec m (family prec rank m (4 * m + 5)) (family prec rank m (m + 3)) Finset.univ := by
  obtain ⟨D,hroot,hrepr,hsplit⟩ := bounded_gap_witness_family m prec hm hprec rank hrank hfeas
  suffices h : ∀ n (W : Finset (Fin N)), W.card = n → W ∈ D →
      Described prec m (family prec rank m (4*m+5)) (family prec rank m (m+3)) W by
    exact h _ _ rfl hroot
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W hn hW
    by_cases he : W = ∅
    · subst W
      exact .empty (hrepr hW)
    · have hne := Finset.nonempty_iff_ne_empty.mpr he
      obtain ⟨S,marks,hS,hk,hi,hr,hc,hg⟩ := hsplit W hW hne
      apply Described.node W (hrepr hW) hne S hS marks hk hi hr hc
      intro A hA hneA
      obtain ⟨hmem,hlt⟩ := hg A hA hneA
      exact ih A.card (hn ▸ hlt) A rfl hmem
