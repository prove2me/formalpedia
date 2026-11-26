-- Prove2me | solution 1 for FixedMachinePrec.accepted_gaps_accept_parent
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:00:16.045638+00:00
-- url     : https://prove2.me/submissions/4d6cb074-249f-42d9-ad69-d7b9dcc4debe

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy
import Theorems.Thm_FixedMachinePrec_evaluate_marked_row_order
import Theorems.Thm_FixedMachinePrec_marked_slots_state_path
import Theorems.Thm_FixedMachinePrec_lemma_5_5

open FixedMachinePrec


theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
    (hg : ∀ A ∈ gaps S marks, (evaluateFamily prec m F C A).isSome = true) :
    (evaluateFamily prec m F C W).isSome = true := by
  apply evaluate_marked_row_order m prec hm hp F C h0 W hw hne S hs marks hk hi hr hc hg
  intro tab hgap
  let st := buildStates prec m C W
  let lk := fun X => (lookup F tab X).isSome
  obtain ⟨i,t,a,b,ha,hb,hL,hR,hpath⟩ := marked_slots_state_path m prec hm hp F C h0 W hw hne S hs marks hk hi hr hc tab hgap
  change st[t]? = some b at hb
  have ht : t < st.length := by by_contra! h; simp [List.getElem?_eq_none h] at hb
  have hm' := ((lemma_5_5 m hm prec hp C W lk).1 t ht).mpr ⟨i,⟨a,ha,hL⟩,hpath⟩
  let test (j : ℕ) := (reachPass st lk).1 j && match st[j]? with | some a => lk a.R | none => false
  have ok : test t = true := by unfold test; rw [hb]; exact Bool.and_eq_true_iff.mpr ⟨hm',hR⟩
  obtain ⟨j,hit⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨t,List.mem_range.mpr ht,ok⟩)
  unfold processParent
  change ((match (List.range st.length).find? test with | none => tab | some v => Function.update tab W (some _)) W).isSome = true
  rw [hit]; simp
