-- Prove2me | solution 1 for Freiman.middle_initial_chain_assembly
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:49:43.518796+00:00
-- url     : https://prove2.me/submissions/5f204975-4c7f-4288-b3da-89cd8517101c

import Definitions.Def_Freiman_middleRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.GetD
open Freiman
set_option autoImplicit false
theorem solution :
    (∀ i : Fin 15, middleRootCertificate i) →
    (∀ (i : ℕ) (hi : i<7), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty) →
    (∀ (i : ℕ) (hlo : 7 ≤ i) (hi : i<14), (middleCover (middleRoot ⟨i,by omega⟩) ∩ middleCover (middleRoot ⟨i+1,by omega⟩)).Nonempty) →
    (middleBounds (middleRoot 14)).1 < Real.sqrt 21 → (128/25:ℝ)<(middleBounds (middleRoot 0)).2 →
    (∀ (cs : List MiddleCore) (l u : ℝ), middleContacts cs → (∃ d ∈ cs, (middleBounds d).1 ≤ l) → (∃ d ∈ cs, u ≤ (middleBounds d).2) → Set.Icc l u ⊆ middleUnion cs) →
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ i : Fin 15, t∈middleCover (middleRoot i) := by
  intro hr hl hu hlow hupp hchain t ht
  have hm (i : Fin 15) : middleRoot i ∈ middleRootList := by
    unfold middleRoot
    rw [List.getD_eq_getElem _ _ (show i.val < middleRootList.length from i.isLt)]
    exact List.getElem_mem _
  have hx (d : MiddleCore) (hd : d ∈ middleRootList) : ∃ i : Fin 15, middleRoot i = d := by
    obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp hd
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [middleRoot, List.getD_eq_getElem _ _ hi, hd]
  have hne (i : Fin 15) : (middleCover (middleRoot i)).Nonempty := by
    refine ⟨middleInnerLeft i, (hr i).2.2.1.le, ?_⟩
    apply le_trans _ (hr i).2.2.2.le
    fin_cases i <;> norm_num [middleInnerLeft, middleInnerRight]
  have hcontacts : middleContacts middleRootList := by
    constructor
    · intro d hd
      obtain ⟨i, rfl⟩ := hx d hd
      exact hne i
    · intro i hi
      change i + 1 < 15 at hi
      by_cases hh : i < 7
      · exact hl i hh
      · exact hu i (by omega) (by omega)
  have hin := hchain middleRootList (Real.sqrt 21) (128/25:ℝ) hcontacts
    ⟨middleRoot 14, hm 14, hlow.le⟩ ⟨middleRoot 0, hm 0, hupp.le⟩ ht
  obtain ⟨d, hd, htd⟩ := hin
  obtain ⟨i, rfl⟩ := hx d hd
  exact ⟨i, htd⟩
#print axioms solution
