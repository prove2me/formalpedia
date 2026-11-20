-- Prove2me | solution 1 for DeletionCode.SingleEditScripts.within_one_realized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:56.643676+00:00
-- url     : https://prove2.me/submissions/b059cd97-5250-4076-ba70-31afe043d475

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts
import Theorems.Thm_DeletionCode_EditAlignment_Script_classify_of_le_one
import Theorems.Thm_DeletionCode_SingleEditScripts_delete_split
import Theorems.Thm_DeletionCode_SingleEditScripts_insert_split

set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditScripts
open Windows CatalogueWords EditAlignment SingleEditOrigins
namespace DeletionCode.SingleEditScripts
theorem _root_.solution {x y : List Bool} (h : WithinEdits 1 x y) :
    ∃ e : Edit, e.Valid x.length ∧ e.outputLength x.length = y.length ∧
      e.word (listLetters x) = listLetters y := by
  obtain ⟨d, i, hscript, hcost⟩ := h
  rcases hscript.classify_of_le_one hcost with hsame | hdelete | hinsert
  · subst y
    exact ⟨.unchanged, trivial, rfl, rfl⟩
  · obtain ⟨pre, suffix, bit, rfl, rfl⟩ := hdelete
    refine ⟨.delete pre.length, ?_, ?_, ?_⟩
    · simp only [Edit.Valid, List.length_append, List.length_cons]
      omega
    · simp only [Edit.outputLength, List.length_append, List.length_cons]
      omega
    · exact delete_split pre suffix bit
  · obtain ⟨pre, suffix, bit, rfl, rfl⟩ := hinsert
    refine ⟨.insert pre.length bit, ?_, ?_, ?_⟩
    · simp only [Edit.Valid, List.length_append]
      omega
    · simp only [Edit.outputLength, List.length_append, List.length_cons]
      omega
    · exact insert_split pre suffix bit
end DeletionCode.SingleEditScripts
