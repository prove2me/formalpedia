-- Prove2me | solution 1 for Freiman.late_mixed_virtual_holding_unique
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T09:58:32.200406+00:00
-- url     : https://prove2.me/submissions/bd63506e-4dc7-4f6e-b707-30942808a314

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

open Freiman
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Freiman

private theorem at_mem {base : LowerPair} {cs : List CertBound} {a : CertBound}
    (h : lowerHistoryAtBase base cs) (ha : a ∈ cs) :
    lowerHistoryAtBase base [a] := fun b hb => by
  simp at hb
  subst b
  exact h a ha

private theorem at_of_cons {base : LowerPair} {a : CertBound} {cs : List CertBound}
    (h : lowerHistoryAtBase base (a :: cs)) :
    lowerHistoryAtBase base cs :=
  fun b hb => h b (List.mem_cons_of_mem a hb)

private theorem at_tail {base : LowerPair} {a b : CertBound}
    (h : lowerHistoryAtBase base [a, b]) : lowerHistoryAtBase base [b] := by
  intro c hc
  simp at hc
  subst c
  exact h b (by simp)

private theorem not_cut_and_complement (base : LowerPair) (c : CertBound) :
    ¬ (lowerHistoryAtBase base [c] ∧
       lowerHistoryAtBase base [lowerHistoryComplement c]) := by
  intro ⟨ha, hb⟩
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, lowerHistoryComplement, certBoundHolds] at ha hb
  cases hL : c.lower <;> cases hS : c.strict <;>
    simp [hL, hS, Bool.not_true, Bool.not_false] at ha hb <;> linarith

private theorem not_both_late_normals (base words : LowerPair) :
    ¬ (lowerHistoryAtBase base [⟨false, false, lowerHistoryWH words⟩] ∧
       lowerHistoryAtBase base [⟨true, true, lowerHistoryWH words⟩]) := by
  intro ⟨hL, hR⟩
  simp only [lowerHistoryAtBase, lowerHistoryConditions, List.mem_singleton,
    forall_eq, certBoundHolds, Bool.false_eq_true, ↓reduceIte] at hL hR
  exact (not_le_of_gt hR hL).elim

private theorem late_normals_decode (w : LowerPair) {wide : Bool} {norm : CertBound}
    (h : (wide, norm) ∈ lateNormals w) :
    (wide = false ∧ norm = ⟨false, false, lowerHistoryWH w⟩) ∨
    (wide = true ∧ norm = ⟨true, true, lowerHistoryWH w⟩) := by
  simpa [lateNormals] using h

private theorem late_equal_holding_unique
    (base : LowerPair) (C : LowerHistoryContext) (words : LowerPair) (upper : Bool)
    {z z' : CertField × CertField} {cs cs' : List CertBound}
    (h : (z, cs) ∈ lateEqualCases C words upper)
    (h' : (z', cs') ∈ lateEqualCases C words upper)
    (hat : lowerHistoryAtBase base cs)
    (hat' : lowerHistoryAtBase base cs') :
    z = z' := by
  by_cases hn : lowerHistoryNatural C words upper false = true ∨
      lowerHistoryNatural C words upper true = true
  · simp [lateEqualCases, hn] at h h'
    exact h.1.trans h'.1.symm
  · simp [lateEqualCases, hn, lateNormals] at h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        ((try rfl) <;>
          (try exact (not_cut_and_complement base _
            ⟨at_tail hat, at_tail hat'⟩).elim) <;>
          (try exact (not_cut_and_complement base _
            ⟨at_tail hat', at_tail hat⟩).elim) <;>
          (try exact (not_both_late_normals base words
            ⟨at_mem hat List.mem_cons_self,
              at_mem hat' List.mem_cons_self⟩).elim) <;>
          (try exact (not_both_late_normals base words
            ⟨at_mem hat' List.mem_cons_self,
              at_mem hat List.mem_cons_self⟩).elim))

private theorem mixed_virtual_mem
    (right3 : Bool) (w : LowerPair) (upper : Bool)
    (hp : lowerHistoryWordParity (lateContext right3) w false ≠
      lowerHistoryWordParity (lateContext right3) w true)
    {z : CertField × CertField} {cs : List CertBound}
    (h : (z, cs) ∈ lateEndpointCases right3 w upper) :
    ∃ wide norm inner,
      (wide, norm) ∈ lateNormals w ∧
      cs = norm :: inner ∧
      ((upper = ! lowerHistoryWordParity (lateContext right3) w wide ∧
          (z, inner) ∈ lateEqualCases (lateContext right3)
            (lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])) upper) ∨
        (upper ≠ ! lowerHistoryWordParity (lateContext right3) w wide ∧
          inner = [] ∧
          z = (lowerHistoryEndVal (lateContext right3) w upper false
                (lowerHistoryNatural (lateContext right3) w upper false),
              lowerHistoryEndVal (lateContext right3) w upper true
                (lowerHistoryNatural (lateContext right3) w upper true)))) := by
  set C := lateContext right3
  unfold lateEndpointCases at h
  rw [if_neg hp] at h
  simp only [List.mem_flatMap] at h
  rcases h with ⟨⟨wide, norm⟩, hnorm, hmap⟩
  simp only [List.mem_map] at hmap
  rcases hmap with ⟨⟨v, inner⟩, hin, hpair⟩
  obtain ⟨rfl, rfl⟩ := hpair
  refine ⟨wide, norm, inner, hnorm, rfl, ?_⟩
  by_cases hif : upper = ! lowerHistoryWordParity C w wide
  · rw [if_pos hif] at hin
    exact Or.inl ⟨hif, hin⟩
  · rw [if_neg hif] at hin
    simp only [List.mem_singleton] at hin
    obtain ⟨rfl, rfl⟩ := hin
    exact Or.inr ⟨hif, rfl, rfl⟩

end Freiman

open Freiman

theorem solution
    (hw : LowerHistoryWidthLaw) (p : LowerPair) (e : LateEndpoint)
    (hm : lateMatches p e.right3)
    (hp : lowerHistoryWordParity (lateContext e.right3) e.words false ≠
      lowerHistoryWordParity (lateContext e.right3) e.words true)
    (hvirt : e.upper = ! lowerHistoryWordParity (lateContext e.right3) e.words
      (decide (¬ lowerWidth ((lowerNormalize p).2 ++ e.words.2) ≤
        lowerWidth ((lowerNormalize p).1 ++ e.words.1))))
    (z z' : CertField × CertField) (cs cs' : List CertBound)
    (h : (z, cs) ∈ lateEndpointCases e.right3 e.words e.upper)
    (h' : (z', cs') ∈ lateEndpointCases e.right3 e.words e.upper)
    (hat : lowerHistoryAtBase (lowerNormalize p) cs)
    (hat' : lowerHistoryAtBase (lowerNormalize p) cs') :
    z = z' := by
  have := hw
  have := hm
  have := hvirt
  obtain ⟨wide, norm, inner, hN, hcs, hcase⟩ :=
    mixed_virtual_mem e.right3 e.words e.upper hp h
  obtain ⟨wide', norm', inner', hN', hcs', hcase'⟩ :=
    mixed_virtual_mem e.right3 e.words e.upper hp h'
  have hatN : lowerHistoryAtBase (lowerNormalize p) [norm] :=
    at_mem hat (hcs.symm ▸ List.mem_cons_self)
  have hatN' : lowerHistoryAtBase (lowerNormalize p) [norm'] :=
    at_mem hat' (hcs'.symm ▸ List.mem_cons_self)
  have hwide : wide = wide' := by
    rcases late_normals_decode e.words hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases late_normals_decode e.words hN' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (not_both_late_normals (lowerNormalize p) e.words
        ⟨hatN, hatN'⟩).elim
    · exact (not_both_late_normals (lowerNormalize p) e.words
        ⟨hatN', hatN⟩).elim
    · rfl
  subst wide'
  rcases hcase with ⟨hvirt_w, heq⟩ | ⟨hnvirt, rfl, hz⟩ <;>
    rcases hcase' with ⟨hvirt_w', heq'⟩ | ⟨hnvirt', rfl, hz'⟩
  · exact late_equal_holding_unique (lowerNormalize p) (lateContext e.right3)
      (lowerHistorySet e.words wide (lowerHistoryPick e.words wide ++ [1]))
      e.upper heq heq'
      (at_of_cons (hcs ▸ hat)) (at_of_cons (hcs' ▸ hat'))
  · exact (hnvirt' hvirt_w).elim
  · exact (hnvirt hvirt_w').elim
  · exact hz.trans hz'.symm
