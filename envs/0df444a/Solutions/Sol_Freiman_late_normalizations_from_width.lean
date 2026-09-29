-- Prove2me | solution 1 for Freiman.late_normalizations_from_width
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:28:23.770622+00:00
-- url     : https://prove2.me/submissions/ff2beaa0-2ae4-4755-af9b-6a7b7416084f

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic
open Freiman
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
private theorem normalizationComplement (b : CertBound) (r s q : ℝ) :
    certBoundHolds (lowerHistoryComplement b) r s q ↔ ¬ certBoundHolds b r s q := by
  cases hl : b.lower <;> cases hs : b.strict <;>
    simp [certBoundHolds, lowerHistoryComplement, hl, hs]

theorem solution (hw : LowerHistoryWidthLaw) : ∀ (p : LowerPair) (path : LatePath), latePathValid lateCatalog path → lateHolds (lateBounds lateCatalog path.required) (lateR p) (lateS p) (lateQ p) → ∀ n ∈ path.normalizations, lateNormalizationHolds p n := by
  intro p path hv hr n hn
  have hnorm := hv.2.2.2.2.2.2.2.2.2.1 n hn
  have hBound := hr _ (List.mem_map.mpr ⟨n.bound,hnorm.1,rfl⟩)
  have hm := hnorm.2
  simp only [lateNormals,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with he | he
  · have hwide : n.wide=false := congrArg Prod.fst he
    have hbound : lateBound lateCatalog n.bound = ⟨false,false,lowerHistoryWH (lateWords n.label)⟩ := congrArg Prod.snd he
    rw [hbound] at hBound
    have hc : lowerHistoryAtBase (lowerNormalize p) [⟨false,false,lowerHistoryWH (lateWords n.label)⟩] := by
      intro b hb
      have he := List.mem_singleton.mp hb
      subst b
      exact hBound
    have hwidth : lowerWidth (lowerChild p n.label).2 ≤ lowerWidth (lowerChild p n.label).1 :=
      (hw (lowerNormalize p) (lateWords n.label)).1.mpr hc
    change lowerNormalize (lowerChild p n.label) =
      (if n.wide then ((lowerChild p n.label).2,(lowerChild p n.label).1) else lowerChild p n.label)
    rw [hwide]
    exact if_pos hwidth
  · have hwide : n.wide=true := congrArg Prod.fst he
    have hbound : lateBound lateCatalog n.bound = ⟨true,true,lowerHistoryWH (lateWords n.label)⟩ := congrArg Prod.snd he
    rw [hbound] at hBound
    have hnot : ¬ certBoundHolds ⟨false,false,lowerHistoryWH (lateWords n.label)⟩
        (lateR p) (lateS p) (lateQ p) :=
      (normalizationComplement ⟨false,false,lowerHistoryWH (lateWords n.label)⟩ _ _ _).mp hBound
    have hwidth : ¬ lowerWidth (lowerChild p n.label).2 ≤ lowerWidth (lowerChild p n.label).1 := by
      intro hh
      have hc := (hw (lowerNormalize p) (lateWords n.label)).1.mp hh
      exact hnot (hc _ (by simp))
    change lowerNormalize (lowerChild p n.label) =
      (if n.wide then ((lowerChild p n.label).2,(lowerChild p n.label).1) else lowerChild p n.label)
    rw [hwide]
    exact if_neg hwidth
#print axioms solution
