-- Prove2me | solution 1 for DetANN.reloc_detProgram
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:43:25.814211+00:00
-- url     : https://prove2.me/submissions/a4ff6ffe-180c-4c96-8283-1cc2f5a8f6a2

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_DataStructure

open PNormReg PNormRegLib DetANN

namespace DetANNRelocAux

lemma mem_reloc {p : RelocParams} {P : Program} {op : Instr} (h : op ∈ reloc p P) :
    ∃ ins ∈ P, op = (p.pair ins).1 ∨ op = (p.pair ins).2 := by
  simp only [reloc, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨ins, hins, h⟩ := h
  exact ⟨ins, hins, h⟩

end DetANNRelocAux

open DetANNRelocAux in
theorem solution (p : PNormRegLib.RelocParams) (P : PNormReg.Program)
    (hP : DetProgram P) : DetProgram (PNormRegLib.reloc p P) := by
  obtain ⟨hadm, hno⟩ := hP
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩
  · obtain ⟨ins, hins, hop'⟩ := mem_reloc hop
    have h1 := hadm ins hins
    cases ins with
    | core i =>
      cases i <;> rcases hop' with rfl | rfl <;>
        simp_all [RelocParams.pair, RelocParams.noop]
    | _ => rcases hop' with rfl | rfl <;> simp_all [RelocParams.pair, RelocParams.noop]
  · obtain ⟨ins, hins, hop'⟩ := mem_reloc hop
    obtain ⟨hc, hr⟩ := hno ins hins
    refine ⟨fun d hd => ?_, fun d a e hd => ?_⟩ <;> subst hd
    all_goals
      cases ins with
      | core i => cases i <;> simp [RelocParams.pair, RelocParams.noop] at hop'
      | coin d' => exact hc d' rfl
      | rpow d' a' e' => exact hr d' a' e' rfl
      | _ => simp [RelocParams.pair, RelocParams.noop] at hop'
