-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:36:20.861022+00:00
-- url     : https://prove2.me/submissions/56a459fd-d219-48f4-bc1c-dcdadb45a6f0

import Theorems.Thm_DirKECC1549_Main_unit_flow_augment_or_cut
import Theorems.Thm_DirKECC1549_Main_unit_flow_cut_bound
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) :
    ∃ q : ℕ, IsGreatest {q : ℕ | ∃ F : Finset (Fin m), IsUnitFlow D F u v q} q ∧
      IsLeast ((fun S ↦ outCount D S) '' {S : Finset (Fin n) | IsCut S u v}) q := by
  classical
  let vals : Set ℕ := {q | ∃ F : Finset (Fin m), IsUnitFlow D F u v q}
  have hcut : IsCut ({u} : Finset (Fin n)) u v := by simp [IsCut, huv.symm]
  have hbound : ∀ q ∈ vals, q ≤ outCount D {u} := by
    rintro q ⟨F, hF⟩
    exact unit_flow_cut_bound D u v q F hF {u} hcut
  have hfinite : vals.Finite := (Set.finite_le_nat _).subset (by
    intro q hq
    exact hbound q hq)
  have hne : vals.Nonempty := by
    refine ⟨0, ∅, ?_⟩
    simp [IsUnitFlow]
  let q := sSup vals
  have hq : q ∈ vals := hne.csSup_mem hfinite
  have hgreat : IsGreatest vals q := by
    refine ⟨hq, ?_⟩
    intro r hr
    exact le_csSup hfinite.bddAbove hr
  obtain ⟨F, hF⟩ := hq
  rcases unit_flow_augment_or_cut D u v huv q F hF with haug | hcut'
  · obtain ⟨F', hF'⟩ := haug
    have hh : q + 1 ≤ q := hgreat.2 ⟨F', hF'⟩
    omega
  · obtain ⟨S, hS, hEq⟩ := hcut'
    refine ⟨q, hgreat, ?_⟩
    refine ⟨⟨S, hS, hEq⟩, ?_⟩
    rintro r ⟨T, hT, rfl⟩
    exact unit_flow_cut_bound D u v q F hF T hT
