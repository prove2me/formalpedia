-- Prove2me | solution 1 for DirKECC1549.Main.sec2_maxflow_mincut
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:25:03.787758+00:00
-- url     : https://prove2.me/submissions/e194eed6-3e3f-467d-a24e-209f9c351192

import Theorems.Thm_DirKECC1549_Main_unit_flow_decomposition
import Theorems.Thm_DirKECC1549_Main_unit_flow_min_cut
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n) (u v : Fin n) (huv : u ≠ v) :
    IsGreatest {q : ℕ | ∃ F : Finset (Fin m), IsUnitFlow D F u v q} (lam D u v) ∧
    IsLeast ((fun S ↦ outCount D S) '' {S : Finset (Fin n) | IsCut S u v}) (lam D u v) := by
  obtain ⟨q, hmax, hmin⟩ := unit_flow_min_cut D u v huv
  have hq : HasDisjointPaths D q u v := (unit_flow_decomposition D u v huv q).mpr hmax.1
  have hbound : BddAbove {r : ℕ | HasDisjointPaths D r u v} := by
    refine ⟨q, ?_⟩
    intro r hr
    exact hmax.2 ((unit_flow_decomposition D u v huv r).mp hr)
  have heq : lam D u v = q := by
    apply le_antisymm
    · apply csSup_le ⟨q, hq⟩
      intro r hr
      exact hmax.2 ((unit_flow_decomposition D u v huv r).mp hr)
    · exact le_csSup hbound hq
  rw [heq]
  exact ⟨hmax, hmin⟩
