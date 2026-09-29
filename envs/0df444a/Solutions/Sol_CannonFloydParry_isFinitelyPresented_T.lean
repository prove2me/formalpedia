-- Prove2me | solution 1 for CannonFloydParry.isFinitelyPresented_T
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T09:36:03.895223+00:00
-- url     : https://prove2.me/submissions/93f38b17-0eae-423b-907e-c3abfcfab405

import Definitions.Def_CannonFloydParry_T
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_T1_T
import Mathlib

/-! `T` is finitely presented: `T₁ ≅ T` (CFP Corollary 5.9), and `T₁` is presented by three
generators and six relators. -/

namespace CannonFloydParry

instance : Fintype FormalABC :=
  ⟨{FormalABC.A, FormalABC.B, FormalABC.C}, fun x => by cases x <;> simp⟩

end CannonFloydParry

open CannonFloydParry in
theorem solution : Group.IsFinitelyPresented T := by
  obtain ⟨e, -⟩ := exists_mulEquiv_T1_T
  have : Finite relsT1 := Set.Finite.to_subtype (by simp [relsT1])
  exact Group.IsFinitelyPresented.equiv e
