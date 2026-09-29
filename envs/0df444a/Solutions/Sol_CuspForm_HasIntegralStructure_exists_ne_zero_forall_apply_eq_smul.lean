-- Prove2me | solution 1 for CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/73c14420-6b46-5cfa-9478-0b2858da9211

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_linearIndependent_of_mem_intLattice
import Theorems.Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul

noncomputable section

open ModularForm ModularFormClass

p2m_open "CuspForm ModularForm.CuspForm"

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ} (χ : CuspForm.heckeAlgebra N k S →+* ℂ) : ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧ ∀ t : CuspForm.heckeAlgebra N k S, (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f := by
  have h := Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom (K := ℂ)
    (heckeAlgebra N k S).val.toRingHom (intLattice N k) (CuspForm.intLattice_fg N k)
    (fun t f hf => CuspForm.mem_intLattice_of_mem_heckeAlgebra hk t.2 hf)
    (fun t ht => Subtype.ext (CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hN (t : Module.End ℂ _) ht))
    (fun n f hf hind => CuspForm.linearIndependent_of_mem_intLattice n f hf hind) χ
  exact h

end

end S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul
end P2MW
export P2MW.S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul (solution)
