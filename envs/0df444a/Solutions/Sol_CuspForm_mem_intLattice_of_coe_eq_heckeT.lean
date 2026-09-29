-- Prove2me | solution 1 for CuspForm.mem_intLattice_of_coe_eq_heckeT
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4b4721f1-bb05-5a53-b81a-345cb22683ee

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularForm_coeffHeckeT_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_intLattice_of_coe_eq_heckeT

set_option autoImplicit false

noncomputable section

open Complex Function
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm Manifold

open ModularForm ModularFormClass

namespace W3WsD

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => CongruenceSubgroup.Gamma0 N

theorem hΓ (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ₀(N)).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

theorem qCoeff_add (f g : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff, CuspForm.coe_add]
  rw [ModularForm.qExpansion_add one_pos (hΓ N) f g, map_add]

theorem qCoeff_zero' (n : ℕ) : qCoeff ⇑(0 : CuspForm Γ₀(N) k) n = 0 := by
  simp only [qCoeff, CuspForm.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zsmul (c : ℤ) (f : CuspForm Γ₀(N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = (c : ℂ) • ⇑f := by
    ext z
    simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (hΓ N) (c : ℂ) f]
  simp

def intSubmodule (N : ℕ) (k : ℤ) : Submodule ℤ (CuspForm Γ₀(N) k) where
  carrier := {f | ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ)}
  add_mem' {f g} hf hg n := by
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a + b, by rw [qCoeff_add, ha, hb]; push_cast; ring⟩
  zero_mem' n := ⟨0, by rw [qCoeff_zero']; simp⟩
  smul_mem' c {f} hf n := by
    obtain ⟨a, ha⟩ := hf n
    exact ⟨c * a, by rw [qCoeff_zsmul, ha]; push_cast; ring⟩

theorem intLattice_eq (N : ℕ) (k : ℤ) : CuspForm.intLattice N k = intSubmodule N k :=
  Submodule.span_eq (intSubmodule N k)

theorem mem_intLattice_iff (f : CuspForm Γ₀(N) k) :
    f ∈ CuspForm.intLattice N k ↔ ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  rw [intLattice_eq]
  rfl

end W3WsD

theorem solution {N : ℕ} {k : ℤ} (hk : 1 ≤ k) {p : ℕ} (hp : p ≠ 0) {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : ⇑g = ModularForm.heckeT k p ⇑f) (hf : f ∈ CuspForm.intLattice N k) : g ∈ CuspForm.intLattice N k := by
  rw [W3WsD.mem_intLattice_iff] at hf ⊢
  intro n
  obtain ⟨m, hm⟩ := ModularForm.coeffHeckeT_int k hk p hf n
  exact ⟨m, by rw [hg, ModularFormClass.qCoeff_heckeT f (W3WsD.hΓ N) hp n, hm]⟩

end

end S_CuspForm_mem_intLattice_of_coe_eq_heckeT
end P2MW
export P2MW.S_CuspForm_mem_intLattice_of_coe_eq_heckeT (solution)
