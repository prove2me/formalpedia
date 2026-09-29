-- Prove2me | solution 1 for CuspForm.exists_gamma1_coe_eq_alSlash_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/001a4053-218d-53f3-9b54-667353656fbb

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped MatrixGroups ModularForm

namespace AlModBlr

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext; rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11
  rw [this]; exact one_mem H

def restrictCusp {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (F : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm (CongruenceSubgroup.Gamma1 M) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_mono (gamma1_le_gammaH M H) hA)
  holo' := CuspFormClass.holo F
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps F (hc.mono (Subgroup.map_mono (gamma1_le_gammaH M H)))

@[scoped simp] theorem coe_restrictCusp {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (F : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(restrictCusp F) : UpperHalfPlane → ℂ) = ⇑F := rfl

end AlModBlr
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH.AlModBlr"

open AlModBlr in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) 2, (⇑g : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) := by
  obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_coe_eq_alSlash M (M / p) Wd (restrictCusp (CuspForm.diamondLinH 2 e f))
  exact ⟨g, by rw [hg, coe_restrictCusp]⟩

end S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH
end P2MW
export P2MW.S_CuspForm_exists_gamma1_coe_eq_alSlash_diamondLinH (solution)
