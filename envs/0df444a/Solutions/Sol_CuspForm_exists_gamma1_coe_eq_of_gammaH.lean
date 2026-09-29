-- Prove2me | solution 1 for CuspForm.exists_gamma1_coe_eq_of_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/42cc0eab-ea90-53e8-8d23-76a34c8722d9

import Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_coe_eq_of_gammaH

set_option autoImplicit false

open scoped MatrixGroups

private theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA.2.2
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA.2.1, Units.val_one]
  rw [this]; exact one_mem H

private theorem Gamma_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := CongruenceSubgroup.Gamma_mem.mp hA
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 M) k, (⇑g : UpperHalfPlane → ℂ) = ⇑f := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_GammaH' M H)
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_GammaH M H)
  refine ⟨{ toFun := ⇑f
            slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
            holo' := CuspFormClass.holo f
            zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f
              ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
                ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)) }, rfl⟩

end S_CuspForm_exists_gamma1_coe_eq_of_gammaH
end P2MW
export P2MW.S_CuspForm_exists_gamma1_coe_eq_of_gammaH (solution)
