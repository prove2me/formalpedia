-- Prove2me | solution 1 for CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/52b7d04c-267c-570c-a1a0-5683e68a5925

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace CohCarrier p2m_export "CohCarrier" "gamma0Units val_gamma0Units GammaH mem_GammaH_iff" end CohCarrier
p2m_open_scoped "CohCarrier" in

theorem CohCarrier.Gamma1_le_GammaH' (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

p2m_open_scoped "CohCarrier" in

theorem CohCarrier.one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    show (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  have hle : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (CohCarrier.Gamma1_le_GammaH' M H)
  exact hle h1

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeULinH k q f)) n = ModularFormClass.qCoeff (⇑f) (n * q) := by
  rw [CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f,
    ModularFormClass.qCoeff_heckeU f (CohCarrier.one_mem_strictPeriods_GammaH M H) hq.ne_zero n,
    ModularForm.coeffHeckeU_apply]

end S_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul
end P2MW
export P2MW.S_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul (solution)
