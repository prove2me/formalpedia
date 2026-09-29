-- Prove2me | solution 1 for CuspForm.heckeULinH_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b0ea0785-b62c-5874-abb2-ae0958b6289b

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeULinH_comm

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped MatrixGroups ModularForm
open ModularFormClass

namespace COMMq

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
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

theorem one_mem_strictPeriods_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := by
    apply Gamma1_le_GammaH
    simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_def (f : UpperHalfPlane → ℂ) (n : ℕ) :
    qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n := rfl

theorem eq_of_forall_qCoeff_eq {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {k : ℤ}
    (F G : CuspForm Γ k) (h : ∀ n : ℕ, qCoeff F n = qCoeff G n) : F = G := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h1 : UpperHalfPlane.qExpansion 1 (⇑(F - G)) = 0 := by
    rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ F G]
    ext n
    have := h n
    rw [qCoeff_def, qCoeff_def] at this
    simp [this]
  have h2 : (⇑(F - G) : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (F - G) hΓ) (ModularFormClass.holo (F - G))
      (ModularFormClass.bdd_at_infty (F - G))).mp h1
  have h3 : F - G = 0 := DFunLike.ext' (by rw [h2]; rfl)
  exact sub_eq_zero.mp h3

theorem qCoeff_heckeULinH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ} (hq : q.Prime)
    (hqM : q ∣ M) (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    qCoeff (CuspForm.heckeULinH k q f) n = qCoeff f (n * q) := by
  have : qCoeff (⇑(CuspForm.heckeULinH k q f)) n = qCoeff (ModularForm.heckeU k q ⇑f) n := by
    rw [CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f]
  rw [this, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_GammaH M H) hq.ne_zero n,
    ModularForm.coeffHeckeU_apply]

end COMMq

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.heckeULinH k q (CuspForm.heckeULinH k q' f) = CuspForm.heckeULinH k q' (CuspForm.heckeULinH k q f) := by
  apply COMMq.eq_of_forall_qCoeff_eq (COMMq.one_mem_strictPeriods_GammaH M H)
  intro n
  rw [COMMq.qCoeff_heckeULinH M H k hq hqM, COMMq.qCoeff_heckeULinH M H k hq' hq'M,
    COMMq.qCoeff_heckeULinH M H k hq' hq'M, COMMq.qCoeff_heckeULinH M H k hq hqM, mul_right_comm]

end S_CuspForm_heckeULinH_comm
end P2MW
export P2MW.S_CuspForm_heckeULinH_comm (solution)
