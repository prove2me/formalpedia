-- Prove2me | solution 1 for CuspForm.exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0891139d-6c7f-5769-8d81-3939fefe8683

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace BddDenomH

open CohCarrier

theorem Gamma1_le_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨ha, hd, hc⟩ := hA
  rw [mem_GammaH_iff]
  refine ⟨CongruenceSubgroup.Gamma0_mem.mpr hc, ?_⟩
  have : gamma0Units M ⟨A, CongruenceSubgroup.Gamma0_mem.mpr hc⟩ = 1 := by
    ext
    rw [val_gamma0Units, Units.val_one]
    exact hd
  rw [this]
  exact one_mem H

noncomputable def restrict (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (GammaH M H) k) :
    ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := f
  slash_action_eq' γ hγ := by
    refine f.slash_action_eq' γ ?_
    obtain ⟨g, hg, rfl⟩ := hγ
    exact ⟨g, Gamma1_le_GammaH M H hg, rfl⟩
  holo' := f.holo'
  bdd_at_cusps' hc := fun g hg =>
    UpperHalfPlane.IsZeroAtImInfty.isBoundedAtImInfty
      (f.zero_at_cusps' (IsCusp.mono (Subgroup.map_mono (Gamma1_le_GammaH M H)) hc) g hg)

theorem coe_restrict (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (GammaH M H) k) :
    (⇑(restrict M H k f) : UpperHalfPlane → ℂ) = ⇑f := rfl

theorem one_mem_strictPeriods (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

open ModularFormClass in
theorem qCoeff_coe_add {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f g : CuspForm (GammaH M H) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M H) f g, map_add]

open ModularFormClass in
theorem qCoeff_coe_neg {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f : CuspForm (GammaH M H) k) (n : ℕ) :
    qCoeff (⇑(-f)) n = -qCoeff (⇑f) n := by
  unfold qCoeff
  rw [CuspForm.coe_neg, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods M H) f, map_neg]

open ModularFormClass in
theorem qCoeff_zero (n : ℕ) : qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  simp [qCoeff, UpperHalfPlane.qExpansion_zero]

open ModularFormClass in
theorem qCoeff_coe_nsmul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (m : ℕ) (f : CuspForm (GammaH M H) k) (n : ℕ) :
    qCoeff (⇑(m • f)) n = (m : ℂ) * qCoeff (⇑f) n := by
  induction m with
  | zero => rw [zero_smul, CuspForm.coe_zero, qCoeff_zero, Nat.cast_zero, zero_mul]
  | succ m ih => rw [add_smul, one_smul, qCoeff_coe_add, ih, Nat.cast_succ]; ring

open ModularFormClass in
theorem qCoeff_coe_zsmul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (m : ℤ) (f : CuspForm (GammaH M H) k) (n : ℕ) :
    qCoeff (⇑(m • f)) n = (m : ℂ) * qCoeff (⇑f) n := by
  rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
  · rw [natCast_zsmul, qCoeff_coe_nsmul, Int.cast_natCast]
  · rw [neg_smul, natCast_zsmul, qCoeff_coe_neg, qCoeff_coe_nsmul, Int.cast_neg, Int.cast_natCast]; ring

end BddDenomH

open BddDenomH ModularFormClass in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n ∈ (algebraMap ℚ ℂ).range) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, (D : ℂ) * ModularFormClass.qCoeff (⇑f) n ∈ (⊥ : Subring ℂ) := by

  have hrat : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (restrict M H k f)).coeff n = (r : ℂ) := by
    intro n
    obtain ⟨r, hr⟩ := hf n
    refine ⟨r, ?_⟩
    rw [coe_restrict, show ((r : ℚ) : ℂ) = algebraMap ℚ ℂ r from rfl, hr]
    rfl
  obtain ⟨D, P, hD, hP⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M (restrict M H k f) hrat
  refine ⟨D.natAbs, Int.natAbs_ne_zero.mpr hD, fun n => ?_⟩

  have hfun : ((D : ℂ) • (⇑(restrict M H k f) : UpperHalfPlane → ℂ)) = ⇑(D • f) := by
    rw [coe_restrict, CuspForm.coe_smul]
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
  have hc : ((PowerSeries.coeff n P : ℤ) : ℂ) = qCoeff (⇑(D • f)) n := by
    rw [hP.coeff n, hfun]; rfl
  rw [qCoeff_coe_zsmul] at hc

  rcases Int.natAbs_eq D with h | h
  · have e : ((D.natAbs : ℕ) : ℂ) = (D : ℂ) := by rw [← Int.cast_natCast, ← h]
    rw [e, ← hc]
    exact Subring.mem_bot.mpr ⟨_, rfl⟩
  · have e : ((D.natAbs : ℕ) : ℂ) = -(D : ℂ) := by
      rw [← Int.cast_natCast, ← Int.cast_neg]
      congr 1
      omega
    rw [e, neg_mul, ← hc, ← Int.cast_neg]
    exact Subring.mem_bot.mpr ⟨_, rfl⟩

end S_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
end P2MW
export P2MW.S_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range (solution)
