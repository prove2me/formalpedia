-- Prove2me | solution 1 for Formalism.LT.PadicP.lubinTateExample_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:53.175607+00:00
-- url     : https://prove2.me/submissions/d2c7640a-9704-4ae2-a779-dbbb2e9ae770

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_frobLiftPadic
import Theorems.Thm_Formalism_LT_PadicP_funEqPadic_of
import Theorems.Thm_Formalism_LT_PadicP_isHom_of_subst_eq_smul
import Theorems.Thm_Formalism_LT_PadicP_constantCoeff_ltLog
import Theorems.Thm_Formalism_LT_PadicP_coeff_one_ltLog
import Theorems.Thm_Formalism_LT_PadicP_ltLog_funEq
import Theorems.Thm_Formalism_LT_PadicP_ltLog_subst_X_pow
import Theorems.Thm_Formalism_LT_PadicP_coeff_one_subst
import Theorems.Thm_Formalism_LT_PadicP_map_coe_injective_mv
import Theorems.Thm_Formalism_G_LogP_hs2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution (hfg : FunEqFormalGroup.{0}) (hh : FunEqHom.{0})
    (hc : FunEqCongr.{0}) : LubinTateExample := by
  intro p hp
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hset := frobLiftPadic p
  have hmapid : ∀ g : PowerSeries ℚ_[p], PowerSeries.map (RingHom.id ℚ_[p]) g = g := fun g => by
    simp
  have hX_int : IntegralPS (X : PowerSeries ℚ_[p]) := fun n => by
    rw [coeff_X]; split_ifs <;> simp
  have hXp_int : IntegralPS ((X : PowerSeries ℚ_[p]) ^ p) := fun n => by
    rw [coeff_X_pow]; split_ifs <;> simp
  have hpn : ‖(p : ℚ_[p])‖ ≤ 1 := hset.2.2.1.le
  have hfe : IsFunEqType p p (RingHom.id ℚ_[p]) (ltLog p) := by
    unfold IsFunEqType; rw [hmapid, ltLog_funEq]; exact hX_int
  have hge : IsFunEqType p p (RingHom.id ℚ_[p]) ((p : ℚ_[p]) • ltLog p) := by
    unfold IsFunEqType
    rw [hmapid, PowerSeries.subst_smul (HasSubst.X_pow hp0), smul_comm ((p : ℚ_[p])⁻¹) (p : ℚ_[p]),
      ← smul_sub, ltLog_funEq]
    intro n
    rw [map_smul, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hpn (norm_nonneg _) (hX_int n)
  obtain ⟨F, hF⟩ := funEqPadic_of hfg p (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
  obtain ⟨eK, heK0, heKi, heK⟩ := hh ℚ_[p] p p (RingHom.id _) hset (ltLog p)
    ((p : ℚ_[p]) • ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
    (by rw [← coeff_zero_eq_constantCoeff_apply, map_smul, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ltLog, smul_zero]) hge
  let e : PowerSeries ℤ_[p] := PowerSeries.mk fun n => ⟨coeff n eK, heKi n⟩
  have hce : ∀ n, ((coeff n e : ℤ_[p]) : ℚ_[p]) = coeff n eK := fun n => by
    have := PowerSeries.coeff_mk (R := ℤ_[p]) n (fun n => (⟨coeff n eK, heKi n⟩ : ℤ_[p]))
    exact congrArg Subtype.val this
  have hemap : PowerSeries.map PadicInt.Coe.ringHom e = eK := by
    ext n; rw [coeff_map]; exact hce n
  refine ⟨F, hF, e, ?_, ?_, ?_⟩
  · obtain ⟨_, hK⟩ := isHom_of_subst_eq_smul (F.map PadicInt.Coe.ringHom) (ltLog p) eK (p : ℚ_[p])
      hF heK0 heK
    have he0 : constantCoeff e = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      apply PadicInt.ext
      rw [hce, coeff_zero_eq_constantCoeff_apply, heK0]; rfl
    refine ⟨he0, ?_⟩
    have hFS : PowerSeries.HasSubst F.toPowerSeries :=
      PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    have hcc : ∀ t : Fin 2, MvPowerSeries.constantCoeff
        (e.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) ℤ_[p])) = 0 := fun t =>
      PowerSeries.constantCoeff_subst_eq_zero (by simp) e he0
    have hv : MvPowerSeries.HasSubst ![atX e, atY e] := LogP.hs2 (hcc 0) (hcc 1)
    apply map_coe_injective_mv
    rw [PowerSeries.map_subst hFS, hemap, MvPowerSeries.map_subst hv]
    have hfun : (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (![atX e, atY e] i)) =
        ![atX eK, atY eK] := by
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, atX]
        rw [PowerSeries.map_subst (HasSubst.X 0), hemap, MvPowerSeries.map_X]
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, atY]
        rw [PowerSeries.map_subst (HasSubst.X 1), hemap, MvPowerSeries.map_X]
    rw [hfun]
    exact hK
  · apply PadicInt.ext
    have h1 := congrArg (coeff 1) heK
    rw [coeff_one_subst _ _ constantCoeff_ltLog heK0, coeff_one_ltLog, one_mul, map_smul,
      coeff_one_ltLog, smul_eq_mul, mul_one] at h1
    rw [hce, h1]; rfl
  · intro n
    have hd := (hc ℚ_[p] p p (RingHom.id _) hset (ltLog p) constantCoeff_ltLog coeff_one_ltLog hfe
      eK (X ^ p) heK0 (by simp [hp0]) heKi hXp_int 1 le_rfl).mpr (by
        rw [pow_one, heK, ltLog_subst_X_pow, ← smul_sub, sub_sub_cancel]
        intro n
        rw [map_smul, smul_eq_mul, norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hX_int n)) n
    rw [pow_one] at hd
    have hm : PowerSeries.map PadicInt.Coe.ringHom (e - X ^ p) = eK - X ^ p := by
      rw [map_sub, map_pow, map_X, hemap]
    have hcn : ((coeff n (e - X ^ p) : ℤ_[p]) : ℚ_[p]) = coeff n (eK - X ^ p) := by
      rw [← hm, coeff_map]; rfl
    apply (PadicInt.norm_lt_one_iff_dvd _).mp
    rw [PadicInt.norm_def, hcn]
    exact lt_of_le_of_lt hd hset.2.2.1
end Formalism.LT.PadicP
