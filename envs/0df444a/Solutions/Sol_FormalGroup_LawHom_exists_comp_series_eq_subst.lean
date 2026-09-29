-- Prove2me | solution 1 for FormalGroup.LawHom.exists_comp_series_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6a76cf4d-e2db-5b29-bfb7-04e2622814e3

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_exists_comp_series_eq_subst

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    {R : Type u} [CommRing R] {F G H : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (η : FormalGroup.LawHom G H) :
    ∃ κ : FormalGroup.LawHom F H, κ.series = PowerSeries.subst θ.series η.series ∧
      PowerSeries.coeff 1 κ.series = PowerSeries.coeff 1 η.series * PowerSeries.coeff 1 θ.series := by
  have hθ0 : PowerSeries.constantCoeff θ.series = 0 := θ.constantCoeff_series
  have hη0 : PowerSeries.constantCoeff η.series = 0 := η.constantCoeff_series
  have hsθ : PowerSeries.HasSubst θ.series := PowerSeries.HasSubst.of_constantCoeff_zero' hθ0
  have hsF : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hsG : PowerSeries.HasSubst G.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff

  have hvec : ∀ φ : PowerSeries R,
      (![LawHom.substX 0 φ, LawHom.substX 1 φ] : Fin 2 → MvPowerSeries (Fin 2) R) = fun s => LawHom.substX s φ := by
    intro φ; funext s; fin_cases s <;> rfl
  have hcX : ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      ∀ s : Fin 2, MvPowerSeries.constantCoeff (LawHom.substX s φ) = 0 :=
    fun φ hφ s => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ hφ
  have hXθ : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s θ.series) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hθ0)
  have hXη : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s η.series) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hη0)
  have hGc : MvPowerSeries.HasSubst (fun _ : Unit => G.toPowerSeries) := hsG.const
  have hXs : ∀ s : Fin 2, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X s : MvPowerSeries (Fin 2) R)) :=
    fun s => (PowerSeries.HasSubst.X s).const

  have hθc := θ.comm
  have hηc := η.comm
  rw [hvec] at hθc hηc

  have key : ∀ s : Fin 2,
      MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t θ.series) (LawHom.substX s η.series) =
        LawHom.substX s (PowerSeries.subst θ.series η.series) := by
    intro s
    rw [show LawHom.substX s (PowerSeries.subst θ.series η.series) =
          PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) (PowerSeries.subst θ.series η.series) from rfl,
      show LawHom.substX s η.series =
          PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) η.series from rfl,
      PowerSeries.subst_comp_subst_apply hsθ (PowerSeries.HasSubst.X s),
      PowerSeries.subst_def (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) η.series,
      MvPowerSeries.subst_comp_subst_apply (hXs s) hXθ, MvPowerSeries.subst_X hXθ s]
    rfl
  refine ⟨⟨PowerSeries.subst θ.series η.series, ?_, ?_⟩, rfl, ?_⟩
  ·
    exact PowerSeries.constantCoeff_subst_eq_zero hθ0 _ hη0
  ·
    rw [hvec, PowerSeries.subst_comp_subst_apply hsθ hsF, hθc,
      PowerSeries.subst_def (MvPowerSeries.subst _ G.toPowerSeries) η.series]
    have e := congrArg (MvPowerSeries.subst (fun s : Fin 2 => LawHom.substX s θ.series)) hηc
    rw [PowerSeries.subst_def G.toPowerSeries η.series, MvPowerSeries.subst_comp_subst_apply hGc hXθ,
      MvPowerSeries.subst_comp_subst_apply hXη hXθ] at e
    rw [e]
    congr 1
    funext s
    exact key s
  ·
    rw [PowerSeries.coeff_subst' hsθ, finsum_eq_single _ 1]
    · rw [pow_one, smul_eq_mul]
    · intro d hd
      rcases Nat.lt_or_gt_of_ne hd with h | h
      · have h0 : d = 0 := by omega
        subst h0
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hη0, zero_smul]
      · obtain ⟨t, ht⟩ := PowerSeries.X_dvd_iff.mpr hθ0
        rw [ht, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), smul_zero]

end S_FormalGroup_LawHom_exists_comp_series_eq_subst
end P2MW
export P2MW.S_FormalGroup_LawHom_exists_comp_series_eq_subst (solution)
