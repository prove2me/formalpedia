-- Prove2me | solution 1 for FormalGroup.LawIso.exists_symm_subst_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9670e3ee-6f38-5467-ae3c-c1be139e0bc4

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawIso_exists_symm_subst_eq_X

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    {R : Type u} [CommRing R] {F G : FormalGroup R} (ψ : FormalGroup.LawIso F G) :
    ∃ ψ' : FormalGroup.LawIso G F,
      PowerSeries.subst ψ.series ψ'.series = PowerSeries.X ∧
        PowerSeries.subst ψ'.series ψ.series = PowerSeries.X := by

  have hP0 : PowerSeries.constantCoeff ψ.series = 0 := ψ.constantCoeff_series
  have hu : IsUnit (PowerSeries.coeff 1 ψ.series) := ψ.isUnit_coeff_one
  have hQ0 : PowerSeries.constantCoeff (PowerSeries.substInvOfIsUnit ψ.series hu) = 0 :=
    PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hleft : PowerSeries.subst ψ.series (PowerSeries.substInvOfIsUnit ψ.series hu) = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_left ψ.series hP0 hu
  have hright : PowerSeries.subst (PowerSeries.substInvOfIsUnit ψ.series hu) ψ.series = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right ψ.series hP0 hu

  have hsP : PowerSeries.HasSubst ψ.series := PowerSeries.HasSubst.of_constantCoeff_zero' hP0
  have hsQ : PowerSeries.HasSubst (PowerSeries.substInvOfIsUnit ψ.series hu) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  have hsF : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hvec : ∀ φ : PowerSeries R,
      (![LawHom.substX 0 φ, LawHom.substX 1 φ] : Fin 2 → MvPowerSeries (Fin 2) R) = fun s => LawHom.substX s φ := by
    intro φ; funext s; fin_cases s <;> rfl
  have hcX : ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      ∀ s : Fin 2, MvPowerSeries.constantCoeff (LawHom.substX s φ) = 0 :=
    fun φ hφ s => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ hφ
  have hXP : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s ψ.series) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hP0)
  have hXQ : MvPowerSeries.HasSubst (fun s : Fin 2 => LawHom.substX s (PowerSeries.substInvOfIsUnit ψ.series hu)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (hcX _ hQ0)
  have hFc : MvPowerSeries.HasSubst (fun _ : Unit => F.toPowerSeries) := hsF.const
  have hXs : ∀ s : Fin 2, MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X s : MvPowerSeries (Fin 2) R)) :=
    fun s => (PowerSeries.HasSubst.X s).const
  have hMvF : PowerSeries.HasSubst
      (MvPowerSeries.subst (fun s : Fin 2 => LawHom.substX s (PowerSeries.substInvOfIsUnit ψ.series hu)) F.toPowerSeries) :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      (MvPowerSeries.constantCoeff_subst_eq_zero hXQ (hcX _ hQ0) F.zero_constantCoeff)

  have hψc := ψ.comm
  rw [hvec] at hψc

  have key : ∀ s : Fin 2,
      MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t (PowerSeries.substInvOfIsUnit ψ.series hu))
        (LawHom.substX s ψ.series) = MvPowerSeries.X s := by
    intro s
    rw [show LawHom.substX s ψ.series =
          PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) ψ.series from rfl,
      PowerSeries.subst_def (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) ψ.series,
      MvPowerSeries.subst_comp_subst_apply (hXs s) hXQ, MvPowerSeries.subst_X hXQ s,
      show LawHom.substX s (PowerSeries.substInvOfIsUnit ψ.series hu) =
          PowerSeries.subst (MvPowerSeries.X s : MvPowerSeries (Fin 2) R) (PowerSeries.substInvOfIsUnit ψ.series hu) from rfl,
      ← PowerSeries.subst_def, ← PowerSeries.subst_comp_subst_apply hsQ (PowerSeries.HasSubst.X s), hright,
      PowerSeries.subst_X (PowerSeries.HasSubst.X s)]

  have e := congrArg
    (MvPowerSeries.subst (fun t : Fin 2 => LawHom.substX t (PowerSeries.substInvOfIsUnit ψ.series hu))) hψc
  rw [PowerSeries.subst_def F.toPowerSeries ψ.series, MvPowerSeries.subst_comp_subst_apply hFc hXQ,
    MvPowerSeries.subst_comp_subst_apply hXP hXQ, ← PowerSeries.subst_def] at e
  simp only [key] at e
  rw [← MvPowerSeries.map_algebraMap_eq_subst_X, Algebra.algebraMap_self, MvPowerSeries.map_id] at e

  refine ⟨⟨⟨PowerSeries.substInvOfIsUnit ψ.series hu, hQ0, ?_⟩, ?_⟩, hleft, hright⟩
  ·
    rw [hvec]
    have e' : G.toPowerSeries =
        PowerSeries.subst (MvPowerSeries.subst
          (fun t : Fin 2 => LawHom.substX t (PowerSeries.substInvOfIsUnit ψ.series hu)) F.toPowerSeries) ψ.series := by
      simpa using e.symm
    rw [e', ← PowerSeries.subst_comp_subst_apply hsP hMvF, hleft, PowerSeries.subst_X hMvF]
  ·
    show IsUnit (PowerSeries.coeff 1 (PowerSeries.substInvOfIsUnit ψ.series hu))
    rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact Units.isUnit _

end S_FormalGroup_LawIso_exists_symm_subst_eq_X
end P2MW
export P2MW.S_FormalGroup_LawIso_exists_symm_subst_eq_X (solution)
