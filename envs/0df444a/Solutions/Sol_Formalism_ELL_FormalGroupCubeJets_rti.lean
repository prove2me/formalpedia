-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.rti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:50.68498+00:00
-- url     : https://prove2.me/submissions/3cef7a38-ac24-44ae-86e2-2535dd348d43

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_omegaF_eq
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_omega_key
import Theorems.Thm_Formalism_G_LogP_psubst_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (j : Fin 3) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j])) =
      (invD F ψ).subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) := by
  have hXj : MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by
    simp
  have hB : MvPowerSeries.constantCoeff ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp [hA]),
      (FK F).zero_constantCoeff]
  have hs := hs2 hA hXj
  have dB : MvPowerSeries.pderiv K j ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) =
      (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries).subst ![A, MvPowerSeries.X j] := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp [hA])]
    simp [Fin.sum_univ_two, hdA]
  have hω : (omegaF F).subst ((FK F).toPowerSeries.subst ![A, MvPowerSeries.X j]) =
      (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries).subst ![A, MvPowerSeries.X j] *
        (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) := by
    have := congrArg (MvPowerSeries.subst ![A, MvPowerSeries.X j]) (omega_key (FK F))
    rw [MvPowerSeries.subst_mul hs, psubst_subst _ (FK F).zero_constantCoeff hs, atY,
      psubst_subst _ hX1 hs, MvPowerSeries.subst_X hs] at this
    simpa [omegaF_eq] using this
  rw [Dj, pderiv_psubst hB, dB, invD,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hB), hω]
  ring
end Formalism.ELL.FormalGroupCubeJets
