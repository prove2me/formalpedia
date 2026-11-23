-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.substMv_fadd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:27.238814+00:00
-- url     : https://prove2.me/submissions/efa59cdc-d40e-4423-be26-d2479a635432

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Dict
variable {K : Type} [Field K] {σ τ : Type} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Dict
theorem _root_.solution [Finite σ] (h : IsLogPair l linv) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (fadd l linv u v) =
      fadd l linv (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
  have hsa : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have psub : ∀ (b : MvPowerSeries σ K), MvPowerSeries.constantCoeff b = 0 → ∀ f : PowerSeries K,
      MvPowerSeries.subst a (PowerSeries.subst b f) = PowerSeries.subst (MvPowerSeries.subst a b) f := by
    intro b hb f
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => b)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hb)) hsa]
  have hu' : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hu l h.1
  have hv' : MvPowerSeries.constantCoeff (PowerSeries.subst v l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hv l h.1
  unfold fadd
  rw [psub _ (by rw [map_add, hu', hv', add_zero]), ← MvPowerSeries.coe_substAlgHom hsa, map_add,
    MvPowerSeries.coe_substAlgHom hsa, psub u hu, psub v hv]
end Formalism.L2.Th1.C.Dict
