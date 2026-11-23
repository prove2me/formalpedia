-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.subst_biextension_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:29.762811+00:00
-- url     : https://prove2.me/submissions/8356684f-39b4-411e-a782-ae6716900d26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_substMv_fadd

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
theorem _root_.solution [Finite σ] (h : IsLogPair l linv) (ph : PowerSeries K) {u v : MvPowerSeries σ K}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (be0 l linv ph u v) =
      be0 l linv ph (MvPowerSeries.subst a u) (MvPowerSeries.subst a v) := by
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
  have hf : MvPowerSeries.constantCoeff (fadd l linv u v) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hu', hv', add_zero]) linv h.2.2.1
  unfold be0
  rw [← MvPowerSeries.coe_substAlgHom hsa, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hsa,
    psub _ hf, psub u hu, psub v hv, substMv_fadd h hu hv ha]
end Formalism.L2.Th1.C.Dict
