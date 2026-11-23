-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.add_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.647988+00:00
-- url     : https://prove2.me/submissions/106574e3-6ea4-4e90-a3b8-34a23e6fd78a

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
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
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
open Formalism.G
namespace Formalism.ELL.Lemma2Aux
theorem _root_.solution (Fs : MvPowerSeries (Fin 2) K) (hFc : MvPowerSeries.constantCoeff Fs = 0)
    (l E g : PowerSeries K) (hl0 : constantCoeff l = 0) (hlF : l.subst Fs = atX l + atY l)
    (hE0 : constantCoeff E = 0) (hEl : E.subst l = X) (hlE : l.subst E = X) :
    MvPowerSeries.subst (fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
        (g.subst Fs - atX g - atY g) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g) := by
  set b := fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) with hbdef
  have hbi : ∀ i, MvPowerSeries.constantCoeff (b i) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (by simp) E hE0
  have hb : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hbi
  have hE : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hlb : ∀ i, l.subst (b i) = MvPowerSeries.X i := by
    intro i
    simp only [hbdef]
    rw [← PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X i), hlE,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have hsF : MvPowerSeries.constantCoeff (MvPowerSeries.subst b Fs) = 0 := by
    rw [LogP.constantCoeff_subst_of_zero Fs hbi, hFc]
  have h1 : l.subst (MvPowerSeries.subst b Fs) = MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
    rw [← LogP.psubst_subst l hFc hb, hlF, MvPowerSeries.subst_add hb, atX, atY,
      LogP.psubst_subst l (by simp) hb, LogP.psubst_subst l (by simp) hb,
      MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, hlb, hlb]
  have key : MvPowerSeries.subst b Fs = E.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    calc MvPowerSeries.subst b Fs
        = PowerSeries.subst (MvPowerSeries.subst b Fs) (X : PowerSeries K) :=
          (PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hsF)).symm
      _ = PowerSeries.subst (MvPowerSeries.subst b Fs) (PowerSeries.subst l E : PowerSeries K) := by rw [hEl]
      _ = PowerSeries.subst (PowerSeries.subst (MvPowerSeries.subst b Fs) l) E :=
          PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
            (PowerSeries.HasSubst.of_constantCoeff_zero hsF) E
      _ = _ := by rw [h1]
  rw [MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, LogP.psubst_subst g hFc hb, key, atX, atY,
    LogP.psubst_subst g (by simp) hb, LogP.psubst_subst g (by simp) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.of_constantCoeff_zero hS),
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X 0),
    PowerSeries.subst_comp_subst_apply hE (PowerSeries.HasSubst.X 1)]
end Formalism.ELL.Lemma2Aux
