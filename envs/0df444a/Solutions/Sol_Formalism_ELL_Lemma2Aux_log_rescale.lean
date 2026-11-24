-- Prove2me | solution 1 for Formalism.ELL.Lemma2Aux.log_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:47.919164+00:00
-- url     : https://prove2.me/submissions/4476be12-d7bb-417b-9c55-c6b9357b92fd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_log_unique
import Theorems.Thm_Formalism_G_homComp
import Theorems.Thm_Formalism_G_logIffHomGa


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
theorem _root_.solution [CharZero K] (F : FormalGroup K) (l : PowerSeries K) (ζ : K) (hζ0 : ζ ≠ 0)
    (hl : IsLog F l) (hhom : IsHom F F (ζ • X)) : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l := by
  have hh : IsHom F FormalGroup.𝔾ₐ (l.subst (ζ • X : PowerSeries K)) :=
    Formalism.G.homComp K F F FormalGroup.𝔾ₐ _ _ hhom ((Formalism.G.logIffHomGa K F l).1 hl).1
  set h : PowerSeries K := l.subst (ζ • X : PowerSeries K) with hdef
  have hFs : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hfun : PowerSeries.subst F.toPowerSeries h = atX h + atY h := by
    have hv := LogP.hs2 (σ := Fin 2) (u := atX h) (v := atY h)
      (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1)
      (PowerSeries.constantCoeff_subst_eq_zero (by simp) h hh.1)
    rw [hh.2, FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv,
      MvPowerSeries.subst_X hv]
    rfl
  have hc1 : coeff 1 h = ζ := by
    rw [hdef, ← PowerSeries.rescale_eq_subst, PowerSeries.coeff_rescale, hl.2.1]; simp
  have hlog : IsLog F (ζ⁻¹ • h) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hh.1]
    · rw [LinearMap.map_smul_of_tower, hc1, smul_eq_mul, inv_mul_cancel₀ hζ0]
    · simp only [Formalism.G.atX, Formalism.G.atY] at hfun ⊢
      rw [PowerSeries.subst_smul hFs, hfun, PowerSeries.subst_smul (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]
  have := LogP.log_unique F hlog hl
  rw [← this, smul_inv_smul₀ hζ0]
end Formalism.ELL.Lemma2Aux
