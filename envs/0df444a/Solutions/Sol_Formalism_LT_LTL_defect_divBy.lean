-- Prove2me | solution 1 for Formalism.LT.LTL.defect_divBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:28.990896+00:00
-- url     : https://prove2.me/submissions/9a8f7976-9993-4d5d-9114-2188e620ece5

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_inverseIntegralClasses_cc_s_fact
import Theorems.Thm_Formalism_LT_LTL_dv_sub
import Theorems.Thm_Formalism_LT_LTL_divBy_subst_sub
import Theorems.Thm_Formalism_LT_LTL_divBy_psubst
import Theorems.Thm_Formalism_LT_LTL_frob_pi
import Theorems.Thm_P2M_Formalism_LT_LTL_integralMv_X__f8764449aa3b
import Theorems.Thm_Formalism_LT_InvIntP_integralSubst
import Theorems.Thm_Formalism_LT_InvIntP_integral_pow


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
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution [Finite ι] {p q : ℕ} {π : K} (hS : LTSetting K p q π)
    {e e' : PowerSeries K} (he : IsLTSeries q π e) (he' : IsLTSeries q π e')
    {P : MvPowerSeries ι K} (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv π (Ldef e e' P) := by
  obtain ⟨hpr, ⟨h, hh, rfl⟩, hπ0, hπ1, hp, hF⟩ := hS
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have ha : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0

  have h1 : DivByMv π (e.subst P - P ^ (p ^ h)) := by
    have := divBy_psubst π (e - X ^ (p ^ h)) P he.2.2.2 hP0 hP
    rwa [PowerSeries.subst_sub ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha] at this
  have h2 := frob_pi p h hpr π hπ0 hπ1 hp hF P hP
  have hXq : ∀ i : ι, MvPowerSeries.constantCoeff
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) = 0 := fun i => by
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]
  have hcong : ∀ i : ι, Cong π (e'.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      ((MvPowerSeries.X i : MvPowerSeries ι K) ^ (p ^ h)) := by
    intro i
    have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by simp
    have hXs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries ι K) :=
      PowerSeries.HasSubst.of_constantCoeff_zero hX0
    refine ⟨integralSubst e' _ he'.1 hX0 (integralMv_X' i), integral_pow (integralMv_X' i) _, ?_⟩
    have := divBy_psubst π (e' - X ^ (p ^ h)) (MvPowerSeries.X i : MvPowerSeries ι K) he'.2.2.2
      hX0 (integralMv_X' i)
    rwa [PowerSeries.subst_sub hXs, PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs] at this
  have h3 : DivByMv π (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) := by
    have := divBy_subst_sub (inverseIntegralClasses_cc_s_fact e' he'.2.1) hXq hcong hP
    rwa [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  have e4 : Ldef e e' P = (Ep e' P - MvPowerSeries.expand (p ^ h) hq P) -
      (P ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq P) - (e.subst P - P ^ (p ^ h)) := by
    unfold Ldef; ring
  rw [e4]
  exact dv_sub (dv_sub h3 h2) h1
end Formalism.LT.LTL
