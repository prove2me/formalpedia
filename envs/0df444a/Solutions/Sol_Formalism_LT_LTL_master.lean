-- Prove2me | solution 1 for Formalism.LT.LTL.master
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:42.346879+00:00
-- url     : https://prove2.me/submissions/6b65768c-350f-4812-bd9a-5f40c098be97

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_low_subst_sub
import Theorems.Thm_P2M_Formalism_LT_LTL_key__07a773ad9047
import Theorems.Thm_Formalism_LT_LTL_near_one_subst_X_coeff_one_smul_X
import Theorems.Thm_Formalism_LT_LTL_prod_const_pow
import Theorems.Thm_Formalism_LT_LTL_inverseIntegralClasses_cc_s_fact
import Theorems.Thm_Formalism_LT_LTL_Ep_sub

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
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) (π : K) (he1 : coeff 1 e = π) (he'1 : coeff 1 e' = π)
    {N : ℕ} {ψ φ : MvPowerSeries ι K} (hψ : MvPowerSeries.constantCoeff ψ = 0)
    (hφ : MvPowerSeries.constantCoeff φ = 0) (hN : Low N (ψ - φ)) (d : ι →₀ ℕ)
    (hd : d.degree ≤ N) :
    MvPowerSeries.coeff d (Ldef e e' ψ) - MvPowerSeries.coeff d (Ldef e e' φ) =
      (π ^ N - π) * MvPowerSeries.coeff d (ψ - φ) := by
  have hag : Agree N ψ φ := fun d hd => by
    have := hN d hd; rw [map_sub] at this; exact sub_eq_zero.mp this
  have h1 := key' e he0 hψ hφ hag d (by omega)
  rw [he1] at h1
  simp only [map_sub, MvPowerSeries.coeff_smul] at h1
  have h2 := low_subst_sub (inverseIntegralClasses_cc_s_fact e' he'0) (fun i => by simp)
    (fun i => near_one_subst_X_coeff_one_smul_X e' he'0 i) hN d (by omega)
  rw [he'1, ← MvPowerSeries.rescale_eq_subst, map_sub, MvPowerSeries.coeff_rescale,
    prod_const_pow] at h2
  have h3 : MvPowerSeries.coeff d (Ep e' ψ) - MvPowerSeries.coeff d (Ep e' φ) =
      MvPowerSeries.coeff d (MvPowerSeries.subst
        (fun i => e'.subst (MvPowerSeries.X i : MvPowerSeries ι K)) (ψ - φ)) := by
    rw [← map_sub, Ep_sub e' he'0]; rfl
  have h4 : π ^ d.degree * MvPowerSeries.coeff d (ψ - φ) =
      π ^ N * MvPowerSeries.coeff d (ψ - φ) := by
    rcases lt_or_eq_of_le hd with hlt | heq
    · rw [hN d hlt, mul_zero, mul_zero]
    · rw [heq]
  unfold Ldef
  simp only [map_sub] at h2 h4 ⊢
  linear_combination h3 + h2 + h4 - h1
end Formalism.LT.LTL
