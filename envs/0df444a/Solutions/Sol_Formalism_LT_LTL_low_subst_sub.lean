-- Prove2me | solution 1 for Formalism.LT.LTL.low_subst_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:51.205332+00:00
-- url     : https://prove2.me/submissions/d5ad00e5-2d66-4429-9b4e-a7f353517551

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_near_monomial

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
theorem _root_.solution [Finite ι] {τ : Type*} {a b : ι → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (hab : ∀ i, Near 1 (a i) (b i)) {N : ℕ} {δ : MvPowerSeries ι K} (hδ : Low N δ) :
    Low (N + 1) (MvPowerSeries.subst a δ - MvPowerSeries.subst b δ) := by
  intro d hd
  have ha' : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [map_sub, MvPowerSeries.coeff_subst ha', MvPowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha' δ d)
      (MvPowerSeries.coeff_subst_finite hb' δ d)]
  have : ∀ m : ι →₀ ℕ, MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => a s ^ e) - MvPowerSeries.coeff m δ •
      MvPowerSeries.coeff d (m.prod fun s e => b s ^ e) = 0 := by
    intro m
    rw [← smul_sub]
    by_cases hm : m.degree < N
    · rw [hδ m hm, zero_smul]
    · have := (near_monomial hab m).2.2 d (by omega)
      rw [map_sub] at this
      rw [this, smul_zero]
  simp only [this, finsum_zero]
end Formalism.LT.LTL
