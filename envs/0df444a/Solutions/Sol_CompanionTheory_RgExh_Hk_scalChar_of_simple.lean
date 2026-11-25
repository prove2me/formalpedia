-- Prove2me | solution 1 for CompanionTheory.RgExh.Hk.scalChar_of_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:54.676729+00:00
-- url     : https://prove2.me/submissions/d150a5f3-0965-4989-81ba-205a53ae2964

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliC_central

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
private theorem eq_zero_of_pow_eq_zero_of_commute_of_isSimple {X : GMod n} (hS : IsSimple X) (N : Module.End ℂ X.V)
    (hc : ∀ a b, Commute (X.E a b) N) (k : ℕ) (hk : N ^ k = 0) : N = 0 := by
  have hker : ∀ a b, ∀ x ∈ LinearMap.ker N, X.E a b x ∈ LinearMap.ker N := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, ← (hc a b).eq, Module.End.mul_apply, hx, map_zero]
  rcases hS.2 (LinearMap.ker N) hker with h | h
  · exfalso
    have hinj : Function.Injective N := LinearMap.ker_eq_bot.1 h
    have hinjk : Function.Injective ⇑(N ^ k) := by
      rw [Module.End.coe_pow]
      exact hinj.iterate k
    obtain ⟨x, y, hxy⟩ := hS.1.exists_pair_ne
    apply hxy
    apply hinjk
    simp [hk]
  · exact LinearMap.ker_eq_top.1 h
end CompanionTheory.RgExh.Hk
end
end

set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
namespace CompanionTheory.RgExh.Hk
theorem _root_.solution (hQ : QdetEq) {X : GMod n} {χ : Fin n → ℂ} (hS : IsSimple X) (hH : HasChar X χ) :
    ScalChar X χ := by
  unfold CompanionTheory.RgExh.ScalChar
  obtain ⟨k, hk⟩ := hH
  intro Y
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_eq_zero_of_commute_of_isSimple hS _ (fun a b => ?_) k (hk Y)
  have hc : Commute (X.E a b) (Formalism.REAL.qdet X.E (Y + ((n : ℂ) - 1) / 2)) := by
    rw [hQ n X.V X.E (Y + ((n : ℂ) - 1) / 2)]
    exact ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelliC_central X.E X.gl _ a b
  exact hc.sub_right ((Commute.one_right _).smul_right _)
end CompanionTheory.RgExh.Hk
