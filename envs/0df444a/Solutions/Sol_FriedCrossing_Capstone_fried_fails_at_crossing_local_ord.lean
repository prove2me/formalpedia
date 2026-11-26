-- Prove2me | solution 1 for FriedCrossing.Capstone.fried_fails_at_crossing_local_ord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:55.362519+00:00
-- url     : https://prove2.me/submissions/81fb0006-c77e-4280-a01c-75d932859b76

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_Crossing_crossing_exists_unique_local
import Theorems.Thm_FriedCrossing_RateRatio_crossing_value_local
import Theorems.Thm_FriedCrossing_RateRatio_crossing_value_ne_iff
import Theorems.Thm_FriedCrossing_RateRatio_eventually_ne_nhdsNE
import Theorems.Thm_FriedCrossing_RateRatio_linearArrival_of_hasDerivAt
import Theorems.Thm_FriedCrossing_RateRatio_ratio_tendsto
import Theorems.Thm_FriedCrossing_TorsionCore_jordan_torsion_eq_neg_ratio


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate PureZeros
namespace FriedCrossing.Capstone
theorem _root_.solution
    (s ds z R : ℝ → ℝ) (c : Fin 5 → ℕ) (r δ τR : ℝ)
    (hτR : τR ≠ 0) (hr : 0 < r)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ)
    (hrate : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ ∧ r ≤ ds τ)
    (hzero : ∀ τ₀, |τ₀| < δ → s τ₀ = 0 → ∃ a : ℝ, a ≠ 0 ∧ a ≠ ds τ₀ ∧ LinearArrival z a τ₀)
    (hcont : ∀ τ₀, s τ₀ = 0 → ContinuousAt R τ₀)
    (hfried_off : ∀ τ, |τ| < δ → s τ ≠ 0 → R τ * z τ / s τ = τR)
    (hord : ∀ τ₀, |τ₀| < δ → s τ₀ = 0 → zetaOrder c = 0) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ (∀ τ, |τ| < δ → s τ = 0 → τ = σ) ∧
      zetaOrder c = 0 ∧
      ∃ a ratio : ℝ, a ≠ 0 ∧ ds σ ≠ 0 ∧
        Tendsto (fun τ => s τ / z τ) (𝓝[≠] σ) (𝓝 ratio) ∧
        ratio = ds σ / a ∧ ratio ≠ 1 ∧ R σ = τR * ratio ∧ R σ ≠ τR ∧
        refinedTorsion 1 (ds σ / (a - ds σ)) = -(a / ds σ) := by
  obtain ⟨σ, hσpos, hσle, hσlt, hσ0, huniq⟩ :=
    crossing_exists_unique_local hr (fun τ hτ => (hrate τ hτ).1)
      (fun τ hτ => (hrate τ hτ).2) hs0 hsmall
  have hσabs : |σ| < δ := by rw [abs_lt]; constructor <;> linarith
  have hoff : ∀ᶠ τ in 𝓝[≠] σ, R τ * z τ / s τ = τR := by
    have hnear : ∀ᶠ τ in 𝓝 σ, |τ| < δ :=
      (continuous_abs.continuousAt (x := σ)).eventually (gt_mem_nhds hσabs)
    filter_upwards [eventually_ne_nhdsNE σ, nhdsWithin_le_nhds hnear] with τ hτ hτδ
    exact hfried_off τ hτδ fun h0 => hτ (huniq τ hτδ h0)
  obtain ⟨a, ha, hab, hzA⟩ := hzero σ hσabs hσ0
  have hpA : LinearArrival s (ds σ) σ := linearArrival_of_hasDerivAt (hrate σ hσabs).1 hσ0
  have hb : ds σ ≠ 0 := (lt_of_lt_of_le hr (hrate σ hσabs).2).ne'
  have hval : R σ = τR * (ds σ / a) :=
    crossing_value_local hzA hpA ha hb hoff (hcont σ hσ0)
  have hratio : ds σ / a ≠ 1 := fun h1 => hab ((div_eq_one_iff_eq ha).mp h1).symm
  have hord : zetaOrder c = 0 := hord σ hσabs hσ0
  refine ⟨σ, hσpos, hσle, hσlt, hσ0, huniq, hord, a, ds σ / a, ha, hb,
    ratio_tendsto hpA hzA ha, rfl, hratio, hval, ?_, ?_⟩
  · rw [hval]; exact (crossing_value_ne_iff hτR ha).mpr fun h => hratio (by rw [h, div_self ha])
  · exact jordan_torsion_eq_neg_ratio (ds σ) a hb hab
end FriedCrossing.Capstone
