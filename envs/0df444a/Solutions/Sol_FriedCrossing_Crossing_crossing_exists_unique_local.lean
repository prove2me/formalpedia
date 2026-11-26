-- Prove2me | solution 1 for FriedCrossing.Crossing.crossing_exists_unique_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:45:18.172238+00:00
-- url     : https://prove2.me/submissions/67cc72ff-dd26-4ac8-8a03-df892d89e3c5

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Crossing
namespace FriedCrossing.Crossing
theorem _root_.solution {s ds : ℝ → ℝ} {r δ : ℝ} (hr : 0 < r)
    (hderiv : ∀ τ, |τ| < δ → HasDerivAt s (ds τ) τ) (hlow : ∀ τ, |τ| < δ → r ≤ ds τ)
    (hs0 : s 0 < 0) (hsmall : |s 0| < r * δ) :
    ∃ σ, 0 < σ ∧ σ ≤ |s 0| / r ∧ σ < δ ∧ s σ = 0 ∧ ∀ τ, |τ| < δ → s τ = 0 → τ = σ := by
  have hmemI : ∀ τ, τ ∈ Set.Ioo (-δ) δ ↔ |τ| < δ := fun τ => by
    rw [Set.mem_Ioo, abs_lt]
  have hcontOn : ContinuousOn s (Set.Ioo (-δ) δ) := fun τ hτ =>
    (hderiv τ ((hmemI τ).mp hτ)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn s (Set.Ioo (-δ) δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcontOn fun τ hτ => ?_
    rw [interior_Ioo] at hτ
    have hτ' := (hmemI τ).mp hτ
    rw [(hderiv τ hτ').deriv]
    exact lt_of_lt_of_le hr (hlow τ hτ')
  set T := -s 0 / r with hT
  have habs : |s 0| = -s 0 := abs_of_neg hs0
  have hTpos : 0 < T := div_pos (neg_pos.mpr hs0) hr
  have hTlt : T < δ := by
    rw [hT, div_lt_iff₀ hr]; rw [habs] at hsmall; linarith
  have hrT : r * T = -s 0 := by rw [hT, mul_div_cancel₀ _ hr.ne']
  -- MVT on [0, T]: s T − s 0 = ds c · T ≥ r T = −s 0
  have hIcc : Set.Icc 0 T ⊆ Set.Ioo (-δ) δ := fun τ hτ =>
    ⟨by linarith [hτ.1], lt_of_le_of_lt hτ.2 hTlt⟩
  have hcontIcc : ContinuousOn s (Set.Icc 0 T) := hcontOn.mono hIcc
  have hderivIoo : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt s (ds τ) τ := fun τ hτ =>
    hderiv τ ((hmemI τ).mp (hIcc (Set.Ioo_subset_Icc_self hτ)))
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope s ds hTpos hcontIcc hderivIoo
  have hc' : |c| < δ := (hmemI c).mp (hIcc (Set.Ioo_subset_Icc_self hc))
  have hsT : 0 ≤ s T := by
    have h1 : r ≤ ds c := hlow c hc'
    have h2 : ds c * (T - 0) = s T - s 0 := by
      rw [hcslope, sub_zero]; exact div_mul_cancel₀ _ hTpos.ne'
    have h3 : r * T ≤ ds c * T := mul_le_mul_of_nonneg_right h1 hTpos.le
    simp only [sub_zero] at h2
    linarith
  obtain ⟨σ, hσmem, hσ⟩ : (0 : ℝ) ∈ s '' Set.Icc 0 T :=
    intermediate_value_Icc hTpos.le hcontIcc ⟨hs0.le, hsT⟩
  have hσpos : 0 < σ := by
    rcases hσmem.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hσ; linarith
  have hσlt : σ < δ := lt_of_le_of_lt hσmem.2 hTlt
  refine ⟨σ, hσpos, ?_, hσlt, hσ, fun τ hτ hτ0 => ?_⟩
  · rw [habs]; exact hσmem.2
  · exact hmono.injOn ((hmemI τ).mpr hτ) ((hmemI σ).mpr (by rw [abs_lt]; constructor <;> linarith))
      (hτ0.trans hσ.symm)
end FriedCrossing.Crossing
