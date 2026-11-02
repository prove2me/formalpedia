-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_nonneg_of_hasDerivAt_im
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:54:31.392433+00:00
-- url     : https://prove2.me/submissions/151d9c0f-ae8c-4ed3-82df-2b71fdfb249c

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Slope



namespace FiniteEnergyPlane

open Filter Topology
open scoped Real

theorem hasLoopWind_nonneg_of_hasDerivAt_im_aux {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) : 0 ≤ k := by
  obtain ⟨-, -, hg0, θ, hθc, hθ, hθk⟩ := hg
  have hpi := Real.pi_pos
  have h2pi : 0 < 2 * π := by positivity
  set m : ℤ := ⌊θ 0 / (2 * π)⌋ with hm
  have hm1 : (m : ℝ) ≤ θ 0 / (2 * π) := Int.floor_le _
  have hm2 : θ 0 / (2 * π) < m + 1 := Int.lt_floor_add_one _
  have hlo : 2 * π * m ≤ θ 0 := by rw [le_div_iff₀ h2pi] at hm1; linarith
  have hhi : θ 0 < 2 * π * m + 2 * π := by rw [div_lt_iff₀ h2pi] at hm2; linarith
  have him : ∀ t, (g t).im = ‖g t‖ * Real.sin (θ t) := by
    intro t
    conv_lhs => rw [hθ t]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hre : ∀ t, (g t).re = ‖g t‖ * Real.cos (θ t) := by
    intro t
    conv_lhs => rw [hθ t]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hbar : Set.Icc (0 : ℝ) 1 ⊆ {t | 2 * π * m ≤ θ t} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · exact (isClosed_le continuous_const hθc).inter isClosed_Icc
    · exact hlo
    · rintro x ⟨hx, -⟩
      simp only [Set.mem_setOf_eq] at hx
      rcases hx.lt_or_eq with hlt | heq
      · filter_upwards [nhdsWithin_le_nhds ((isOpen_lt continuous_const hθc).mem_nhds hlt)]
          with t ht using le_of_lt ht
      · have hsin : Real.sin (θ x) = 0 := by
          rw [← heq, show 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) by ring]
          simpa using Real.sin_sub_int_mul_two_pi 0 m
        have hcos : Real.cos (θ x) = 1 := by
          rw [← heq, show 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) by ring]
          exact Real.cos_int_mul_two_pi m
        have hgx : 0 < ‖g x‖ := norm_pos_iff.2 (hg0 x)
        have hderpos : 0 < c * (g x).re := by rw [hre, hcos, mul_one]; positivity
        have hslope := hasDerivWithinAt_iff_tendsto_slope.1
          ((hd x).hasDerivWithinAt (s := Set.Ioi x))
        rw [Set.diff_singleton_eq_self (s := Set.Ioi x) (lt_irrefl x)] at hslope
        have hev1 : ∀ᶠ t in 𝓝[>] x, 0 < slope (fun s => (g s).im) x t :=
          hslope.eventually (lt_mem_nhds hderpos)
        have hev2 : ∀ᶠ t in 𝓝[>] x, θ t ∈ Set.Ioo (θ x - π) (θ x + π) :=
          nhdsWithin_le_nhds ((hθc.tendsto x) (Ioo_mem_nhds (by linarith) (by linarith)))
        filter_upwards [hev1, hev2, self_mem_nhdsWithin] with t h1 h2 h3
        have himx : (g x).im = 0 := by rw [him, hsin, mul_zero]
        rw [slope_def_field, himx, sub_zero] at h1
        have htx : 0 < t - x := sub_pos.2 h3
        have ht : 0 < (g t).im := by
          by_contra hn
          push_neg at hn
          exact absurd h1 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hn htx.le))
        rw [him] at ht
        have hs : 0 < Real.sin (θ t) := pos_of_mul_pos_right ht (norm_nonneg _)
        show 2 * π * m ≤ θ t
        by_contra hneg
        push_neg at hneg
        have hsn : Real.sin (θ t) ≤ 0 := by
          rw [← Real.sin_sub_int_mul_two_pi (θ t) m]
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
          · linarith
          · have := h2.1
            linarith
        linarith
  have h1 : 2 * π * m ≤ θ 1 := hbar ⟨zero_le_one, le_refl 1⟩
  have hk : 0 < 2 * π * ((k : ℝ) + 1) := by nlinarith
  have hk' : (-1 : ℝ) < k := by
    have := (mul_pos_iff_of_pos_left h2pi).1 hk
    linarith
  have : (-1 : ℤ) < k := by exact_mod_cast hk'
  omega

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) : 0 ≤ k :=
  hasLoopWind_nonneg_of_hasDerivAt_im_aux hg hc hd
