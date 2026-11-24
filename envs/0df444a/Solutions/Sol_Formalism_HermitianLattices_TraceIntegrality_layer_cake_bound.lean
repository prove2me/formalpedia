-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.layer_cake_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:46.120929+00:00
-- url     : https://prove2.me/submissions/4d0600a6-b2b7-439c-8aab-730704944077

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SeparatedSetPackingBound
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_gamma_integral_polynomial_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Set Metric
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : LayerCakeSumBound := by
  intro Y h g v hv hh hc
  obtain ⟨hint, hle⟩ := Formalism.LogVandermondeBounds.flipTwoThree.gamma_integral_polynomial_bound v g hv
  have hpi := Real.pi_pos
  set w : ℝ → ℝ := fun u => Real.pi * Real.exp (-Real.pi * u) with hw
  have hwpos : ∀ u, 0 ≤ w u := fun u => by positivity
  have hwint : IntegrableOn w (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith) 0).const_mul _
  have key : ∀ F : Finset Y,
      ∑ y ∈ F, Real.exp (-Real.pi * h y) ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
    intro F
    have h1 : ∀ y, Real.exp (-Real.pi * h y) = ∫ u in Ioi 0, (Ioi (h y)).indicator w u := by
      intro y
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right (hh y)]
      simp only [hw]
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
      field_simp
    have hi : ∀ y, IntegrableOn ((Ioi (h y)).indicator w) (Ioi 0) := fun y =>
      hwint.indicator measurableSet_Ioi
    have hpt : ∀ u ∈ Ioi (0 : ℝ), ∑ y ∈ F, (Ioi (h y)).indicator w u ≤
        2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) := by
      intro u hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      obtain ⟨hfin, hcard⟩ := hc u hu0
      have e1 : ∑ y ∈ F, (Ioi (h y)).indicator w u = ((F.filter (fun y => h y < u)).card : ℝ) * w u := by
        simp only [Set.indicator_apply, mem_Ioi]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have e2 : (F.filter (fun y => h y < u)).card ≤ {y | h y ≤ u}.ncard := by
        rw [← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard _ hfin
        intro y hy
        simp only [Finset.coe_filter, mem_ofPred_eq] at hy
        exact le_of_lt hy.2
      have e3 : ((F.filter (fun y => h y < u)).card : ℝ) ≤ 2 ^ g * (1 + 4 * u * v) ^ g :=
        le_trans (by exact_mod_cast e2) hcard
      rw [e1]
      calc ((F.filter (fun y => h y < u)).card : ℝ) * w u
          ≤ (2 ^ g * (1 + 4 * u * v) ^ g) * w u := mul_le_mul_of_nonneg_right e3 (hwpos u)
        _ = _ := by simp only [hw]; ring
    calc ∑ y ∈ F, Real.exp (-Real.pi * h y)
        = ∑ y ∈ F, ∫ u in Ioi 0, (Ioi (h y)).indicator w u := Finset.sum_congr rfl fun y _ => h1 y
      _ = ∫ u in Ioi 0, ∑ y ∈ F, (Ioi (h y)).indicator w u :=
          (integral_finsetSum F fun y _ => hi y).symm
      _ ≤ ∫ u in Ioi (0 : ℝ), 2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) :=
          setIntegral_mono_on (integrable_finsetSum F fun y _ => hi y) (hint.const_mul _)
            measurableSet_Ioi hpt
      _ = 2 ^ g * ∫ u in Ioi (0 : ℝ), Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g :=
          integral_const_mul _ _
      _ ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := mul_le_mul_of_nonneg_left hle (by positivity)
  have hnn : (0 : Y → ℝ) ≤ fun y => Real.exp (-Real.pi * h y) := fun y => (Real.exp_pos _).le
  have hsum := Real.tsum_le_of_sum_le hnn key
  refine ⟨summable_of_sum_le hnn key, hsum, ?_⟩
  have hb : 1 + 4 * (g : ℝ) * v / Real.pi ≤ 2 + 8 * g * v := by
    have h3 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hgv : 0 ≤ 4 * (g : ℝ) * v := by positivity
    have : 4 * (g : ℝ) * v / Real.pi ≤ 4 * (g : ℝ) * v := div_le_self hgv h3
    linarith
  have hb0 : 0 ≤ 1 + 4 * (g : ℝ) * v / Real.pi := by positivity
  calc (2 : ℝ) ^ g * ∑' y, Real.exp (-Real.pi * h y)
      ≤ 2 ^ g * (2 ^ g * (1 + 4 * g * v / Real.pi) ^ g) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 4 ^ g * (2 + 8 * g * v) ^ g :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb g) (by positivity)
end Formalism.HermitianLattices.TraceIntegrality
