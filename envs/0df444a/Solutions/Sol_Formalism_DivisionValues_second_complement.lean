-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:25:45.031874+00:00
-- url     : https://prove2.me/submissions/05726b9f-23f1-4ea7-b38e-6f37c4f7c30d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_second_complement_sum
import Theorems.Thm_Formalism_DivisionValues_second_complement_parameter_bounds
import Theorems.Thm_Formalism_DivisionValues_eta_weight_bounds
import Theorems.Thm_Formalism_DivisionValues_second_complement_error_bound
import Theorems.Thm_Formalism_DivisionValues_second_complement_els_bound
import Theorems.Thm_Formalism_DivisionValues_second_complement_absorption
import Theorems.Thm_Formalism_DivisionValues_second_complement_delta_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : Complement2 := by
  unfold Complement2
  intro K _ _ _ _ g hg hcop J Pl _ _ TT _ E F hEfin nn cg Dpi Dp Dm er Eels aT w nν δν δpm
    x eps L b B0 m f k N S tt η w'' b' X'' logd C0 hE hF hcg hnn hEels hDpi hnν hD hx heps hL hb
    hB0 hJ hPl hm hf hk hN hS htt hη hb' hlogd hwb hkS hmη hNw hNN hkb hX hdL hlg hC0 her hδν
    hδpm hEe
  have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_rpow hx heps.le
  have hB0' : B0 = f * m * b * L := by rw [hB0, hL]
  obtain ⟨hfb0, hfbL, hbB0⟩ := second_complement_parameter_bounds f m b L B0 hB0' hf hm hL1 hb
  have hη1 := eta_weight_bounds m tt η w'' hm htt hη hmη
  have hw0 : 0 ≤ w'' := le_trans (mul_nonneg (by linarith) hS) hkS
  have hw'' : w'' ≤ b := by have := mul_nonneg hw0 (sub_nonneg.2 hN); linarith
  have hg0 : (1 : ℝ) ≤ (g 0 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 0).ne'
  have hg1 : (1 : ℝ) ≤ (g 1 : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 1).ne'
  have hlg0 : 0 ≤ Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := Real.log_nonneg (by nlinarith)
  have hcf : (TT.card : ℝ) ≤ f := le_trans (by exact_mod_cast Finset.card_le_univ TT) hPl
  have hone : ∀ j, |2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := by
    intro j
    have hs := second_complement_sum K g hg hcop (E j) (F j) (hEfin j) (nn j) cg m (Dpi j) (Dp j)
      (Dm j) (er j) (Eels j) (hE j) (hF j) hcg (hnn j) (hEels j) Pl TT aT (w j) (nν j) (δν j)
      (δpm j) k (hDpi j) (hnν j) (hD j)
    refine le_trans hs ?_
    refine second_complement_absorption _ _ _ _ _ C0 f m b L B0 hB0' hf hm hb hC0 hfbL ?_ ?_ ?_ hlg0 hlg ?_
    · calc ∑ ρ, (if ρ ∈ TT then 0 else |w j ρ|) ≤ ∑ _ρ : Pl, 2 * b := by
            apply Finset.sum_le_sum
            intro ρ _
            obtain ⟨h1, h2⟩ := hwb j ρ
            split_ifs
            · linarith
            · rw [abs_of_nonneg h1]; exact h2
        _ = (Fintype.card Pl : ℝ) * (2 * b) := by simp
        _ ≤ f * (2 * b) := mul_le_mul_of_nonneg_right hPl (by linarith)
    · calc ∑ ρ, (|δν j ρ| + |δpm j ρ|) ≤ ∑ _ρ : Pl, 5 * C0 * b := by
            apply Finset.sum_le_sum
            intro ρ _
            have hz : (if ρ ∈ TT then b' / x else 0) ≤ b := by
              split_ifs
              · have h1 : b' / x ≤ b' := div_le_self hb' hx
                have h2 : b' ≤ k * b' := by
                  have := mul_nonneg hb' (sub_nonneg.2 hk); linarith
                linarith
              · exact hb
            exact second_complement_delta_bound C0 k S m tt η b w'' _ _ _ hC0 hkS hη1.1 hη1.2 hw'' hz (hδν j ρ) (hδpm j ρ)
        _ = (Fintype.card Pl : ℝ) * (5 * C0 * b) := by simp
        _ ≤ f * (5 * C0 * b) :=
            mul_le_mul_of_nonneg_right hPl (mul_nonneg (mul_nonneg (by norm_num) hC0) hb)
    · exact second_complement_error_bound C0 f N tt m η b w'' (er j) hC0 hf hm hNN hη1.1 hw'' (her j)
    · exact second_complement_els_bound C0 B0 f b L k b' N X'' logd (TT.card : ℝ) (Eels j) hC0 hf hb hk hb' hcf hkb hX
        hlogd hdL hfbL hbB0 (hEe j)
  refine ⟨hone, ?_⟩
  have e : 2 * (∑ j, (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v)) - m * ((∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))) = ∑ j, (2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ, Finset.mul_sum]
  rw [e]
  calc _ ≤ ∑ j, |2 * (∑ᶠ v : HeightOneSpectrum (𝓞 K), lw v * E j v) - (∑ t ∈ TT, aT t) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := Finset.sum_le_sum (fun j _ => hone j)
    _ = (9 * C0 ^ 2 + 6 * C0 + 20) * (m * B0) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]; ring
end Formalism.DivisionValues
