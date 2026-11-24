-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.rpow_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:22.024601+00:00
-- url     : https://prove2.me/submissions/3be29512-6238-4ae3-b861-8521cddf8f19

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_rpow_bd
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {κ ρ a b t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hρ : κ ≤ ρ) (ha : ρ ≤ a) (hb : ρ ≤ b)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |a ^ (-t) - b ^ (-t)| ≤ 2 * (κ ^ 2)⁻¹ * ρ⁻¹ * |a - b| := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hκ hρ
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun x : ℝ => x ^ (-t)) (f' := fun x : ℝ => (-t) * x ^ (-t - 1)) (s := Set.Ici ρ)
    (C := 2 * (κ ^ 2)⁻¹ * ρ⁻¹) (x := b) (y := a)
    (fun x hx => (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le hρ0 hx)))).hasDerivWithinAt)
    (fun x hx => by
      have hx' : ρ ≤ x := hx
      have hx0 : 0 < x := lt_of_lt_of_le hρ0 hx'
      rw [Real.rpow_sub hx0, Real.rpow_one, norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0, abs_of_pos hx0,
        abs_of_nonneg (Real.rpow_nonneg hx0.le _), div_eq_mul_inv, ← mul_assoc]
      have h1 := rpow_bd hκ hκ1 (hρ.trans hx') ht0 ht2
      have h2 : x⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ0 hx'
      have h3 : 0 ≤ x ^ (-t) := Real.rpow_nonneg hx0.le _
      gcongr)
    (convex_Ici ρ) hb ha
  simpa [Real.norm_eq_abs] using key
end Formalism.L2.Th1.F.Hk2
