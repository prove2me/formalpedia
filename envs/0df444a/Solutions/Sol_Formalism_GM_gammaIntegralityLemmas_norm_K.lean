-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.norm_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:08.19548+00:00
-- url     : https://prove2.me/submissions/3c93dc7a-367c-4c07-a2f5-a742d3c1997b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_nat_eq
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (κ : ℕ) (h h' : ℚ_[p]) (Eh Eh' : ℤ) (hh : ‖h‖ ≤ (p : ℝ) ^ Eh) (hh' : ‖h'‖ ≤ (p : ℝ) ^ Eh')
    (Num Den : ℕ) (hN : Num ≠ 0) (hD : Den ≠ 0) (s : ℚ_[p]) (hs : ‖s‖ = 1)
    (hE : -(κ : ℤ) + Eh + Eh' - (padicValNat p Num : ℤ) + (padicValNat p Den : ℤ) ≤ 0) :
    ‖(p : ℚ_[p]) ^ κ * (s * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))‖ ≤ 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, hs, Padic.norm_p_pow, norm_nat_eq _ hN,
    norm_nat_eq _ hD]
  calc (p : ℝ) ^ (-(κ : ℤ)) * (1 * ‖h‖ * ‖h'‖ * (p : ℝ) ^ (-(padicValNat p Num : ℤ)) /
        (p : ℝ) ^ (-(padicValNat p Den : ℤ)))
      ≤ (p : ℝ) ^ (-(κ : ℤ)) * (1 * (p : ℝ) ^ Eh * (p : ℝ) ^ Eh' * (p : ℝ) ^ (-(padicValNat p Num : ℤ)) /
        (p : ℝ) ^ (-(padicValNat p Den : ℤ))) := by
        gcongr
    _ = (p : ℝ) ^ (-(κ : ℤ) + Eh + Eh' - (padicValNat p Num : ℤ) + (padicValNat p Den : ℤ)) := by
        rw [zpow_add₀ hp0, zpow_sub₀ hp0, zpow_add₀ hp0, zpow_add₀ hp0, zpow_neg, zpow_neg, zpow_neg]
        field_simp
    _ ≤ (p : ℝ) ^ (0 : ℤ) := zpow_mono' hE
    _ = 1 := by simp
end Formalism.GM.gammaIntegralityLemmas
