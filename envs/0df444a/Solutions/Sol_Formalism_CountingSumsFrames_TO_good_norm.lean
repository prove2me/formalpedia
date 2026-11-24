-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.good_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:03.746846+00:00
-- url     : https://prove2.me/submissions/b6005aa7-a778-4919-923e-7dc9088ec75c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (E : ℝ) (hE : 0 ≤ E) (d : ℚ_[p]) (hd : ¬ ‖d‖ < (p : ℝ) ^ (-E)) :
    ‖(p : ℚ_[p]) ^ ⌊E⌋₊ / d‖ ≤ 1 ∧ d ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    rw [h, norm_zero]
    exact Real.rpow_pos_of_pos hp0 _
  refine ⟨?_, hd0⟩
  rw [not_lt, Padic.norm_eq_zpow_neg_valuation hd0, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff hp1] at hd
  have hk : ((d.valuation : ℤ) : ℝ) ≤ E := by push_cast at hd; linarith
  have hk' : d.valuation ≤ (⌊E⌋₊ : ℤ) := by
    by_cases h0 : d.valuation ≤ 0
    · exact h0.trans (Int.natCast_nonneg _)
    · push Not at h0
      have h1 : ((d.valuation.toNat : ℕ) : ℝ) ≤ E := by
        have : ((d.valuation.toNat : ℕ) : ℤ) = d.valuation := Int.toNat_of_nonneg h0.le
        calc ((d.valuation.toNat : ℕ) : ℝ) = (((d.valuation.toNat : ℕ) : ℤ) : ℝ) := by push_cast; rfl
          _ = ((d.valuation : ℤ) : ℝ) := by rw [this]
          _ ≤ E := hk
      have h2 := Nat.le_floor h1
      omega
  rw [norm_div, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hd0, div_le_one (zpow_pos hp0 _),
    inv_pow, ← zpow_natCast, ← zpow_neg]
  exact zpow_le_zpow_right₀ hp1.le (by omega)
end Formalism.CountingSumsFrames.TO
