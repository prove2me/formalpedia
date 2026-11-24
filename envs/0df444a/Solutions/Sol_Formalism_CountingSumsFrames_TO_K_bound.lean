-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.K_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:48.895857+00:00
-- url     : https://prove2.me/submissions/4ac45eef-b261-4b94-a4fc-e929443c0fef

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
theorem _root_.solution (N r a j0 : ℕ) (κ : ℝ) (hr : 2 ≤ r) (hj0 : j0 ≤ N)
    (hκ : ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    ((⌈κ / (N + 2)⌉₊ * j0 + 2 * ⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) ≤ 3 * κ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg1 : 1 ≤ lgV2 p a r := by
    unfold lgV2
    have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    have := Real.logb_nonneg hp1 this
    linarith
  have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hκN : ((N : ℝ) + 2) * 4 ≤ κ := by
    have h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
    have h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r :=
      le_mul_of_one_le_right (by positivity) hlg1
    linarith
  have hκ0 : 0 ≤ κ := by nlinarith
  have hce : ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) < κ / (N + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hj : (j0 : ℝ) ≤ N := by exact_mod_cast hj0
  have hj' : (0 : ℝ) ≤ j0 := Nat.cast_nonneg j0
  have h3 : κ / (N + 2) * (N + 2) = κ := by
    field_simp
  push_cast
  calc ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * j0 + 2 * ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ)
      = ((⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) * (j0 + 2) := by ring
    _ ≤ (κ / (N + 2) + 1) * (j0 + 2) := mul_le_mul_of_nonneg_right hce.le (by positivity)
    _ ≤ (κ / (N + 2) + 1) * (N + 2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = κ / (N + 2) * (N + 2) + (N + 2) := by ring
    _ ≤ 3 * κ := by rw [h3]; linarith
end Formalism.CountingSumsFrames.TO
