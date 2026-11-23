-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Easy.dual_volume_power_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.162616+00:00
-- url     : https://prove2.me/submissions/ed477c24-b526-42d8-80dd-80b83da00f11

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real
open Formalism.FourierDecayAlt.P.Easy
namespace Formalism.FourierDecayAlt.P.Easy
theorem _root_.solution (ι : Type) [Fintype ι] (c : ι → ℝ) (g rd : ℝ) (r i : ℕ) (hg : 0 < g) (hrd : 0 < rd) :
    (∏ v, c v * (2 * π / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) /
        (g * rd ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(Fintype.card ι : ℤ)) =
      (∏ v, c v) * (2 * π / rd) ^ (((2 * i : ℤ) - 3 - 2 * r) * Fintype.card ι) *
        g ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * Fintype.card ι) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set e : ℤ := (2 * i : ℤ) - 3 - 2 * r with he
  set f : ℤ := (Fintype.card ι : ℤ) with hf
  have h1 : (2 * r : ℤ) + 3 - 2 * i = -e := by rw [he]; ring
  have h2 : ((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) = -e + 1 := by rw [he]; ring
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← zpow_natCast, ← hf]
  have hg0 : g ≠ 0 := hg.ne'
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hpi0 : (2 * π) ≠ 0 := hpi.ne'
  generalize 2 * π = A at hpi0 ⊢
  have k1 : ((A / g) ^ e) ^ f = A ^ (e * f) / g ^ (e * f) := by
    rw [← zpow_mul, div_zpow]
  have k2 : (g * rd ^ (-e)) ^ (-f) = (g ^ f)⁻¹ * rd ^ (e * f) := by
    rw [mul_zpow, ← zpow_mul, zpow_neg, show (-e * -f) = e * f by ring]
  have k3 : (A / rd) ^ (e * f) = A ^ (e * f) / rd ^ (e * f) := div_zpow _ _ _
  have k4 : g ^ ((-e + 1) * f) = (g ^ (e * f))⁻¹ * g ^ f := by
    rw [show ((-e + 1) * f) = -(e * f) + f by ring, zpow_add₀ hg0, zpow_neg]
  rw [k1, k2, k3, k4]
  have : g ^ (e * f) ≠ 0 := zpow_ne_zero _ hg0
  have : g ^ f ≠ 0 := zpow_ne_zero _ hg0
  have : rd ^ (e * f) ≠ 0 := zpow_ne_zero _ hrd0
  field_simp
end Formalism.FourierDecayAlt.P.Easy
