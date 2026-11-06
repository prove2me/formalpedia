-- Prove2me | solution 1 for BianchiIX.volume_gaussCylinder_prefix
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:41:31.427346+00:00
-- url     : https://prove2.me/submissions/82144f4a-9427-43e3-9178-a573f062a3a1

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussDensity
import Theorems.Thm_BianchiIX_abs_deriv_gaussWord_prefix
import Theorems.Thm_BianchiIX_gaussDenoms_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_gaussWord_prefix
import Theorems.Thm_BianchiIX_measurableEmbedding_gaussWord
import Theorems.Thm_BianchiIX_volume_image_eq_lintegral_abs_deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal

private def BianchiIX.densityPrimitive (q p x : ℝ) : ℝ := x / (q * (q + p * x))

private theorem BianchiIX.hasDerivAt_densityPrimitive {q p x : ℝ}
    (hq : 0 < q) (hp : 0 ≤ p) (hx : 0 ≤ x) :
    HasDerivAt (densityPrimitive q p) (1 / (q + p * x) ^ 2) x := by
  have hd : 0 < q + p * x := by positivity
  have h := (hasDerivAt_id x).div
    ((((hasDerivAt_id x).const_mul p).const_add q).const_mul q) (mul_pos hq hd).ne'
  convert! h using 1
  dsimp only [id_eq]
  field_simp
  ring

private theorem BianchiIX.densityPrimitive_strictMonoOn {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) :
    StrictMonoOn (densityPrimitive q p) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hdx : 0 < q * (q + p * x) := by positivity
  have hdy : 0 < q * (q + p * y) := by positivity
  apply (div_lt_div_iff₀ hdx hdy).mpr
  nlinarith [mul_pos (sq_pos_of_pos hq) (sub_pos.mpr hxy)]

theorem solution (a : ℕ → ℕ+) (n : ℕ) :
    volume (gaussCylinder (digitPrefix a n)) = ENNReal.ofReal (gaussPrefixLength a n) := by
  let q := (gaussDenoms a n).1
  let p := (gaussDenoms a n).2
  have hq : 0 < q := by dsimp [q]; linarith [(gaussDenoms_bounds a n).1]
  have hp : 0 ≤ p := (gaussDenoms_bounds a n).2.1
  have hf (x : ℝ) (hx : 0 ≤ x) := hasDerivAt_densityPrimitive hq hp hx
  have hcont : ContinuousOn (densityPrimitive q p) (Icc 0 1) :=
    fun x hx => (hf x hx.1).continuousAt.continuousWithinAt
  have hmono := densityPrimitive_strictMonoOn hq hp
  have himg := hcont.image_Ioo_of_strictMonoOn zero_le_one (hmono.mono Icc_subset_Ici_self)
  have hG := volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
      (hasDerivAt_gaussWord_prefix a n hx.1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn
  change volume (gaussWord (digitPrefix a n) '' Ioo 0 1) = _
  rw [hG]
  have heq : (∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal |deriv (gaussWord (digitPrefix a n)) x|) =
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal |1 / (q + p * x) ^ 2| := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    dsimp only
    rw [abs_deriv_gaussWord_prefix a n hx.1.le, abs_of_nonneg (by positivity)]
    rfl
  rw [heq, ← volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo (0 : ℝ) 1) => hf x hx.1.le)
    (hmono.injOn.mono (fun _ ht => ht.1.le)), himg, Real.volume_Ioo]
  simp [densityPrimitive, gaussPrefixLength, q, p]
