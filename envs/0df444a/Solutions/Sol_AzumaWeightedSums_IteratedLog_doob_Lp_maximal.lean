-- Prove2me | solution 1 for AzumaWeightedSums.IteratedLog.doob_Lp_maximal
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T08:07:40.033769+00:00
-- url     : https://prove2.me/submissions/dd19bb67-b8b0-4f05-a13e-9c3195732836

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory


open MeasureTheory

/-!
# Piece (A) of `AzumaWeightedSums.IteratedLog.doob_Lp_maximal` (verification-planner)

The layer-cake step of Doob's `L^α` maximal inequality, stated generically. `M` stands for
the running maximum `max_{m ≤ n} f_m` and `g` for `f_n`. The weak (Doob) inequality is a
hypothesis `hweak`. The owner derives it from `MeasureTheory.maximal_ineq` (piece (C)),
using `ofReal_setIntegral_eq_setLIntegral` below to rewrite its right-hand side.

Route, with ν = μ.withDensity (ofReal ∘ g) and no product-measure swap:
  ∫⁻ M^α dμ = α ∫⁻_{t>0} μ{t ≤ M} t^{α-1} dt                 (layer cake, μ, exponent α)
            ≤ α ∫⁻_{t>0} ν{t ≤ M} t^{α-2} dt                 (hweak: t·μ{t ≤ M} ≤ ν{t ≤ M})
            = α/(α-1) · ∫⁻ M^{α-1} dν                         (layer cake, ν, exponent α-1)
            = α/(α-1) · ∫⁻ g · M^{α-1} dμ.
-/

namespace AzumaWeightedSums.IteratedLog.DoobLayerCake

/-- The right-hand side of `maximal_ineq` as a set lower integral. -/
theorem ofReal_setIntegral_eq_setLIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) {g : Ω → ℝ} (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω) (S : Set Ω) :
    ENNReal.ofReal (∫ ω in S, g ω ∂μ) = ∫⁻ ω in S, ENNReal.ofReal (g ω) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal hg.integrableOn (Filter.Eventually.of_forall hg0)

/-- Layer-cake/Tonelli step (piece (A)). From the weak maximal inequality
`t · μ{t ≤ M} ≤ ∫⁻_{t ≤ M} g`, for every `t > 0`, it follows that
`∫⁻ M^α ≤ α/(α-1) · ∫⁻ g · M^{α-1}`, for every real `α > 1`. -/
theorem lintegral_rpow_le_of_weak_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ] {M g : Ω → ℝ}
    (hM : Measurable M) (hM0 : ∀ ω, 0 ≤ M ω) (hg : Measurable g)
    {α : ℝ} (hα : 1 < α)
    (hweak : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤ ∫⁻ ω in {ω | t ≤ M ω}, ENNReal.ofReal (g ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ ≤
      ENNReal.ofReal (α / (α - 1)) *
        ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (M ω ^ (α - 1)) ∂μ := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  have hgm : Measurable (fun ω => ENNReal.ofReal (g ω)) := ENNReal.measurable_ofReal.comp hg
  set ν : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (g ω)) with hν
  -- Layer cake for μ (exponent α) and for ν (exponent α - 1).
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hM0) hM.aemeasurable hα0
  have h2 := lintegral_rpow_eq_lintegral_meas_le_mul ν
    (Filter.Eventually.of_forall hM0) hM.aemeasurable hα1
  -- Pointwise comparison of the layer-cake integrands on `t > 0`.
  have hstep : ∀ t ∈ Set.Ioi (0 : ℝ),
      μ {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1)) ≤
        ν {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1 - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hS : MeasurableSet {a | t ≤ M a} := measurableSet_le measurable_const hM
    have hνS : ν {a | t ≤ M a} = ∫⁻ ω in {a | t ≤ M a}, ENNReal.ofReal (g ω) ∂μ := by
      rw [hν, withDensity_apply _ hS]
    have hsplit : t ^ (α - 1) = t * t ^ (α - 1 - 1) := by
      calc
        t ^ (α - 1) = t ^ ((1 : ℝ) + (α - 1 - 1)) := by ring_nf
        _ = t ^ (1 : ℝ) * t ^ (α - 1 - 1) := Real.rpow_add ht0 1 (α - 1 - 1)
        _ = t * t ^ (α - 1 - 1) := by rw [Real.rpow_one]
    rw [hsplit, ENNReal.ofReal_mul ht0.le, hνS]
    calc
      μ {a | t ≤ M a} * (ENNReal.ofReal t * ENNReal.ofReal (t ^ (α - 1 - 1)))
          = (ENNReal.ofReal t * μ {a | t ≤ M a}) * ENNReal.ofReal (t ^ (α - 1 - 1)) := by ring
      _ ≤ (∫⁻ ω in {a | t ≤ M a}, ENNReal.ofReal (g ω) ∂μ) *
            ENNReal.ofReal (t ^ (α - 1 - 1)) :=
          mul_le_mul_of_nonneg_right (hweak t ht0) zero_le
  have hmono : (∫⁻ t in Set.Ioi 0, μ {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1))) ≤
      ∫⁻ t in Set.Ioi 0, ν {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1 - 1)) :=
    setLIntegral_mono' measurableSet_Ioi hstep
  -- The `ν`-integral back as a `μ`-integral.
  have hν1 : ∫⁻ ω, ENNReal.ofReal (M ω ^ (α - 1)) ∂ν =
      ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (M ω ^ (α - 1)) ∂μ := by
    have hpm : Measurable (fun ω => ENNReal.ofReal (M ω ^ (α - 1))) :=
      ENNReal.measurable_ofReal.comp (hM.pow_const (α - 1))
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ hgm hpm]
    rfl
  have hc0 : ENNReal.ofReal (α - 1) ≠ 0 := (ENNReal.ofReal_pos.mpr hα1).ne'
  have hctop : ENNReal.ofReal (α - 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    ∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ
        = ENNReal.ofReal α *
            ∫⁻ t in Set.Ioi 0, μ {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1)) := h1
    _ ≤ ENNReal.ofReal α *
            ∫⁻ t in Set.Ioi 0, ν {a | t ≤ M a} * ENNReal.ofReal (t ^ (α - 1 - 1)) :=
        mul_le_mul_of_nonneg_left hmono zero_le
    _ = ENNReal.ofReal α *
          ((ENNReal.ofReal (α - 1))⁻¹ * ∫⁻ ω, ENNReal.ofReal (M ω ^ (α - 1)) ∂ν) := by
        congr 1
        rw [h2, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ = ENNReal.ofReal (α / (α - 1)) *
          ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (M ω ^ (α - 1)) ∂μ := by
        rw [hν1, ← mul_assoc, ENNReal.ofReal_div_of_pos hα1, div_eq_mul_inv]

end AzumaWeightedSums.IteratedLog.DoobLayerCake



open MeasureTheory

/- Source part: LpBridgePiece.lean -/
namespace NativeDoobLp

open MeasureTheory
open scoped ENNReal

theorem finiteMax_nonneg {Ω : Type*} (f : ℕ → Ω → ℝ)
    (hnonneg : ∀ m ω, 0 ≤ f m ω) (n : ℕ) (ω : Ω) :
    0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun m => f m ω) := by
  exact (hnonneg 0 ω).trans (Finset.le_sup' (fun m => f m ω)
    (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem finiteMax_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (hmeas : ∀ m, Measurable[mΩ] (f m)) (n : ℕ) :
    Measurable[mΩ] (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun m => f m ω)) := by
  exact Finset.measurable_range_sup'' (fun m _hm => hmeas m)

theorem submartingale_finiteMax_measurable {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (n : ℕ) :
    Measurable (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun m => f m ω)) := by
  exact finiteMax_measurable f
    (fun m => (hf.stronglyMeasurable m).measurable.le (ℱ.le m)) n

theorem finiteMax_moment_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (hmeas : ∀ m, Measurable[mΩ] (f m))
    (n : ℕ) (α : ℝ) :
    Measurable[mΩ] (fun ω => ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun m => f m ω)) ^ α)) := by
  exact ((finiteMax_measurable f hmeas n).pow_const α).ennreal_ofReal

theorem ofReal_rpow_eq_enorm_rpow {x α : ℝ}
    (hx : 0 ≤ x) (hα : 0 ≤ α) :
    ENNReal.ofReal (x ^ α) = ‖x‖ₑ ^ α := by
  calc
    ENNReal.ofReal (x ^ α) = ENNReal.ofReal x ^ α :=
      (ENNReal.ofReal_rpow_of_nonneg hx hα).symm
    _ = ‖x‖ₑ ^ α := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]

theorem lintegral_moment_eq_lintegral_enorm {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω) {α : ℝ} (hα : 0 ≤ α) :
    (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) = ∫⁻ ω, ‖g ω‖ₑ ^ α ∂μ := by
  apply lintegral_congr
  intro ω
  exact ofReal_rpow_eq_enorm_rpow (hg ω) hα

theorem lintegral_moment_eq_eLpNorm_rpow {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω) {α : ℝ} (hα : 0 < α) :
    (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) =
      eLpNorm g (ENNReal.ofReal α) μ ^ α := by
  have hp : ENNReal.ofReal α ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hα)
  rw [eLpNorm_eq_eLpNorm' hp ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hα.le]
  exact (lintegral_moment_eq_lintegral_enorm μ g hg hα.le).trans
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' hα)

theorem memLp_of_finite_moment {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure[mΩ] Ω) (g : Ω → ℝ)
    (hgmeas : AEStronglyMeasurable g μ) (hg : ∀ ω, 0 ≤ g ω)
    {α : ℝ} (hα : 0 < α)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) < ⊤) :
    MemLp g (ENNReal.ofReal α) μ := by
  refine ⟨hgmeas, ?_⟩
  have hp : ENNReal.ofReal α ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hα)
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hα.le]
  rw [← lintegral_moment_eq_lintegral_enorm μ g hg hα.le]
  exact hfinite

theorem lintegral_moment_eq_ofReal_integral {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω) (α : ℝ)
    (hint : Integrable (fun ω => g ω ^ α) μ) :
    (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) =
      ENNReal.ofReal (∫ ω, g ω ^ α ∂μ) := by
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hg ω) α))).symm

theorem moment_bound_of_eLpNorm_bound {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (g h : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω) (hh : ∀ ω, 0 ≤ h ω)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (hnorm : eLpNorm g (ENNReal.ofReal α) μ ≤
      ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal α) μ) :
    (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ≤
      ENNReal.ofReal (C ^ α) * ∫⁻ ω, ENNReal.ofReal (h ω ^ α) ∂μ := by
  rw [lintegral_moment_eq_eLpNorm_rpow μ g hg hα,
    lintegral_moment_eq_eLpNorm_rpow μ h hh hα]
  calc
    eLpNorm g (ENNReal.ofReal α) μ ^ α ≤
        (ENNReal.ofReal C * eLpNorm h (ENNReal.ofReal α) μ) ^ α :=
      ENNReal.rpow_le_rpow hnorm hα.le
    _ = ENNReal.ofReal (C ^ α) * eLpNorm h (ENNReal.ofReal α) μ ^ α := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le,
        ENNReal.ofReal_rpow_of_nonneg hC hα.le]

theorem finiteMax_moment_bound_of_eLpNorm_bound {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (f : ℕ → Ω → ℝ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    (n : ℕ) {α : ℝ} (hα : 1 < α)
    (hnorm : eLpNorm
      (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun m => f m ω)) (ENNReal.ofReal α) μ ≤
      ENNReal.ofReal (α / (α - 1)) * eLpNorm (f n) (ENNReal.ofReal α) μ) :
    (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun m => f m ω)) ^ α) ∂μ) ≤
      ENNReal.ofReal ((α / (α - 1)) ^ α) *
        ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  exact moment_bound_of_eLpNorm_bound μ
    (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun m => f m ω)) (f n)
    (finiteMax_nonneg f hnonneg n) (hnonneg n) hα0
    (div_nonneg hα0.le (sub_nonneg.mpr hα.le)) hnorm

end NativeDoobLp

/- Source part: InfinityPiece.lean -/
open MeasureTheory
open scoped ENNReal

namespace IndependentDoob

/-- The exact real-exponent constant in Doob's inequality is strictly positive. -/
theorem doob_coefficient_pos {α : ℝ} (hα : 1 < α) :
    0 < ENNReal.ofReal ((α / (α - 1)) ^ α) := by
  apply ENNReal.ofReal_pos.mpr
  exact Real.rpow_pos_of_pos (div_pos (by linarith) (sub_pos.mpr hα)) α

/-- The infinite-terminal-moment branch requires no finite-moment assumption. -/
theorem maximal_moment_le_of_terminal_eq_top
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (f : ℕ → Ω → ℝ) (n : ℕ) {α : ℝ} (hα : 1 < α)
    (htop : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) = ∞) :
    (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ) ≤
      ENNReal.ofReal ((α / (α - 1)) ^ α) *
        ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  rw [htop, ENNReal.mul_top (ne_of_gt (doob_coefficient_pos hα))]
  exact le_top

/-- A finite-case proof can be assembled without strengthening the public assumptions. -/
theorem maximal_moment_le_of_finite_case
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (f : ℕ → Ω → ℝ) (n : ℕ) {α : ℝ} (hα : 1 < α)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) < ∞ →
      (∫⁻ ω, ENNReal.ofReal
        (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ) ≤
        ENNReal.ofReal ((α / (α - 1)) ^ α) *
          ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) :
    (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ) ≤
      ENNReal.ofReal ((α / (α - 1)) ^ α) *
        ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) = ∞
  · exact maximal_moment_le_of_terminal_eq_top μ f n hα htop
  · exact hfinite (lt_top_iff_ne_top.mpr htop)

end IndependentDoob

/- Source part: Holder.lean -/
namespace NativeDoobLp

open MeasureTheory
open scoped ENNReal

theorem mixedMoment_integrand_eq_weighted {x y α : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hα : 1 < α) :
    ENNReal.ofReal (x * y ^ (α - 1)) =
      (‖x‖ₑ ^ α) ^ (1 / α) * (‖y‖ₑ ^ α) ^ ((α - 1) / α) := by
  have hαne : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  have hfirst : α * (1 / α) = 1 := by
    rw [one_div, mul_inv_cancel₀ hαne]
  have hsecond : α * ((α - 1) / α) = α - 1 := by
    calc
      α * ((α - 1) / α) = (α - 1) * (α / α) := by ring
      _ = α - 1 := by rw [div_self hαne, mul_one]
  have hnorm : ENNReal.ofReal x = ‖x‖ₑ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hx]
  rw [ENNReal.ofReal_mul hx, hnorm,
    ofReal_rpow_eq_enorm_rpow hy (sub_nonneg.mpr hα.le),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hfirst, hsecond, ENNReal.rpow_one]

theorem lintegral_mixed_moment_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure[mΩ] Ω) (g h : Ω → ℝ)
    (hgmeas : AEMeasurable g μ) (hhmeas : AEMeasurable h μ)
    (hg : ∀ ω, 0 ≤ g ω) (hh : ∀ ω, 0 ≤ h ω)
    {α : ℝ} (hα : 1 < α) :
    (∫⁻ ω, ENNReal.ofReal (g ω * h ω ^ (α - 1)) ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
        (∫⁻ ω, ENNReal.ofReal (h ω ^ α) ∂μ) ^ ((α - 1) / α) := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hp : 0 ≤ 1 / α := div_nonneg zero_le_one hα0.le
  have hq : 0 ≤ (α - 1) / α :=
    div_nonneg (sub_nonneg.mpr hα.le) hα0.le
  have hpq : 1 / α + (α - 1) / α = 1 := by
    calc
      1 / α + (α - 1) / α = α / α := by ring
      _ = 1 := div_self hα0.ne'
  calc
    (∫⁻ ω, ENNReal.ofReal (g ω * h ω ^ (α - 1)) ∂μ) =
        ∫⁻ ω, (‖g ω‖ₑ ^ α) ^ (1 / α) *
          (‖h ω‖ₑ ^ α) ^ ((α - 1) / α) ∂μ := by
      apply lintegral_congr
      intro ω
      exact mixedMoment_integrand_eq_weighted (hg ω) (hh ω) hα
    _ ≤ (∫⁻ ω, ‖g ω‖ₑ ^ α ∂μ) ^ (1 / α) *
        (∫⁻ ω, ‖h ω‖ₑ ^ α ∂μ) ^ ((α - 1) / α) :=
      ENNReal.lintegral_mul_norm_pow_le
        (hgmeas.enorm.pow_const α) (hhmeas.enorm.pow_const α) hp hq hpq
    _ = (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
        (∫⁻ ω, ENNReal.ofReal (h ω ^ α) ∂μ) ^ ((α - 1) / α) := by
      rw [← lintegral_moment_eq_lintegral_enorm μ g hg hα0.le,
        ← lintegral_moment_eq_lintegral_enorm μ h hh hα0.le]

theorem lintegral_mul_ofReal_rpow_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure[mΩ] Ω) (g h : Ω → ℝ)
    (hgmeas : AEMeasurable g μ) (hhmeas : AEMeasurable h μ)
    (hg : ∀ ω, 0 ≤ g ω) (hh : ∀ ω, 0 ≤ h ω)
    {α : ℝ} (hα : 1 < α) :
    (∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (h ω ^ (α - 1)) ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
        (∫⁻ ω, ENNReal.ofReal (h ω ^ α) ∂μ) ^ ((α - 1) / α) := by
  calc
    (∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (h ω ^ (α - 1)) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (g ω * h ω ^ (α - 1)) ∂μ := by
      apply lintegral_congr
      intro ω
      exact (ENNReal.ofReal_mul (hg ω)).symm
    _ ≤ (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
        (∫⁻ ω, ENNReal.ofReal (h ω ^ α) ∂μ) ^ ((α - 1) / α) :=
      lintegral_mixed_moment_le μ g h hgmeas hhmeas hg hh hα

end NativeDoobLp

/- Source part: Finiteness.lean -/
namespace NativeDoobLp

open MeasureTheory
open scoped ENNReal

/-- Conditional-expectation contraction transfers terminal Lp membership to an earlier
nonnegative submartingale value. -/
theorem submartingale_memLp_before_terminal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (n : ℕ) (hterminal : MemLp (f n) p μ)
    {i : ℕ} (hi : i ≤ n) :
    MemLp (f i) p μ := by
  have hcond : MemLp (condExp (ℱ i) μ (f n)) p μ :=
    hterminal.condExp (m := ℱ i) hp
  apply hcond.mono ((hf.stronglyMeasurable i).mono (ℱ.le i)).aestronglyMeasurable
  filter_upwards [hf.2.1 i n hi] with ω hω
  change |f i ω| ≤ |condExp (ℱ i) μ (f n) ω|
  rw [abs_of_nonneg (hnonneg i ω)]
  exact hω.trans (le_abs_self _)

/-- Finite sums dominate the literal finite maximum, so no maximum-closure API is needed. -/
theorem finiteMax_memLp_of_terminal_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hterminal : MemLp (f n) p μ) :
    MemLp (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun m => f m ω)) p μ := by
  have hsum : MemLp (fun ω => ∑ i ∈ Finset.range (n + 1), f i ω) p μ := by
    refine memLp_finsetSum (Finset.range (n + 1)) ?_
    intro i hi
    exact submartingale_memLp_before_terminal hf hnonneg hp n hterminal
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  apply hsum.mono' (submartingale_finiteMax_measurable hf n).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteMax_nonneg f hnonneg n ω)]
  apply (Finset.sup'_le_iff Finset.nonempty_range_add_one _).2
  intro i hi
  exact Finset.single_le_sum (fun j _hj => hnonneg j ω) hi

/-- The finite-terminal-moment branch supplies Lp membership of the exact frozen maximum. -/
theorem finiteMax_memLp_of_finite_terminal_moment {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    (n : ℕ) {α : ℝ} (hα : 1 < α)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) < ⊤) :
    MemLp (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun m => f m ω)) (ENNReal.ofReal α) μ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal α := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hα.le
  have hterminal : MemLp (f n) (ENNReal.ofReal α) μ :=
    memLp_of_finite_moment μ (f n)
      ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
      (hnonneg n) hα0 hfinite
  exact finiteMax_memLp_of_terminal_memLp hf hnonneg n hp hterminal

/-- A finite terminal alpha moment forces the finite maximum's alpha moment to be finite.
This is an internal finite-moment branch, not a new hypothesis on Doob's final inequality. -/
theorem finiteMax_moment_lt_top_of_finite_terminal_moment {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    (n : ℕ) {α : ℝ} (hα : 1 < α)
    (hfinite : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) < ⊤) :
    (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun m => f m ω)) ^ α) ∂μ) < ⊤ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hp0 : ENNReal.ofReal α ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hα0)
  have hmax := finiteMax_memLp_of_finite_terminal_moment hf hnonneg n hα hfinite
  have hnorm := hmax.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hα0.le] at hnorm
  rw [lintegral_moment_eq_lintegral_enorm μ
    (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun m => f m ω)) (finiteMax_nonneg f hnonneg n) hα0.le]
  exact hnorm

end NativeDoobLp

/- Source part: Cancellation.lean -/
namespace NativeDoobLp

open scoped ENNReal

/-- Finite maximal-moment cancellation after the layer-cake and Holder estimates. -/
theorem moment_bound_of_mixed_bound {α : ℝ} (hα : 1 < α)
    {H T C : ℝ≥0∞} (hHfinite : H < ∞)
    (h : H ≤ C * T ^ (1 / α) * H ^ ((α - 1) / α)) :
    H ≤ C ^ α * T := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have ha : 0 < 1 / α := one_div_pos.mpr hα0
  have hb : 0 < (α - 1) / α := div_pos (sub_pos.mpr hα) hα0
  have hab : 1 / α + (α - 1) / α = 1 := by
    calc
      1 / α + (α - 1) / α = (1 + (α - 1)) / α := (add_div _ _ _).symm
      _ = α / α := by congr 1; ring
      _ = 1 := div_self (ne_of_gt hα0)
  by_cases hH0 : H = 0
  · subst H
    exact zero_le
  · have hpow0 : H ^ ((α - 1) / α) ≠ 0 :=
      ne_of_gt (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hH0) hHfinite.ne)
    have hpowtop : H ^ ((α - 1) / α) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hb.le hHfinite.ne
    have hdecomp : H ^ (1 / α) * H ^ ((α - 1) / α) = H := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb.le, hab, ENNReal.rpow_one]
    have hmul : H ^ (1 / α) * H ^ ((α - 1) / α) ≤
        (C * T ^ (1 / α)) * H ^ ((α - 1) / α) := by
      calc
        _ = H := hdecomp
        _ ≤ _ := h
    have hroot : H ^ (1 / α) ≤ C * T ^ (1 / α) :=
      (ENNReal.mul_le_mul_iff_left hpow0 hpowtop).mp hmul
    have hinv : (1 / α) * α = 1 := by
      exact one_div_mul_cancel (ne_of_gt hα0)
    calc
      H = (H ^ (1 / α)) ^ α := by
        rw [← ENNReal.rpow_mul, hinv, ENNReal.rpow_one]
      _ ≤ (C * T ^ (1 / α)) ^ α := ENNReal.rpow_le_rpow hroot hα0.le
      _ = C ^ α * T := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le,
          ← ENNReal.rpow_mul, hinv, ENNReal.rpow_one]

end NativeDoobLp

/- Source part: PieceB.lean -/
namespace NativeDoobLp

open MeasureTheory
open scoped ENNReal

/-- Piece B: the preliminary layer-cake estimate and Holder imply the sharp moment bound. -/
theorem moment_bound_of_layercake {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure[mΩ] Ω) (g M : Ω → ℝ)
    (hgmeas : AEMeasurable g μ) (hMmeas : AEMeasurable M μ)
    (hg0 : ∀ ω, 0 ≤ g ω) (hM0 : ∀ ω, 0 ≤ M ω)
    {α : ℝ} (hα : 1 < α)
    (hMfinite : (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) < ∞)
    (hpre : (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) ≤
      ENNReal.ofReal (α / (α - 1)) *
        ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (M ω ^ (α - 1)) ∂μ) :
    (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) ≤
      ENNReal.ofReal ((α / (α - 1)) ^ α) *
        ∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hc : 0 ≤ α / (α - 1) :=
    div_nonneg hα0.le (sub_nonneg.mpr hα.le)
  have hholder := lintegral_mul_ofReal_rpow_le μ g M hgmeas hMmeas hg0 hM0 hα
  have hcombined : (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) ≤
      ENNReal.ofReal (α / (α - 1)) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
        (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) ^ ((α - 1) / α) := by
    calc
      _ ≤ ENNReal.ofReal (α / (α - 1)) *
          (∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (M ω ^ (α - 1)) ∂μ) := hpre
      _ ≤ ENNReal.ofReal (α / (α - 1)) *
          ((∫⁻ ω, ENNReal.ofReal (g ω ^ α) ∂μ) ^ (1 / α) *
            (∫⁻ ω, ENNReal.ofReal (M ω ^ α) ∂μ) ^ ((α - 1) / α)) :=
        mul_le_mul_of_nonneg_left hholder zero_le
      _ = _ := (mul_assoc _ _ _).symm
  simpa only [ENNReal.ofReal_rpow_of_nonneg hc hα0.le] using
    moment_bound_of_mixed_bound hα hMfinite hcombined

/-- Piece B for the exact finite maximum: the terminal moment is never assumed finite publicly. -/
theorem doob_moment_bound_of_layercake {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure[mΩ] Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω)
    (n : ℕ) {α : ℝ} (hα : 1 < α)
    (hpre : (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ) ≤
      ENNReal.ofReal (α / (α - 1)) * ∫⁻ ω,
        ENNReal.ofReal (f n ω) * ENNReal.ofReal
          (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            (fun m => f m ω)) ^ (α - 1)) ∂μ) :
    (∫⁻ ω, ENNReal.ofReal
      (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ) ≤
      ENNReal.ofReal ((α / (α - 1)) ^ α) *
        ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) = ∞
  · exact IndependentDoob.maximal_moment_le_of_terminal_eq_top μ f n hα htop
  · have hfinite : (∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ) < ∞ :=
      lt_top_iff_ne_top.mpr htop
    have hmaxfinite := finiteMax_moment_lt_top_of_finite_terminal_moment
      hf hnonneg n hα hfinite
    exact moment_bound_of_layercake μ (f n)
      (fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω))
      (((hf.stronglyMeasurable n).mono (ℱ.le n)).measurable.aemeasurable)
      (submartingale_finiteMax_measurable hf n).aemeasurable
      (hnonneg n) (finiteMax_nonneg f hnonneg n) hα hmaxfinite hpre

end NativeDoobLp



open MeasureTheory

namespace AzumaWeightedSums.IteratedLog

/-- Doob's `L^α` maximal inequality for nonnegative submartingales, as cited by Azuma 1967
(proof of Lemma 2, p. 359, from Doob, *Stochastic Processes*, p. 317): for a nonnegative
submartingale `(f_m)`, every `n` and every real `α > 1`,
`E{(max_{m ≤ n} f_m)^α} ≤ (α/(α−1))^α E{f_n^α}`. -/
theorem doob_Lp_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω) (n : ℕ) {α : ℝ} (hα : 1 < α) :
    ∫⁻ ω, ENNReal.ofReal
        (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ
      ≤ ENNReal.ofReal ((α / (α - 1)) ^ α) * ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  apply NativeDoobLp.doob_moment_bound_of_layercake hf hnonneg n hα
  apply DoobLayerCake.lintegral_rpow_le_of_weak_maximal μ
    (NativeDoobLp.submartingale_finiteMax_measurable hf n)
    (NativeDoobLp.finiteMax_nonneg f hnonneg n)
    ((hf.stronglyMeasurable n).measurable.le (ℱ.le n)) hα
  intro t ht
  have hw := MeasureTheory.maximal_ineq hf hnonneg (ε := ⟨t, ht.le⟩) n
  rw [DoobLayerCake.ofReal_setIntegral_eq_setLIntegral μ
    (hf.integrable n) (hnonneg n)] at hw
  rw [ENNReal.ofReal_eq_coe_nnreal ht.le]
  exact hw

end AzumaWeightedSums.IteratedLog

end Prove2SwarmSubmission

open MeasureTheory
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ μ) (hnonneg : ∀ m ω, 0 ≤ f m ω) (n : ℕ) {α : ℝ} (hα : 1 < α) :
    ∫⁻ ω, ENNReal.ofReal
        (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun m => f m ω)) ^ α) ∂μ
      ≤ ENNReal.ofReal ((α / (α - 1)) ^ α) * ∫⁻ ω, ENNReal.ofReal (f n ω ^ α) ∂μ := by
  exact Prove2SwarmSubmission.AzumaWeightedSums.IteratedLog.doob_Lp_maximal hf hnonneg n hα
