-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialConcentration.concave_radial_gap_of_off_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/d4ae7b8a-dfe1-4873-b705-4141ae1e296f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialConcentration
theorem _root_.solution
    {n : ℕ} {f : Space n → ℝ}
    (hconc : ConcaveOn ℝ Set.univ f)
    (x₀ : Space n)
    {r η : ℝ} (hr : 0 < r)
    (hgap : ∀ x : Space n,
      x ∉ Metric.ball x₀ r → f x ≤ f x₀ - η)
    (x : Space n)
    (hx : r ≤ ‖x - x₀‖) :
    f x ≤ f x₀ - (η / r) * ‖x - x₀‖ := by
  let d : ℝ := ‖x - x₀‖
  let t : ℝ := r / d
  have hd : 0 < d := lt_of_lt_of_le hr hx
  have htpos : 0 < t := div_pos hr hd
  have htone : t ≤ 1 := (div_le_one hd).mpr hx
  let y : Space n := x₀ + t • (x - x₀)
  have hydist : dist y x₀ = r := by
    calc
      dist y x₀ = ‖t • (x - x₀)‖ := by
        dsimp [y]
        rw [dist_eq_norm]
        simp
      _ = t * d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      _ = r := by
        dsimp [t]
        exact div_mul_cancel₀ r hd.ne'
  have hyout : y ∉ Metric.ball x₀ r := by
    rw [Metric.mem_ball]
    exact not_lt.mpr (le_of_eq hydist.symm)
  have hsegle :
      (1 - t) * f x₀ + t * f x ≤ f y := by
    have hraw := hconc.2
      (Set.mem_univ x₀) (Set.mem_univ x)
      (sub_nonneg.mpr htone) htpos.le
      (show (1 - t) + t = 1 by ring)
    have hcomb : (1 - t) • x₀ + t • x = y := by
      dsimp [y]
      module
    rw [hcomb] at hraw
    simpa [smul_eq_mul] using hraw
  have hygap := hgap y hyout
  have htbound : t * (f x - f x₀) ≤ -η := by
    linarith
  have hquot : (r * (f x - f x₀)) / d ≤ -η := by
    calc
      (r * (f x - f x₀)) / d =
        t * (f x - f x₀) := by
          dsimp [t]
          ring
      _ ≤ -η := htbound
  have hscale : r * (f x - f x₀) ≤ -η * d :=
    (div_le_iff₀ hd).mp hquot
  have hratio : (η / r) * r = η :=
    div_mul_cancel₀ η hr.ne'
  nlinarith
end Ehrhart.BergmanJetMovingMonomialConcentration
