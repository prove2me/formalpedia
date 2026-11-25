-- Prove2me | solution 1 for Erdos679.gap_from_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:20.473089+00:00
-- url     : https://prove2.me/submissions/95258687-a960-40d5-9e36-036631bd4061

module
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos679_Gap

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (θ : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hupper : ∀ᶠ m : ℕ in atTop,
      θ m ≤ m * (log m + log (log m) - δ))
    (hlower : ∀ᶠ m : ℕ in atTop, m * (log m - 2) < θ m) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, θ m / log (θ m) + C < m := by
  let C₀ := max C 0
  have hC : 0 ≤ C₀ := le_max_right _ _
  have hL : Tendsto (fun m : ℕ => log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun m : ℕ => log (m : ℝ) / m) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hsmall := (hratio.const_mul (2 * C₀)).eventually
    (gt_mem_nhds (show 2 * C₀ * (0 : ℝ) < δ / 4 by nlinarith))
  have hinv : Tendsto (fun m : ℕ => 2 / log (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hlog : Tendsto (fun m : ℕ => log (1 - 2 / log (m : ℝ)))
      atTop (𝓝 0) := by
    have hsub := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv
    simpa using hsub.log (by norm_num)
  have hlogbound := hlog.eventually (lt_mem_nhds (by linarith : -δ / 2 < (0 : ℝ)))
  have hlarge := tendsto_natCast_atTop_atTop.eventually_gt_atTop C₀
  filter_upwards [hupper, hlower, hsmall, hlogbound, hL.eventually_gt_atTop 3,
    hlarge, eventually_ge_atTop (1 : ℕ)] with m hu hl hs hlogb hLm hmC hm1
  have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < m := by linarith
  have hLp : 0 < log (m : ℝ) := by linarith
  have hloglog : log (log (m : ℝ)) ≤ log m :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hs' : 2 * C₀ * log (m : ℝ) < (δ / 4) * m := by
    apply (div_lt_iff₀ hmpos).mp
    simpa only [mul_div_assoc] using hs
  have hCA : C₀ * (log (m : ℝ) + log (log m)) < (δ / 4) * m := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hloglog)]
  have hbase : 0 < (m : ℝ) * (log m - 2) := mul_pos hmpos (by linarith)
  have hθone : 1 < θ m := by nlinarith
  have hfactor : 0 < 1 - 2 / log (m : ℝ) := by
    have : 2 / log (m : ℝ) < 1 := (div_lt_one hLp).mpr (by linarith)
    linarith
  have heq : log ((m : ℝ) * (log m - 2)) =
      log m + log (log m) + log (1 - 2 / log m) := by
    have heq' : (m : ℝ) * (log m - 2) = m * log m * (1 - 2 / log m) := by
      field_simp [hLp.ne']
    rw [heq', Real.log_mul (mul_ne_zero hmpos.ne' hLp.ne') hfactor.ne',
      Real.log_mul hmpos.ne' hLp.ne']
  have hθlog := Real.log_lt_log hbase hl
  rw [heq] at hθlog
  have hθlower : log (m : ℝ) + log (log m) - δ / 2 < log (θ m) := by
    linarith
  have hbound : θ m < ((m : ℝ) - C₀) * log (θ m) := by
    calc
      θ m ≤ m * (log m + log (log m) - δ) := hu
      _ < (m - C₀) * (log m + log (log m) - δ / 2) := by
        nlinarith [mul_nonneg hC hδ.le, mul_pos hδ hmpos]
      _ < (m - C₀) * log (θ m) :=
        mul_lt_mul_of_pos_left hθlower (by linarith)
  have hdiv := (div_lt_iff₀ (Real.log_pos hθone)).mpr hbound
  have hCC : C ≤ C₀ := le_max_left _ _
  linarith
end Erdos679
