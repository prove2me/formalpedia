-- Prove2me | solution 1 for Ehrhart.JetAsymptotics.tendsto_choose_floor_mul_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/1b8c586d-aee0-4907-88ed-025ce9b9ae8c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetAsymptotics_tendsto_shifted_floor_mul_div_nat

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology
namespace Ehrhart.JetAsymptotics
theorem _root_.solution
    (r b : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
          (k : ℝ) ^ r)
      atTop (𝓝 (t ^ r / (r.factorial : ℝ))) := by
  have hshift :
      Tendsto (fun k : ℕ => Nat.floor (t * (k : ℝ)) + b)
        atTop atTop :=
    (tendsto_add_atTop_nat b).comp
      (tendsto_nat_floor_mul_atTop t ht)
  have hequiv :
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ))
        ~[atTop]
      (fun k : ℕ =>
        (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
          (r.factorial : ℝ))) := by
    simpa [Function.comp_def] using
      (isEquivalent_choose r).comp_tendsto hshift
  have hnonzero : ∀ᶠ k : ℕ in atTop,
      ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
        (r.factorial : ℝ) ≠ 0 := by
    filter_upwards [hshift.eventually (eventually_ge_atTop (1 : ℕ))]
      with k hk
    have hm : 0 < Nat.floor (t * (k : ℝ)) + b :=
      lt_of_lt_of_le Nat.zero_lt_one hk
    positivity
  have hratio :
      Tendsto
        (fun k : ℕ =>
          (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (r.factorial : ℝ)))
        atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hnonzero).mp hequiv
  have hscale := tendsto_shifted_floor_mul_div_nat ht.le b
  have hcombined := (hratio.mul (hscale.pow r)).div_const
    (r.factorial : ℝ)
  have htarget :
      Tendsto
        (fun k : ℕ =>
          (((Nat.floor (t * (k : ℝ)) + b).choose r : ℕ) : ℝ) /
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (r.factorial : ℝ)) *
            (((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ^ r /
              (k : ℝ) ^ r) /
            (r.factorial : ℝ))
        atTop (𝓝 (t ^ r / (r.factorial : ℝ))) := by
    convert hcombined using 1 <;> simp [div_pow]
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hshift.eventually (eventually_ge_atTop (1 : ℕ))]
      with k hk hm
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hmne :
      ((Nat.floor (t * (k : ℝ)) + b : ℕ) : ℝ) ≠ 0 := by
    have hmpos : 0 < Nat.floor (t * (k : ℝ)) + b :=
      lt_of_lt_of_le Nat.zero_lt_one hm
    exact_mod_cast Nat.ne_of_gt hmpos
  have hfact : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp
end Ehrhart.JetAsymptotics
