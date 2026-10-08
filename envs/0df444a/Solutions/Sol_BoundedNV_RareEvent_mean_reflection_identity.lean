-- Prove2me | solution 1 for BoundedNV.RareEvent.mean_reflection_identity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:00:59.437729+00:00
-- url     : https://prove2.me/submissions/e290295c-98bc-4498-bbeb-acc8a88cbe10

import Mathlib
import Definitions.Def_BoundedNV_RareEvent_Logit
open MeasureTheory
private lemma reflect_integral (F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (hmass : (∫ x in a..b, F x) = 1) :
    (∫ x in a..b, x * F x) =
      (a+b)/2 + ∫ v in (0:ℝ)..((b-a)/2), v*(F ((a+b)/2+v)-F ((a+b)/2-v)) := by
  let m := (a+b)/2
  let r := (b-a)/2
  let G := fun x => (x-m)*F x
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hG : ContinuousOn G (Set.Icc a b) := (continuousOn_id.sub continuousOn_const).mul hF
  have hGi : IntervalIntegrable G volume a b := hG.intervalIntegrable_of_Icc hab.le
  have hGa : IntervalIntegrable G volume a m :=
    (hG.mono (Set.Icc_subset_Icc le_rfl hmb)).intervalIntegrable_of_Icc ham
  have hGb : IntervalIntegrable G volume m b :=
    (hG.mono (Set.Icc_subset_Icc ham le_rfl)).intervalIntegrable_of_Icc hmb
  have hplus : (∫ v in (0:ℝ)..r, G (m+v)) = ∫ x in m..b, G x := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> dsimp [m,r] <;> ring
  have hminus : (∫ v in (0:ℝ)..r, G (m-v)) = ∫ x in a..m, G x := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> dsimp [m,r] <;> ring
  have hip : IntervalIntegrable (fun v => G (m+v)) volume 0 r := by
    have h := hGb.comp_add_left m
    convert h using 1 <;> dsimp [m,r] <;> ring
  have him : IntervalIntegrable (fun v => G (m-v)) volume 0 r := by
    have h := hGa.comp_sub_left m
    convert h.symm using 1 <;> dsimp [m,r] <;> ring
  have hcenter : (∫ x in a..b, G x) =
      ∫ v in (0:ℝ)..r, v*(F (m+v)-F (m-v)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hGa hGb, ← hplus, ← hminus,
      ← intervalIntegral.integral_add him hip]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp [G]
    ring
  have hFi : IntervalIntegrable F volume a b := hF.intervalIntegrable_of_Icc hab.le
  have hdecomp : (∫ x in a..b, x*F x) = m + ∫ x in a..b, G x := by
    calc
      _ = ∫ x in a..b, m*F x + G x := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [G]
        ring
      _ = m*(∫ x in a..b, F x) + ∫ x in a..b, G x := by
        rw [intervalIntegral.integral_add (hFi.const_mul m) hGi, intervalIntegral.integral_const_mul]
      _ = _ := by rw [hmass]; ring
  rw [hdecomp,hcenter]

theorem solution (u : ℝ → ℝ) (β a b : ℝ)
    (hβ : 0 < β) (hab : a < b)
    (hu : ContinuousOn u (Set.Icc a b)) :
    BoundedNV.Uniform.logitExp (Set.Icc a b) u β id =
      (a + b) / 2 + ∫ v in (0 : ℝ)..((b - a) / 2),
        v * (BoundedNV.Uniform.logitDensity (Set.Icc a b) u β ((a + b) / 2 + v) -
          BoundedNV.Uniform.logitDensity (Set.Icc a b) u β ((a + b) / 2 - v)) := by
  classical
  let E := fun x => Real.exp (u x / β)
  let Z := ∫ x in Set.Icc a b, E x
  let F := fun x => E x / Z
  have hE : ContinuousOn E (Set.Icc a b) := Real.continuous_exp.comp_continuousOn (hu.div_const β)
  have hZi : Z = ∫ x in a..b, E x := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  have hZ : 0 < Z := by
    rw [hZi]
    apply intervalIntegral.integral_pos hab hE
    · intro x hx
      exact (Real.exp_pos _).le
    · exact ⟨a, ⟨le_rfl,hab.le⟩,Real.exp_pos _⟩
  have hF : ContinuousOn F (Set.Icc a b) := hE.div_const Z
  have hmass : (∫ x in a..b, F x) = 1 := by
    dsimp [F]
    rw [intervalIntegral.integral_div, ← hZi, div_self hZ.ne']
  have hmean : BoundedNV.Uniform.logitExp (Set.Icc a b) u β id =
      ∫ x in a..b, x*F x := by
    unfold BoundedNV.Uniform.logitExp BoundedNV.Uniform.logitDensity
    have he : (fun y => id y * (Set.Icc a b).indicator F y) =
        (Set.Icc a b).indicator (fun y => y*F y) := by
      ext y
      by_cases hy : y ∈ Set.Icc a b <;> simp [hy]
    change (∫ y, id y * (Set.Icc a b).indicator F y) = _
    rw [he, MeasureTheory.integral_indicator measurableSet_Icc,
      intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  rw [hmean, reflect_integral F a b hab hF hmass]
  congr 1
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Set.Icc 0 ((b-a)/2) := by
    simpa [Set.uIcc_of_le (show (0:ℝ) ≤ (b-a)/2 by linarith)] using hv
  have hp : (a+b)/2+v ∈ Set.Icc a b := by constructor <;> linarith [hv'.1,hv'.2]
  have hm : (a+b)/2-v ∈ Set.Icc a b := by constructor <;> linarith [hv'.1,hv'.2]
  simp [BoundedNV.Uniform.logitDensity, hp, hm, F, E, Z]
#print axioms solution
