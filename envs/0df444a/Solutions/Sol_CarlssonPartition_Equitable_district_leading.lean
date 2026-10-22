-- Prove2me | solution 1 for CarlssonPartition.Equitable.district_leading
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:44:25.04775+00:00
-- url     : https://prove2.me/submissions/08d1231a-c28f-4af0-a4bb-85310cbc3bac

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

set_option autoImplicit false
open Filter Topology MeasureTheory CarlssonPartition.Equitable

namespace CARHelp

theorem facts (I : Instance) (hI : I.Standing) (S : Set Plane) (hSR : S ⊆ I.R) :
    IntegrableOn I.f S ∧ IntegrableOn (fun x => ‖x - I.x0‖ * I.f x) S := by
  have hint : IntegrableOn I.f I.R := by
    by_contra h
    have := hI.2.2.2.2.2.1
    rw [integral_undef h] at this
    exact zero_ne_one this
  obtain ⟨K, hK⟩ := hI.2.2.2.2.1
  have hcont : ContinuousOn I.f I.R := hK.continuousOn
  have hc2 : ContinuousOn (fun x => ‖x - I.x0‖ * I.f x) I.R :=
    ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn).mul hcont
  exact ⟨hint.mono_set hSR, (hc2.integrableOn_compact hI.1).mono_set hSR⟩

theorem expand (I : Instance) (hI : I.Standing) (S : Set Plane) (hSR : S ⊆ I.R) :
    (∫ x in S, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = I.sbar * I.v * (I.q : ℝ) * (∫ x in S, I.f x) + 2 * ∫ x in S, ‖x - I.x0‖ * I.f x := by
  obtain ⟨h1, h2⟩ := facts I hI S hSR
  have : (fun x => (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = fun x => I.sbar * I.v * (I.q : ℝ) * I.f x + 2 * (‖x - I.x0‖ * I.f x) := by
    funext x; ring
  rw [this, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]

theorem wl (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs) (i : Fin I.m)
    (h2 : (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (hpos : 0 < I.pr (Rs i)) (lam : ℝ) :
    I.workload 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
      = I.workload I.m lam I.R I.f := by
  have hsub : Rs i ⊆ I.R := hP.2.2 ▸ Set.subset_iUnion Rs i
  have hv : 0 < I.v := hI.2.2.2.2.2.2.2.1
  have hq : (1 : ℝ) ≤ I.q := by exact_mod_cast hI.2.2.2.2.2.2.2.2.1
  have hm : (1 : ℝ) ≤ I.m := by exact_mod_cast hI.2.2.2.2.2.2.1
  have hone : (∫ x in I.R, I.f x) = 1 := hI.2.2.2.2.2.1
  rw [expand I hI _ hsub, expand I hI _ subset_rfl, hone] at h2
  have hJ : (∫ x in Rs i, ‖x - I.x0‖ * I.fSub (Rs i) x) = (∫ x in Rs i, ‖x - I.x0‖ * I.f x) / I.pr (Rs i) := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Instance.fSub]
    ring
  unfold Instance.workload Instance.lamSub
  rw [hJ]
  unfold Instance.pr at hpos ⊢
  generalize (∫ x in Rs i, I.f x) = p at *
  generalize (∫ x in Rs i, ‖x - I.x0‖ * I.f x) = Ji at *
  generalize (∫ x in I.R, ‖x - I.x0‖ * I.f x) = J at *
  have hvq : I.v * (I.q : ℝ) ≠ 0 := by positivity
  have hm0 : (I.m : ℝ) ≠ 0 := by positivity
  field_simp
  field_simp at h2
  push_cast
  linear_combination lam * h2

end CARHelp

theorem solution (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs) (i : Fin I.m)
    (h1 : (∫ x in Rs i, Real.sqrt (I.f x)) = (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (hpos : 0 < I.pr (Rs i)) (lam : ℝ) :
    I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) = I.bvrLeading I.m lam I.R I.f := by
  have hW := CARHelp.wl I hI Rs hP i h2 hpos lam
  have hs : (∫ x in Rs i, Real.sqrt (I.fSub (Rs i) x)) = (∫ x in Rs i, Real.sqrt (I.f x)) / Real.sqrt (I.pr (Rs i)) := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Instance.fSub]
    rw [Real.sqrt_div' _ hpos.le]
  have hm : (1 : ℝ) ≤ I.m := by exact_mod_cast hI.2.2.2.2.2.2.1
  have hv : 0 < I.v := hI.2.2.2.2.2.2.2.1
  unfold Instance.bvrLeading
  rw [hW, hs, h1]
  unfold Instance.lamSub
  generalize (∫ x in I.R, Real.sqrt (I.f x)) = SS
  generalize (1 - I.workload I.m lam I.R I.f) ^ 2 = D
  have hsq : Real.sqrt (I.pr (Rs i)) ^ 2 = I.pr (Rs i) := Real.sq_sqrt hpos.le
  have hp0 : I.pr (Rs i) ≠ 0 := hpos.ne'
  have hs0 : Real.sqrt (I.pr (Rs i)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hm0 : (I.m : ℝ) ≠ 0 := by positivity
  rcases eq_or_ne D 0 with hD | hD
  · simp [hD]
  · push_cast
    field_simp
    rw [hsq]
    ring
