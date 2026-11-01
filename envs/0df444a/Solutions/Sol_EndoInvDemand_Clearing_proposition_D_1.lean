-- Prove2me | solution 1 for EndoInvDemand.Clearing.proposition_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:30:24.092852+00:00
-- url     : https://prove2.me/submissions/1070aac3-8bc2-47cd-b167-ba49c02aa3e5

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology
set_option linter.unusedSectionVars false

namespace EndoInvDemand.Clearing


lemma eid_Dset_open (D : Dom) : IsOpen D.set := by
  cases D with
  | real => exact isOpen_univ
  | pos => exact isOpen_Ioi

lemma eid_R_diffAt {D : Dom} {R : ℝ → ℝ} (hR : Assumption31 D R) {y : ℝ} (hy : y ∈ D.set) :
    DifferentiableAt ℝ R y :=
  hR.2.1.differentiableAt ((eid_Dset_open D).mem_nhds hy)

lemma eid_deriv_R_nonneg {D : Dom} {R : ℝ → ℝ} (hR : Assumption31 D R) {y : ℝ} (hy : y ∈ D.set) :
    0 ≤ deriv R y := by
  rw [← derivWithin_of_isOpen (eid_Dset_open D) hy]
  exact hR.1.monotoneOn.derivWithin_nonneg

lemma eid_deriv_R_anti {D : Dom} {R : ℝ → ℝ} (hR : Assumption31 D R) :
    AntitoneOn (deriv R) D.set :=
  hR.2.2.antitoneOn_deriv (fun _ hy => eid_R_diffAt hR hy)

lemma eid_f_hasDeriv {D : Dom} {R : ℝ → ℝ} (hR : Assumption31 D R) (x : ℝ) {z : ℝ}
    (hz : x + z ∈ D.set) :
    HasDerivAt (fun z => z * Real.exp (-R (x + z)))
      (Real.exp (-R (x + z)) * (1 - z * deriv R (x + z))) z := by
  have h1 : HasDerivAt (fun z => x + z) 1 z := by
    simpa using (hasDerivAt_id z).const_add x
  have h2 : HasDerivAt (fun z => R (x + z)) (deriv R (x + z) * 1) z :=
    (eid_R_diffAt hR hz).hasDerivAt.comp z h1
  have h3 : HasDerivAt (fun z => Real.exp (-R (x + z)))
      (Real.exp (-R (x + z)) * -(deriv R (x + z) * 1)) z := h2.neg.exp
  have h4 : HasDerivAt (fun z => z * Real.exp (-R (x + z)))
      (1 * Real.exp (-R (x + z)) + z * (Real.exp (-R (x + z)) * -(deriv R (x + z) * 1))) z :=
    (hasDerivAt_id' z).mul h3
  convert h4 using 1
  ring

theorem eid_proposition_D_1 (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (x : ℝ) (hx : x ∈ D.set) :
    (MonotoneOn (fun z => z * Real.exp (-R (x + z))) (Set.Ioi 0) →
        MonotoneOn (fun z => z * Real.exp (-R (x + z))) {z | x + z ∈ D.set}) ∧
    (ConcaveOn ℝ (Set.Ioi 0) (fun z => z * Real.exp (-R (x + z))) →
        ConcaveOn ℝ {z | x + z ∈ D.set} (fun z => z * Real.exp (-R (x + z)))) := by
  -- the weight `g z = exp(-R(x+z))` is antitone on `S`
  have hpos_mem : ∀ z : ℝ, 0 < z → x + z ∈ D.set := by
    intro z hz
    cases D with
    | real => simp [Dom.set]
    | pos => show (0:ℝ) < x + z; have : (0:ℝ) < x := hx; linarith
  have hg : ∀ z1 z2 : ℝ, x + z1 ∈ D.set → x + z2 ∈ D.set → z1 ≤ z2 →
      Real.exp (-R (x + z2)) ≤ Real.exp (-R (x + z1)) := by
    intro z1 z2 h1 h2 h12
    apply Real.exp_le_exp.2
    have := hR.1.monotoneOn h1 h2 (by linarith)
    linarith
  have hSopen : IsOpen {z | x + z ∈ D.set} :=
    (eid_Dset_open D).preimage (continuous_const.add continuous_id)
  constructor
  · intro hmono z1 h1 z2 h2 h12
    simp only [Set.mem_ofPred_eq] at h1 h2
    by_cases hz1 : 0 < z1
    · exact hmono hz1 (lt_of_lt_of_le hz1 h12 : (0:ℝ) < z2) h12
    · push Not at hz1
      by_cases hz2 : z2 ≤ 0
      · have g12 := hg z1 z2 h1 h2 h12
        have gp := Real.exp_pos (-R (x + z1))
        calc z1 * Real.exp (-R (x + z1)) ≤ z2 * Real.exp (-R (x + z1)) :=
              mul_le_mul_of_nonneg_right h12 gp.le
          _ ≤ z2 * Real.exp (-R (x + z2)) := mul_le_mul_of_nonpos_left g12 hz2
      · push Not at hz2
        have a : z1 * Real.exp (-R (x + z1)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hz1 (Real.exp_pos _).le
        have b : 0 ≤ z2 * Real.exp (-R (x + z2)) := mul_nonneg hz2.le (Real.exp_pos _).le
        simp only; linarith
  · intro hconc
    have hdiff : ∀ z ∈ {z | x + z ∈ D.set},
        DifferentiableAt ℝ (fun z => z * Real.exp (-R (x + z))) z :=
      fun z hz => (eid_f_hasDeriv hR x hz).differentiableAt
    have hderiv : ∀ z ∈ {z | x + z ∈ D.set}, deriv (fun z => z * Real.exp (-R (x + z))) z
        = Real.exp (-R (x + z)) * (1 - z * deriv R (x + z)) :=
      fun z hz => (eid_f_hasDeriv hR x hz).deriv
    apply AntitoneOn.concaveOn_of_deriv
    · -- convexity of S
      intro a ha b hb s t hs ht hst
      simp only [Set.mem_ofPred_eq] at ha hb ⊢
      cases D with
      | real => simp [Dom.set]
      | pos =>
        have ha' : (0:ℝ) < x + a := ha
        have hb' : (0:ℝ) < x + b := hb
        show (0:ℝ) < x + (s • a + t • b)
        simp only [smul_eq_mul]
        have : x + (s * a + t * b) = s * (x + a) + t * (x + b) := by
          have : x = (s + t) * x := by rw [hst]; ring
          linarith [this]
        rw [this]
        rcases hs.lt_or_eq with hs' | hs'
        · nlinarith [mul_pos hs' ha', mul_nonneg ht hb'.le]
        · subst hs'; simp at hst; subst hst; simpa using hb'
    · exact fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
    · rw [hSopen.interior_eq]; exact fun z hz => (hdiff z hz).differentiableWithinAt
    · rw [hSopen.interior_eq]
      intro z1 h1 z2 h2 h12
      rw [hderiv z1 h1, hderiv z2 h2]
      simp only [Set.mem_ofPred_eq] at h1 h2
      have g12 := hg z1 z2 h1 h2 h12
      have gp1 := Real.exp_pos (-R (x + z1))
      have gp2 := Real.exp_pos (-R (x + z2))
      have d1 := eid_deriv_R_nonneg hR h1
      have d2 := eid_deriv_R_nonneg hR h2
      have d12 := eid_deriv_R_anti hR h1 h2 (by linarith)
      by_cases hz1 : 0 < z1
      · have hz2 : 0 < z2 := lt_of_lt_of_le hz1 h12
        have := hconc.antitoneOn_deriv
          (fun z (hz : (0:ℝ) < z) => (eid_f_hasDeriv hR x (hpos_mem z hz)).differentiableAt)
          (show (0:ℝ) < z1 from hz1) (show (0:ℝ) < z2 from hz2) h12
        rwa [hderiv z1 h1, hderiv z2 h2] at this
      · push Not at hz1
        have e1 : 1 ≤ 1 - z1 * deriv R (x + z1) := by nlinarith
        by_cases hz2 : z2 ≤ 0
        · have e2 : 1 - z2 * deriv R (x + z2) ≤ 1 - z1 * deriv R (x + z1) := by
            have : z1 * deriv R (x + z1) ≤ z2 * deriv R (x + z2) := by
              have := mul_le_mul_of_nonpos_left d12 hz1
              nlinarith
            linarith
          have e2' : 0 ≤ 1 - z2 * deriv R (x + z2) := by nlinarith
          calc Real.exp (-R (x + z2)) * (1 - z2 * deriv R (x + z2))
              ≤ Real.exp (-R (x + z1)) * (1 - z2 * deriv R (x + z2)) :=
                mul_le_mul_of_nonneg_right g12 e2'
            _ ≤ Real.exp (-R (x + z1)) * (1 - z1 * deriv R (x + z1)) :=
                mul_le_mul_of_nonneg_left e2 gp1.le
        · push Not at hz2
          have e2 : 1 - z2 * deriv R (x + z2) ≤ 1 := by nlinarith
          calc Real.exp (-R (x + z2)) * (1 - z2 * deriv R (x + z2))
              ≤ Real.exp (-R (x + z2)) * 1 := mul_le_mul_of_nonneg_left e2 gp2.le
            _ ≤ Real.exp (-R (x + z1)) * 1 := by linarith
            _ ≤ Real.exp (-R (x + z1)) * (1 - z1 * deriv R (x + z1)) :=
                mul_le_mul_of_nonneg_left e1 gp1.le

end EndoInvDemand.Clearing

open EndoInvDemand.Clearing

theorem solution (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (x : ℝ) (hx : x ∈ D.set) :
    (MonotoneOn (fun z => z * Real.exp (-R (x + z))) (Set.Ioi 0) →
        MonotoneOn (fun z => z * Real.exp (-R (x + z))) {z | x + z ∈ D.set}) ∧
    (ConcaveOn ℝ (Set.Ioi 0) (fun z => z * Real.exp (-R (x + z))) →
        ConcaveOn ℝ {z | x + z ∈ D.set} (fun z => z * Real.exp (-R (x + z)))) :=
  eid_proposition_D_1 D R hR x hx
