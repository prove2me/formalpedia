-- Prove2me | solution 1 for CorreaThreshold.Tight.prop_A_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:39:27.892612+00:00
-- url     : https://prove2.me/submissions/64cbe763-f805-484b-b7f2-616ee98f0430

import Mathlib
import Definitions.Def_CorreaThreshold_Tight_Setting

set_option autoImplicit false
open MeasureTheory

theorem psi_nonneg_aux (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hea : Real.exp 1 = a + 2)
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ a * x + 1 - Real.exp x + x * Real.exp (x - 1) := by
  have hx1 : ∀ x : ℝ, Real.exp x = Real.exp (x - 1) * (a + 2) := fun x => by
    rw [← hea, ← Real.exp_add]; ring_nf
  set P : ℝ → ℝ := fun x => a + Real.exp (x - 1) * (x - a - 1) with hPdef
  set Ψ : ℝ → ℝ := fun x => a * x + 1 - Real.exp x + x * Real.exp (x - 1) with hΨdef
  have hexp1 : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (x - 1)) (Real.exp (x - 1)) x := fun x => by
    simpa using ((hasDerivAt_id x).sub_const 1).exp
  have hΨ : ∀ x, HasDerivAt Ψ (P x) x := by
    intro x
    have h1 : HasDerivAt (fun x => a * x) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h4 : HasDerivAt (fun x => x * Real.exp (x - 1)) (1 * Real.exp (x - 1) + x * Real.exp (x - 1)) x :=
      (hasDerivAt_id x).mul (hexp1 x)
    refine (((h1.add_const 1).sub (Real.hasDerivAt_exp x)).add h4).congr_deriv ?_
    simp only [hPdef]
    rw [hx1 x]; ring
  have hP : ∀ x, HasDerivAt P (Real.exp (x - 1) * (x - a)) x := by
    intro x
    have h2 : HasDerivAt (fun x => x - a - 1) 1 x := by
      simpa using ((hasDerivAt_id x).sub_const a).sub_const 1
    refine ((((hexp1 x).mul h2)).const_add a).congr_deriv ?_
    ring
  have hP1 : P 1 = 0 := by simp [hPdef]
  have hΨ1 : Ψ 1 = 0 := by
    show a * 1 + 1 - Real.exp 1 + 1 * Real.exp (1 - 1) = 0
    rw [hea, sub_self, Real.exp_zero]; ring
  have hΨ0 : Ψ 0 = 0 := by simp [hΨdef]
  have hPmono : MonotoneOn P (Set.Ici a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici a) (fun x _ => (hP x).continuousAt.continuousWithinAt)
      (fun x _ => (hP x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hP x).deriv]
    exact mul_nonneg (Real.exp_pos _).le (by have := Set.mem_Ioi.mp hx; linarith)
  have hge1 : ∀ x, 1 ≤ x → 0 ≤ Ψ x := by
    have hm : MonotoneOn Ψ (Set.Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) (fun x _ => (hΨ x).continuousAt.continuousWithinAt)
        (fun x _ => (hΨ x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Ici] at hx
      rw [(hΨ x).deriv]
      have hx' : 1 < x := hx
      have := hPmono (show a ∈ Set.Ici a from le_refl a) (show x ∈ Set.Ici a from by
        show a ≤ x; linarith) (by linarith)
      rw [← hP1]; exact hPmono (show (1:ℝ) ∈ Set.Ici a from by show a ≤ 1; linarith)
        (show x ∈ Set.Ici a from by show a ≤ x; linarith) hx'.le
    intro x hx
    have := hm (Set.mem_Ici.mpr le_rfl) (show x ∈ Set.Ici 1 from hx) hx
    rw [hΨ1] at this; exact this
  have hmid : ∀ x, a ≤ x → x ≤ 1 → 0 ≤ Ψ x := by
    have hm : AntitoneOn Ψ (Set.Icc a 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a 1) (fun x _ => (hΨ x).continuousAt.continuousWithinAt)
        (fun x _ => (hΨ x).differentiableAt.differentiableWithinAt) ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(hΨ x).deriv]
      have hx' := hx
      rw [← hP1]
      exact hPmono (show x ∈ Set.Ici a from by show a ≤ x; exact hx'.1.le)
        (show (1:ℝ) ∈ Set.Ici a from by show a ≤ 1; linarith) hx'.2.le
    intro x hx hx1'
    have := hm (show x ∈ Set.Icc a 1 from ⟨hx, hx1'⟩) (show (1:ℝ) ∈ Set.Icc a 1 from ⟨ha1.le, le_refl _⟩) hx1'
    rw [hΨ1] at this; exact this
  have hge_a : ∀ x, a ≤ x → 0 ≤ Ψ x := by
    intro x hx
    rcases le_total x 1 with h | h
    · exact hmid x hx h
    · exact hge1 x h
  have hΨa : 0 ≤ Ψ a := hge_a a le_rfl
  show 0 ≤ Ψ x
  rcases le_total a x with h | h
  · exact hge_a x h
  · -- concavity on [0, a]
    have hder : deriv Ψ = P := funext fun x => (hΨ x).deriv
    have hconc : ConcaveOn ℝ (Set.Icc 0 a) Ψ := by
      refine concaveOn_of_deriv2_nonpos (convex_Icc 0 a) (fun x _ => (hΨ x).continuousAt.continuousWithinAt)
        (fun x _ => (hΨ x).differentiableAt.differentiableWithinAt) ?_ ?_
      · rw [hder]; exact fun x _ => (hP x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        show deriv (deriv Ψ) x ≤ 0
        rw [hder, (hP x).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by have := hx.2; linarith)
    have := hconc.2 (show (0:ℝ) ∈ Set.Icc 0 a from ⟨le_rfl, ha0.le⟩) (show a ∈ Set.Icc 0 a from ⟨ha0.le, le_rfl⟩)
      (show (0:ℝ) ≤ 1 - x / a by rw [sub_nonneg, div_le_one ha0]; exact h) (show 0 ≤ x / a by positivity) (show (1 - x / a) + x / a = 1 by ring)
    simp only [smul_eq_mul, hΨ0, mul_zero, zero_add, mul_zero, add_zero] at this
    have e2 : x / a * a = x := by field_simp
    rw [e2] at this
    exact le_trans (mul_nonneg (by positivity) hΨa) this

theorem solution :
    ∀ x : ℝ, 0 < x →
      (1 - Real.exp (-x)) * (1 / (x * (Real.exp 1 - 2)) + 1) ≤
        (1 - Real.exp (-1)) * (1 / (Real.exp 1 - 2) + 1) := by
  intro x hx
  have he2 : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  obtain ⟨a, ha⟩ : ∃ a, a = Real.exp 1 - 2 := ⟨_, rfl⟩
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := by linarith
  have hea : Real.exp 1 = a + 2 := by linarith
  have hpsi := psi_nonneg_aux a ha0 ha1 hea x hx.le
  have hxe : Real.exp x = Real.exp (x - 1) * (a + 2) := by
    rw [← hea, ← Real.exp_add]; ring_nf
  rw [← ha, Real.exp_neg, Real.exp_neg, hea]
  have hE : 0 < Real.exp x := Real.exp_pos x
  have hexm : 0 < Real.exp (x - 1) := Real.exp_pos _
  rw [hxe] at hpsi ⊢
  set E := Real.exp (x - 1) with hEdef
  have hE0 : 0 < E := hexm
  rw [← sub_nonneg]
  have : (1 - (a + 2)⁻¹) * (1 / a + 1) - (1 - (E * (a + 2))⁻¹) * (1 / (x * a) + 1) =
      (a * x + 1 - E * (a + 2) + x * E) / (x * a * E * (a + 2) ) * 1 := by
    field_simp
    ring
  rw [this, mul_one]
  positivity
