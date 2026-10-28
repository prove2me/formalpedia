-- Prove2me | solution 1 for D1Bound5.coupled_phase_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:01:01.779631+00:00
-- url     : https://prove2.me/submissions/6ec3d82b-9f64-46b5-9431-dec412b06dd3

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions
import Theorems.Thm_D1Bound5_phaseHalfPolynomial_deriv

section
namespace D1Bound5






theorem phaseCritical_mono (q x y : ℝ) (hq : 0 < q)
    (hx : 0 ≤ x) (hxy : x ≤ y) : phaseCritical q x ≤ phaseCritical q y := by
  unfold phaseCritical
  gcongr

/-- Exact rational brackets around the positive critical point suffice
for a global bound. The two outer intervals use the proved derivative
sign; the middle interval uses monotonicity of its two positive factors. -/
theorem _root_.solution (q l r F : ℝ)
    (hq : 1 ≤ q) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 2)
    (hleft : phaseCritical q l ≤ 0) (hright : 0 ≤ phaseCritical q r)
    (henvelope : (4-l^2)^4*(1+(1/q)^2+r/q)^2 < F)
    (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 2) : coupledPhasePolynomial q x < F := by
  have hq0 : 0 < q := by linarith only [hq]
  have hl2 : l ≤ 2 := hlr.trans hr
  have hr0 : 0 ≤ r := hl.trans hlr
  have hbase (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 2) : 0 ≤ 4-t^2 := by
    nlinarith only [ht,ht2]
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1+(1/q)^2+t/q := by positivity
  have hmono : MonotoneOn (phaseHalfPolynomial q) (Set.Icc 0 l) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 l)
    · unfold phaseHalfPolynomial
      fun_prop
    · intro t _
      exact (phaseHalfPolynomial_deriv q t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc 0 l := interior_subset ht
      rw [(phaseHalfPolynomial_deriv q t).deriv]
      have hcrit : phaseCritical q t ≤ 0 :=
        (phaseCritical_mono q t l hq0 ht'.1 ht'.2).trans hleft
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hbase t ht'.1 (ht'.2.trans hl2))) hcrit
  have hanti : AntitoneOn (phaseHalfPolynomial q) (Set.Icc r 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r 2)
    · unfold phaseHalfPolynomial
      fun_prop
    · intro t _
      exact (phaseHalfPolynomial_deriv q t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc r 2 := interior_subset ht
      rw [(phaseHalfPolynomial_deriv q t).deriv]
      have hcrit : 0 ≤ phaseCritical q t :=
        hright.trans (phaseCritical_mono q r t hq0 hr0 ht'.1)
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (hbase t (hr0.trans ht'.1) ht'.2)) hcrit
  let G := (4-l^2)^2*(1+(1/q)^2+r/q)
  have hG0 : 0 ≤ G := mul_nonneg (sq_nonneg _) (hpos r hr0)
  have hg0 : 0 ≤ phaseHalfPolynomial q x := mul_nonneg (sq_nonneg _) (hpos x hx)
  have hlbase := hbase l hl hl2
  have hrbase := hbase r hr0 hr
  have hxbase := hbase x hx hx2
  have hg : phaseHalfPolynomial q x ≤ G := by
    by_cases hxl : x ≤ l
    · calc
        _ ≤ phaseHalfPolynomial q l := hmono ⟨hx,hxl⟩ ⟨hl,le_rfl⟩ hxl
        _ ≤ G := by unfold phaseHalfPolynomial; dsimp [G]; gcongr
    · by_cases hrx : r ≤ x
      · calc
          _ ≤ phaseHalfPolynomial q r := hanti ⟨le_rfl,hr⟩ ⟨hrx,hx2⟩ hrx
          _ ≤ G := by
            unfold phaseHalfPolynomial
            dsimp [G]
            gcongr
      · have hlx : l ≤ x := (lt_of_not_ge hxl).le
        have hxr : x ≤ r := (lt_of_not_ge hrx).le
        unfold phaseHalfPolynomial
        dsimp [G]
        gcongr
  have hsquare : (phaseHalfPolynomial q x)^2 ≤ G^2 := by
    nlinarith only [hg,hg0,hG0]
  have hf : coupledPhasePolynomial q x = (phaseHalfPolynomial q x)^2 := by
    unfold coupledPhasePolynomial phaseHalfPolynomial
    ring
  rw [hf]
  apply lt_of_le_of_lt hsquare
  have hGeq : G^2 = (4-l^2)^4*(1+(1/q)^2+r/q)^2 := by dsimp [G]; ring
  rwa [hGeq]







end D1Bound5
end
