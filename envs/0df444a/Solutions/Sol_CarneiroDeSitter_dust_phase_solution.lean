-- Prove2me | solution 1 for CarneiroDeSitter.dust_phase_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:51:37.291553+00:00
-- url     : https://prove2.me/submissions/2738667f-16a9-4b59-9333-df47cfe3afec

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set
namespace CarneiroDeSitter

lemma dust_hasDeriv (C σ : ℝ) (hσ : 0 < σ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (dustScaleFactor C σ)
      (C * ((2/3 : ℝ) * (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3 - 1) * (Real.exp (σ * s / 2) * (σ / 2)))) s := by
  have hE : 0 < Real.exp (σ * s / 2) - 1 := by
    have : 1 < Real.exp (σ * s / 2) := Real.one_lt_exp_iff.2 (by positivity)
    linarith
  have h1 : HasDerivAt (fun s => Real.exp (σ * s / 2) - 1) (Real.exp (σ * s / 2) * (σ / 2)) s := by
    have : HasDerivAt (fun s => σ * s / 2) (σ / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul σ).div_const 2
    exact (this.exp).sub_const 1
  have h2 := h1.rpow_const (p := (2:ℝ)/3) (Or.inl hE.ne')
  have h3 : HasDerivAt (dustScaleFactor C σ) _ s := h2.const_mul C
  exact h3.congr_deriv (by ring)

lemma dust_H (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) (s : ℝ) (hs : 0 < s) :
    deriv (dustScaleFactor C σ) s / dustScaleFactor C σ s
      = σ / 3 * Real.exp (σ * s / 2) / (Real.exp (σ * s / 2) - 1) := by
  have hE : 0 < Real.exp (σ * s / 2) - 1 := by
    have : 1 < Real.exp (σ * s / 2) := Real.one_lt_exp_iff.2 (by positivity)
    linarith
  rw [(dust_hasDeriv C σ hσ s hs).deriv, dustScaleFactor]
  have : (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3 - 1)
      = (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3) / (Real.exp (σ * s / 2) - 1) := by
    rw [Real.rpow_sub hE, Real.rpow_one]
  rw [this]
  have hp : 0 < (Real.exp (σ * s / 2) - 1) ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos hE _
  field_simp

theorem dps (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) (t : ℝ) (ht : 0 < t) :
    let H := fun s => deriv (dustScaleFactor C σ) s / dustScaleFactor C σ s
    deriv (fun s => 3 * H s ^ 2) t + 3 * H t * (3 * H t ^ 2 + (0 - σ * H t)) = 0 := by
  intro H
  set h : ℝ → ℝ := fun s => σ / 3 * Real.exp (σ * s / 2) / (Real.exp (σ * s / 2) - 1) with hh
  have hEq : H =ᶠ[𝓝 t] h := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact dust_H C σ hC hσ s hs
  have hHt : H t = h t := hEq.eq_of_nhds
  have hE : 0 < Real.exp (σ * t / 2) - 1 := by
    have : 1 < Real.exp (σ * t / 2) := Real.one_lt_exp_iff.2 (by positivity)
    linarith
  have e1 : HasDerivAt (fun s => Real.exp (σ * s / 2)) (Real.exp (σ * t / 2) * (σ / 2)) t := by
    have : HasDerivAt (fun s => σ * s / 2) (σ / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul σ).div_const 2
    exact this.exp
  have q := (e1.const_mul (σ / 3)).div (e1.sub_const 1) hE.ne'
  have hd := (q.pow 2).const_mul 3
  have hfun : (fun s => 3 * h s ^ 2) = fun y => 3 * (((fun y => σ / 3 * Real.exp (σ * y / 2)) / fun x => Real.exp (σ * x / 2) - 1) ^ 2) y := by
    funext y; simp [hh]
  have hd' : deriv (fun s => 3 * H s ^ 2) t = deriv (fun s => 3 * h s ^ 2) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hEq] with s hs
    simp [hs]
  rw [hd', hfun, hd.deriv, hHt]
  simp only [hh, Pi.div_apply]
  generalize Real.exp (σ * t / 2) = E at hE ⊢
  have hE' : E - 1 ≠ 0 := hE.ne'
  norm_num only [Nat.cast_ofNat, pow_one]
  field_simp
  ring

end CarneiroDeSitter

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (C σ : ℝ) (hC : 0 < C) (hσ : 0 < σ) (t : ℝ) (ht : 0 < t) :
    let H := fun s => deriv (dustScaleFactor C σ) s / dustScaleFactor C σ s
    deriv (fun s => 3 * H s ^ 2) t + 3 * H t * (3 * H t ^ 2 + (0 - σ * H t)) = 0 :=
  dps C σ hC hσ t ht
