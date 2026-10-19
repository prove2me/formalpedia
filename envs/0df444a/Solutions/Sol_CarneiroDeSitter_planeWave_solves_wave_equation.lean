-- Prove2me | solution 1 for CarneiroDeSitter.planeWave_solves_wave_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:55:00.571426+00:00
-- url     : https://prove2.me/submissions/ffd2f720-50dc-460a-a6b2-09c09276b2b4

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set
namespace CarneiroDeSitter

lemma pw_dt (φ₀ : ℂ) (b ω k r s : ℝ) :
    HasDerivAt (fun s => planeWave φ₀ b ω k s r) (-Complex.I * ω * planeWave φ₀ b ω k s r) s := by
  have h1 : HasDerivAt (fun s : ℝ => ((ω * s - k * r : ℝ) : ℂ)) (ω : ℂ) s := by
    have : HasDerivAt (fun s : ℝ => ω * s - k * r) ω s := by
      simpa using ((hasDerivAt_id s).const_mul ω).sub_const (k * r)
    exact this.ofReal_comp
  have h2 := ((h1.const_mul (-Complex.I)).cexp).const_mul (φ₀ * Complex.exp (-((b * r : ℝ) : ℂ)))
  unfold planeWave
  exact h2.congr_deriv (by ring)

lemma pw_dr (φ₀ : ℂ) (b ω k t x : ℝ) :
    HasDerivAt (fun x => planeWave φ₀ b ω k t x) ((-b + Complex.I * k) * planeWave φ₀ b ω k t x) x := by
  have h1 : HasDerivAt (fun x : ℝ => ((ω * t - k * x : ℝ) : ℂ)) (-(k : ℂ)) x := by
    have : HasDerivAt (fun x : ℝ => ω * t - k * x) (-k) x := by
      simpa using ((hasDerivAt_id x).const_mul k).const_sub (ω * t)
    convert this.ofReal_comp using 1; push_cast; ring
  have h0 : HasDerivAt (fun x : ℝ => -((b * x : ℝ) : ℂ)) (-(b : ℂ)) x := by
    have : HasDerivAt (fun x : ℝ => b * x) b x := by
      simpa using ((hasDerivAt_id x).const_mul b)
    exact this.ofReal_comp.neg
  have h2 := ((h0.cexp).const_mul φ₀).mul ((h1.const_mul (-Complex.I)).cexp)
  unfold planeWave
  exact h2.congr_deriv (by ring)

lemma pw_deriv_t (φ₀ : ℂ) (b ω k r : ℝ) :
    deriv (fun s => planeWave φ₀ b ω k s r) = fun s => -Complex.I * ω * planeWave φ₀ b ω k s r := by
  funext s; exact (pw_dt φ₀ b ω k r s).deriv

lemma pw_deriv_r (φ₀ : ℂ) (b ω k t : ℝ) :
    deriv (fun x => planeWave φ₀ b ω k t x) = fun x => (-b + Complex.I * k) * planeWave φ₀ b ω k t x := by
  funext x; exact (pw_dr φ₀ b ω k t x).deriv

lemma kb_rel (ω H : ℝ) (hω : 0 < ω) :
    waveNumber ω H ^ 2 - dampingRate ω H ^ 2 = ω ^ 2 ∧
    2 * dampingRate ω H * waveNumber ω H = 3 * H * ω := by
  set S := Real.sqrt (1 + (3 * H / ω) ^ 2) with hS
  have hS1 : 1 ≤ S := by rw [hS]; exact Real.one_le_sqrt.2 (by nlinarith)
  have hS2 : S ^ 2 = 1 + (3 * H / ω) ^ 2 := Real.sq_sqrt (by positivity)
  have hA : 0 < 1 + S := by linarith
  have hsA : Real.sqrt (1 + S) ^ 2 = 1 + S := Real.sq_sqrt hA.le
  have hsA0 : 0 < Real.sqrt (1 + S) := Real.sqrt_pos.2 hA
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [waveNumber, dampingRate, ← hS]
  constructor
  · field_simp
    have : (3 * H) ^ 2 = ω ^ 2 * (S ^ 2 - 1) := by rw [hS2]; field_simp; ring
    have h4 : Real.sqrt (1 + S) ^ 4 = (1 + S) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hsA]
    rw [h2, h4, hsA]
    linear_combination (-2) * this
  · field_simp
    rw [h2]

theorem pw_wave (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let φ := planeWave φ₀ (dampingRate ω H) ω (waveNumber ω H)
    deriv (deriv (fun s => φ s r)) t + 3 * H * deriv (fun s => φ s r) t
      - deriv (deriv (fun x => φ t x)) r = 0 := by
  intro φ
  obtain ⟨h1, h2⟩ := kb_rel ω H hω
  set b := dampingRate ω H
  set k := waveNumber ω H
  have e1 : deriv (fun s => φ s r) = fun s => -Complex.I * ω * φ s r := pw_deriv_t φ₀ b ω k r
  have e2 : deriv (fun x => φ t x) = fun x => (-b + Complex.I * k) * φ t x := pw_deriv_r φ₀ b ω k t
  have e1' : deriv (fun s => -Complex.I * ω * φ s r) t = -Complex.I * ω * (-Complex.I * ω * φ t r) := by
    rw [deriv_const_mul _ (pw_dt φ₀ b ω k r t).differentiableAt, e1]
  rw [e1, e2, e1']
  rw [deriv_const_mul _ (pw_dr φ₀ b ω k t r).differentiableAt, e2]
  have c1 : (k : ℂ) ^ 2 - (b : ℂ) ^ 2 = (ω : ℂ) ^ 2 := by exact_mod_cast h1
  have c2 : 2 * (b : ℂ) * k = 3 * H * ω := by exact_mod_cast h2
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (φ t r) * c1 + (Complex.I * φ t r) * c2 + ((ω:ℂ)^2 * φ t r - k^2 * φ t r) * hI

end CarneiroDeSitter

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let φ := planeWave φ₀ (dampingRate ω H) ω (waveNumber ω H)
    deriv (deriv (fun s => φ s r)) t + 3 * H * deriv (fun s => φ s r) t
      - deriv (deriv (fun x => φ t x)) r = 0 := pw_wave ω H hω φ₀ t r
