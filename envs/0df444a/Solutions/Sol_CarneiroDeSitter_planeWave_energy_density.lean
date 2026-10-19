-- Prove2me | solution 1 for CarneiroDeSitter.planeWave_energy_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:55:09.136794+00:00
-- url     : https://prove2.me/submissions/1ec3bdf8-703c-4e29-a6ac-2d431b4ef8b0

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

theorem pw_energy (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let b := dampingRate ω H
    let φ := planeWave φ₀ b ω (waveNumber ω H)
    let φt := deriv (fun s => φ s r) t
    let φr := deriv (fun x => φ t x) r
    Complex.normSq φt - (1 / 2) * (Complex.normSq φt - Complex.normSq φr)
      = (ω ^ 2 + b ^ 2) * Complex.normSq (φ t r) := by
  intro b φ φt φr
  obtain ⟨h1, -⟩ := kb_rel ω H hω
  set k := waveNumber ω H
  have et : φt = -Complex.I * ω * φ t r := (pw_dt φ₀ b ω k r t).deriv
  have er : φr = (-b + Complex.I * k) * φ t r := (pw_dr φ₀ b ω k t r).deriv
  rw [et, er, Complex.normSq_mul (-Complex.I * ω), Complex.normSq_mul (-b + Complex.I * k)]
  have n1 : Complex.normSq (-Complex.I * ω) = ω ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, Complex.normSq_ofReal]; ring
  have n2 : Complex.normSq (-b + Complex.I * k) = b ^ 2 + k ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [n1, n2]
  linear_combination (1/2 * Complex.normSq (φ t r)) * h1

end CarneiroDeSitter

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (ω H : ℝ) (hω : 0 < ω) (φ₀ : ℂ) (t r : ℝ) :
    let b := dampingRate ω H
    let φ := planeWave φ₀ b ω (waveNumber ω H)
    let φt := deriv (fun s => φ s r) t
    let φr := deriv (fun x => φ t x) r
    Complex.normSq φt - (1 / 2) * (Complex.normSq φt - Complex.normSq φr)
      = (ω ^ 2 + b ^ 2) * Complex.normSq (φ t r) := pw_energy ω H hω φ₀ t r
