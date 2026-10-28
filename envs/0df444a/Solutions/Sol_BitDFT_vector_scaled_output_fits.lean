-- Prove2me | solution 1 for BitDFT.vector_scaled_output_fits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:08:23.564338+00:00
-- url     : https://prove2.me/submissions/cfa71676-1888-482e-9771-dccc257cdf56

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

namespace BitDFT.VectorScaleEncoding

private theorem coordinate_bounds (q : ℕ) (z : ℤ × ℤ) (h : inDisc q z) :
    z.1.natAbs ≤ 2^q ∧ z.2.natAbs ≤ 2^q := by
  have hp : (0 : ℝ) < 2^q := by positivity
  have hn : ‖(z.1 : ℂ) + (z.2 : ℂ) * Complex.I‖ ≤ (2 : ℝ)^q := by
    unfold inDisc value at h
    rw [norm_div, norm_pow] at h
    norm_num at h
    exact (div_le_iff₀ hp).mp h |>.trans (by simp)
  have hre := (Complex.abs_re_le_norm ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).trans hn
  have him := (Complex.abs_im_le_norm ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)).trans hn
  simp at hre him
  constructor
  · have hc : (z.1.natAbs : ℝ) ≤ (2 : ℝ)^q := by simpa [Nat.cast_natAbs] using hre
    exact_mod_cast hc
  · have hc : (z.2.natAbs : ℝ) ≤ (2 : ℝ)^q := by simpa [Nat.cast_natAbs] using him
    exact_mod_cast hc

/-- Every coordinate in a disc-valued vector remains representable after exact
integer rescaling, using the output width reserved by the transfer theorem. -/
theorem scaled_coordinates_fit {n q ell : ℕ} (hscale : n ≤ 2^ell)
    (U : Fin n → ℤ × ℤ) (hU : vectorDisc q U) (k : Fin n) :
    ((n : ℤ) * (U k).1).natAbs < 2^(q + ell + 1) ∧
    ((n : ℤ) * (U k).2).natAbs < 2^(q + ell + 1) := by
  obtain ⟨hreal, himag⟩ := coordinate_bounds q (U k) (hU k)
  have hrealmul : ((n : ℤ) * (U k).1).natAbs = n * (U k).1.natAbs := by
    simp [Int.natAbs_mul]
  have himagmul : ((n : ℤ) * (U k).2).natAbs = n * (U k).2.natAbs := by
    simp [Int.natAbs_mul]
  have hpow : 2^(ell + q) < 2^(q + ell + 1) := by
    apply Nat.pow_lt_pow_right (by decide : 1 < 2)
    omega
  constructor
  · rw [hrealmul]
    calc
      n * (U k).1.natAbs ≤ 2^ell * 2^q := Nat.mul_le_mul hscale hreal
      _ = 2^(ell + q) := by rw [pow_add]
      _ < 2^(q + ell + 1) := hpow
  · rw [himagmul]
    calc
      n * (U k).2.natAbs ≤ 2^ell * 2^q := Nat.mul_le_mul hscale himag
      _ = 2^(ell + q) := by rw [pow_add]
      _ < 2^(q + ell + 1) := hpow

/-- The signed-vector encoding is the flat stream of coordinate encodings, so
the preceding field-width bound applies uniformly to every output record. -/
theorem scaled_vector_length {n q ell : ℕ} (U : Fin n → ℤ × ℤ) :
    (encVector (q + ell + 1) (fun k =>
      ((n : ℤ) * (U k).1, (n : ℤ) * (U k).2))).length =
        2 * n * (q + ell + 2) := by
  simp [encVector, encComplex, encInt, bin, List.flatMap_assoc]
  ring

end BitDFT.VectorScaleEncoding

theorem solution {n q ell : ℕ} (hscale : n ≤ 2^ell)
    (U : Fin n → ℤ × ℤ) (hU : vectorDisc q U) :
    (∀ k, ((n : ℤ) * (U k).1).natAbs < 2^(q + ell + 1) ∧
      ((n : ℤ) * (U k).2).natAbs < 2^(q + ell + 1)) ∧
    (encVector (q + ell + 1) (fun k =>
      ((n : ℤ) * (U k).1, (n : ℤ) * (U k).2))).length =
        2 * n * (q + ell + 2) := by
  constructor
  · intro k
    exact BitDFT.VectorScaleEncoding.scaled_coordinates_fit hscale U hU k
  · exact BitDFT.VectorScaleEncoding.scaled_vector_length U
