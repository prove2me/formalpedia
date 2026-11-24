-- Prove2me | solution 1 for GaussianPerimeter.expLower_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:56:13.790186+00:00
-- url     : https://prove2.me/submissions/bdcbf642-2de4-45c0-8688-7d19b9f5c1cd

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_ExpBounds
section
@[expose] public section
namespace GaussianPerimeter
namespace ExpBounds
private theorem scale_pos : 0 < scale := by norm_num [scale]
private theorem roundDown_le (x : ℚ) : roundDown x ≤ x :=
  (div_le_iff₀ scale_pos).2 (Int.floor_le _)
private theorem lowerSquares_nonneg (n : ℕ) (x : ℚ) : 0 ≤ lowerSquares n x := by
  cases n with
  | zero => exact le_max_left _ _
  | succ n =>
    apply div_nonneg _ scale_pos.le
    exact_mod_cast Int.floor_nonneg.mpr
      (mul_nonneg (sq_nonneg (lowerSquares n x)) scale_pos.le)
private theorem lowerSquares_le_pow (n : ℕ) (x : ℚ) {y : ℝ}
    (hy : 0 ≤ y) (hx : (x : ℝ) ≤ y) :
    (lowerSquares n x : ℝ) ≤ y ^ (2 ^ n : ℕ) := by
  induction n with
  | zero => simpa [lowerSquares] using max_le hy hx
  | succ n ih =>
    rw [lowerSquares, pow_succ (2 : ℕ), pow_mul]
    have hr := roundDown_le ((lowerSquares n x) ^ 2)
    have hr' : (roundDown ((lowerSquares n x) ^ 2) : ℝ) ≤ (lowerSquares n x : ℝ) ^ 2 := by
      exact_mod_cast hr
    exact hr'.trans (pow_le_pow_left₀ (by exact_mod_cast lowerSquares_nonneg n x) ih _)
private theorem roundedStep_spec (x : ℚ) (k : ℕ) (hk : 0 < k) (r : ℤ) :
    |(scaledInt (roundedStep x k r) : ℝ) -
      (1 + (x : ℝ) / k * (scaledInt r : ℝ))| ≤ 1 / (intScale : ℝ) := by
  let m : ℤ := x.num * r
  let d : ℤ := (x.den : ℤ) * k
  let f : ℤ := m / d
  have hden : 0 < d := mul_pos (by exact_mod_cast x.den_pos) (by exact_mod_cast hk)
  have hden' : (0 : ℝ) < d := by exact_mod_cast hden
  have hlo : (f : ℝ) * d ≤ m := by exact_mod_cast Int.ediv_mul_le m hden.ne'
  have hhi : (m : ℝ) < ((f : ℝ) + 1) * d := by
    exact_mod_cast Int.lt_ediv_add_one_mul_self m hden
  have hround : |(f : ℝ) - (m : ℝ) / d| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith only [(div_lt_iff₀ hden').2 hhi]
    · linarith only [(le_div_iff₀ hden').2 hlo]
  have hpos : (0 : ℝ) < intScale := by norm_num [intScale]
  have heval : (scaledInt (roundedStep x k r) : ℝ) = 1 + (f : ℝ) / intScale := by
    change ((((intScale + f : ℤ) : ℚ) / intScale : ℚ) : ℝ) = _
    push_cast
    rw [add_div, div_self hpos.ne']
  have hm : ((m : ℝ) / d) / intScale = (x : ℝ) / k * (scaledInt r : ℝ) := by
    dsimp [m, d, scaledInt]
    push_cast
    rw [Rat.cast_def x]
    ring
  rw [heval, ← hm]
  rw [show (1 + (f : ℝ) / intScale) - (1 + (m : ℝ) / d / intScale) =
      ((f : ℝ) - (m : ℝ) / d) / intScale by ring, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right hround hpos.le
private theorem roundedHorner_spec (x : ℚ) (hx : |(x : ℝ)| ≤ 1)
    (n : ℕ) (r : ℤ) (v : ℝ) :
    |(scaledInt (roundedHorner x n r) : ℝ) - Real.expNear n (x : ℝ) v| ≤
      |(scaledInt r : ℝ) - v| + n / (intScale : ℝ) := by
  induction n generalizing r v with
  | zero => simp [roundedHorner]
  | succ n ih =>
    rw [roundedHorner, Real.expNear_succ]
    apply (ih _ _).trans
    have hstep := roundedStep_spec x (n + 1) n.succ_pos r
    have hfact : |(x : ℝ) / (n + 1)| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
      exact (div_le_iff₀ (by positivity)).2 (by linarith)
    have htail : |1 + (x : ℝ) / (n + 1) * (scaledInt r : ℝ) -
        (1 + (x : ℝ) / (n + 1) * v)| ≤ |(scaledInt r : ℝ) - v| := by
      rw [show ∀ a b c : ℝ, 1 + a * b - (1 + a * c) = a * (b - c) by
        intros; ring, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hfact
    push_cast at hstep
    have ht := (abs_sub_le (scaledInt (roundedStep x (n + 1) r) : ℝ)
      (1 + (x : ℝ) / (n + 1) * (scaledInt r : ℝ)) (1 + (x : ℝ) / (n + 1) * v)).trans
      (add_le_add hstep htail)
    push_cast
    rw [add_div]
    linarith only [ht]
private theorem expNear_error {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - Real.expNear 16 x 0| ≤ 1 / (intScale : ℝ) := by
  have h := Real.exp_approx_end 15 16 x rfl hx
  refine h.trans ?_
  have hpow : |x| ^ (16 : ℕ) ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg x) hx 16
  norm_num [Nat.factorial, intScale] at *
  nlinarith only [hpow]
private theorem scaledHorner_error (x : ℚ) (hx : |(x : ℝ)| ≤ 1) :
    |Real.exp (x : ℝ) - (scaledInt (roundedHorner x 16 0) : ℝ)| ≤
      17 / (intScale : ℝ) := by
  apply (abs_sub_le _ (Real.expNear 16 (x : ℝ) 0) _).trans
  have h := roundedHorner_spec x hx 16 0 0
  simp [scaledInt] at h
  have h' := expNear_error hx
  rw [abs_sub_comm (Real.expNear 16 (x : ℝ) 0)]
  norm_num [intScale] at *
  dsimp [scaledInt]
  norm_num [intScale]
  linarith only [h, h']
private theorem scaledInt_square (z : ℤ) :
    (scaledInt z) ^ 2 * scale = ((z * z : ℤ) : ℚ) / ((1000000000000 : ℕ) : ℚ) := by
  norm_num [scaledInt, intScale, scale]
  ring
private theorem cast_roundedLowerSquares (n : ℕ) (r : ℤ) :
    scaledInt (roundedLowerSquares n r) = lowerSquares n (scaledInt r) := by
  induction n with
  | zero =>
    rw [roundedLowerSquares, lowerSquares]
    rcases le_total 0 r with h | h
    · rw [max_eq_right h, max_eq_right]
      apply div_nonneg (by exact_mod_cast h) (by norm_num [intScale])
    · rw [max_eq_left h, max_eq_left]
      · simp [scaledInt]
      · apply div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (by norm_num [intScale])
  | succ n ih =>
    rw [lowerSquares, ← ih, roundDown, scaledInt_square, Rat.floor_intCast_div_natCast]
    rfl
end ExpBounds
open ExpBounds
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter
open ExpBounds
namespace GaussianPerimeter
theorem _root_.solution (x : ℚ) : (expLower x : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLower
  split_ifs with hx
  · have hx' : |(x : ℝ)| ≤ 32 := by exact_mod_cast hx
    have he := scaledHorner_error (x / 32) (by
      push_cast
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
      linarith)
    rw [← show (32 : ℝ) * ((x : ℝ) / 32) = (x : ℝ) by ring,
      show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num,
      Real.exp_nat_mul]
    rw [cast_roundedLowerSquares]
    apply lowerSquares_le_pow 5 _ (Real.exp_nonneg _)
    unfold scaledInt at he ⊢
    push_cast at he ⊢
    rw [sub_div]
    linarith only [(abs_le.mp he).1]
  · simpa using Real.exp_nonneg (x : ℝ)
end GaussianPerimeter
