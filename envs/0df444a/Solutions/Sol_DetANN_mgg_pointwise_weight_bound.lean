-- Prove2me | solution 1 for DetANN.mgg_pointwise_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-14T21:27:50.871438+00:00
-- url     : https://prove2.me/submissions/f32a2016-e760-4749-b9ee-9fdb5eb14531

import Mathlib
import Definitions.Def_DetANN_MGGOrder

-- ===== MGG_D1 =====
/-! MGG child D, sub-step D1: distance-to-the-nearest-multiple arithmetic on `ℤ`. -/

namespace DetANNMGGD

/-- `dm m t = |valMinAbs (t mod m)|`, the distance from the integer `t` to the nearest multiple of `m`. -/
def dm (m : ℕ) (t : ℤ) : ℕ := ((t : ZMod m).valMinAbs).natAbs

variable {m : ℕ} [NeZero m]
set_option linter.unusedSectionVars false

/-- `dm m t ≤ |t - k m|` for every integer `k` (minimality of `valMinAbs`). -/
lemma dm_le (t k : ℤ) : dm m t ≤ (t - k * m).natAbs := by
  unfold dm
  refine ZMod.natAbs_min_of_le_div_two m _ _ ?_ (ZMod.natAbs_valMinAbs_le _)
  rw [ZMod.coe_valMinAbs]
  push_cast
  simp

lemma dm_le_natAbs (t : ℤ) : dm m t ≤ t.natAbs := by
  simpa using dm_le (m := m) t 0

lemma dm_neg (t : ℤ) : dm m (-t) = dm m t := by
  unfold dm
  rw [Int.cast_neg, ZMod.natAbs_valMinAbs_neg]

lemma dm_add_mul (t k : ℤ) : dm m (t + k * m) = dm m t := by
  unfold dm
  congr 2
  push_cast
  simp

lemma two_mul_dm_le (t : ℤ) : 2 * dm m t ≤ m := by
  have := ZMod.natAbs_valMinAbs_le (n := m) (t : ZMod m)
  unfold dm
  omega

/-- On `0 ≤ t ≤ m` the distance is `min t (m - t)`. -/
lemma dm_eq_min (t : ℤ) (h0 : 0 ≤ t) (h1 : t ≤ m) :
    (dm m t : ℤ) = min t (m - t) := by
  rcases lt_or_eq_of_le h1 with hlt | heq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hn : n < m := by exact_mod_cast hlt
    unfold dm
    rw [Int.cast_natCast, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast_of_lt hn]
    push_cast [Nat.cast_sub hn.le]
    rfl
  · subst heq
    unfold dm
    simp

/-- Lower bound form: on `0 ≤ t ≤ m`, `dm m t > r` iff both `t > r` and `m - t > r`. -/
lemma lt_dm_iff (t : ℤ) (r : ℕ) (h0 : 0 ≤ t) (h1 : t ≤ m) :
    r < dm m t ↔ (r : ℤ) < t ∧ (r : ℤ) < m - t := by
  have := dm_eq_min (m := m) t h0 h1
  constructor
  · intro h
    have h' : (r : ℤ) < dm m t := by exact_mod_cast h
    rw [this] at h'
    exact ⟨lt_of_lt_of_le h' (min_le_left _ _), lt_of_lt_of_le h' (min_le_right _ _)⟩
  · rintro ⟨ha, hb⟩
    have : (r : ℤ) < dm m t := by rw [this]; exact lt_min ha hb
    exact_mod_cast this

end DetANNMGGD

-- ===== MGG_D2 =====
/-! MGG child D, sub-step D2: reduction of the `ZMod` statement to a statement about naturals
`x = |z̃₁|`, `y = |z̃₂|`. -/

open DetANN

namespace DetANNMGGD

/-- The weight of a move that changes one coordinate from distance `r` to distance `d`. -/
noncomputable def wt (r d : ℕ) : ℝ :=
  if r < d then (Real.sqrt 2)⁻¹ else if d < r then Real.sqrt 2 else 1

/-- The local sum in the variables `x = |z̃₁|`, `y = |z̃₂|`. -/
noncomputable def Qcore (m x y : ℕ) : ℝ :=
  Real.cos (Real.pi * x / m) *
      (wt y (dm m ((y : ℤ) + 2 * x)) + wt y (dm m ((y : ℤ) - 2 * x))) +
    Real.cos (Real.pi * y / m) *
      (wt x (dm m ((x : ℤ) + 2 * y)) + wt x (dm m ((x : ℤ) - 2 * y)))

variable {m : ℕ} [NeZero m]
set_option linter.unusedSectionVars false

/-- Notation-free distance of a residue from `0`. -/
abbrev nd (u : ZMod m) : ℕ := u.valMinAbs.natAbs

/-- A move changing only the second coordinate: the weight is a comparison of naturals. -/
lemma weight_snd (z : ZMod m × ZMod m) (w : ZMod m) :
    mggWeight (Real.sqrt 2) z (z.1, w) = wt (nd z.2) (nd w) := by
  unfold mggWeight mggFarther wt
  simp only
  by_cases h : nd z.2 < nd w
  · rw [if_pos ⟨le_refl _, h.le, Or.inr h⟩, if_pos h]
  · rw [if_neg (by rintro ⟨_, _, h3 | h3⟩; exacts [absurd h3 (lt_irrefl _), h h3]), if_neg h]
    by_cases h' : nd w < nd z.2
    · rw [if_pos ⟨le_refl _, h'.le, Or.inr h'⟩, if_pos h']
    · rw [if_neg (by rintro ⟨_, _, h3 | h3⟩; exacts [absurd h3 (lt_irrefl _), h' h3]), if_neg h']

/-- A move changing only the first coordinate. -/
lemma weight_fst (z : ZMod m × ZMod m) (w : ZMod m) :
    mggWeight (Real.sqrt 2) z (w, z.2) = wt (nd z.1) (nd w) := by
  unfold mggWeight mggFarther wt
  simp only
  by_cases h : nd z.1 < nd w
  · rw [if_pos ⟨h.le, le_refl _, Or.inl h⟩, if_pos h]
  · rw [if_neg (by rintro ⟨_, _, h3 | h3⟩; exacts [h h3, absurd h3 (lt_irrefl _)]), if_neg h]
    by_cases h' : nd w < nd z.1
    · rw [if_pos ⟨h'.le, le_refl _, Or.inl h'⟩, if_pos h']
    · rw [if_neg (by rintro ⟨_, _, h3 | h3⟩; exacts [h' h3, absurd h3 (lt_irrefl _)]), if_neg h']

lemma nd_add (u v : ZMod m) : nd (u + 2 * v) = dm m (u.valMinAbs + 2 * v.valMinAbs) := by
  unfold dm nd
  push_cast
  rfl

lemma nd_sub (u v : ZMod m) : nd (u - 2 * v) = dm m (u.valMinAbs - 2 * v.valMinAbs) := by
  unfold dm nd
  push_cast
  rfl

lemma dm_eq_of_eq_neg {t s : ℤ} (h : t = -s) : dm m t = dm m s := by
  rw [h, dm_neg]

/-- The pair sum depends only on `|a| = x` and `|b| = y`. -/
lemma pair_sign (x y : ℕ) (a b : ℤ) (ha : a = x ∨ a = -x) (hb : b = y ∨ b = -y) :
    wt y (dm m (b + 2 * a)) + wt y (dm m (b - 2 * a)) =
      wt y (dm m ((y : ℤ) + 2 * x)) + wt y (dm m ((y : ℤ) - 2 * x)) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · rw [dm_eq_of_eq_neg (t := -(y : ℤ) + 2 * x) (s := (y : ℤ) - 2 * x) (by ring),
      dm_eq_of_eq_neg (t := -(y : ℤ) - 2 * x) (s := (y : ℤ) + 2 * x) (by ring), add_comm]
  · rw [show (y : ℤ) + 2 * -(x : ℤ) = y - 2 * x by ring,
      show (y : ℤ) - 2 * -(x : ℤ) = y + 2 * x by ring, add_comm]
  · rw [dm_eq_of_eq_neg (t := -(y : ℤ) + 2 * -(x : ℤ)) (s := (y : ℤ) + 2 * x) (by ring),
      dm_eq_of_eq_neg (t := -(y : ℤ) - 2 * -(x : ℤ)) (s := (y : ℤ) - 2 * x) (by ring)]

lemma two_mul_nd_le (u : ZMod m) : 2 * nd u ≤ m := by
  have := ZMod.natAbs_valMinAbs_le u
  show 2 * u.valMinAbs.natAbs ≤ m
  omega

/-- `|cos(π ũ/m)| = cos(π |ũ|/m)`, since `|ũ| ≤ m/2`. -/
lemma abs_cos_eq (u : ZMod m) :
    |Real.cos (Real.pi * (u.valMinAbs : ℝ) / m)| = Real.cos (Real.pi * (nd u : ℝ) / m) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h2 : (2 * nd u : ℝ) ≤ m := by exact_mod_cast two_mul_nd_le u
  have hcos : 0 ≤ Real.cos (Real.pi * (nd u : ℝ) / m) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ Real.pi * (nd u : ℝ) / m := by positivity
      linarith [Real.pi_pos]
    · rw [div_le_iff₀ hm]
      nlinarith [Real.pi_pos]
  have hcast : ((nd u : ℕ) : ℝ) = |(u.valMinAbs : ℝ)| := by
    show ((u.valMinAbs.natAbs : ℕ) : ℝ) = _
    rw [Nat.cast_natAbs, Int.cast_abs]
  have harg : Real.pi * |(u.valMinAbs : ℝ)| / m = |Real.pi * (u.valMinAbs : ℝ) / m| := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hm]
  rw [hcast, harg, Real.cos_abs] at hcos ⊢
  exact abs_of_nonneg hcos

/-- **D2.** Child D follows from the inequality for `Qcore` on naturals. -/
theorem pointwise_of_core
    (hcore : ∀ x y : ℕ, 2 * x ≤ m → 2 * y ≤ m → (x ≠ 0 ∨ y ≠ 0) →
      Qcore m x y ≤ 5 * Real.sqrt 2 / 2)
    (z : ZMod m × ZMod m) (hz : z ≠ 0) :
    |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1, z.2 + 2 * z.1) +
          mggWeight (Real.sqrt 2) z (z.1, z.2 - 2 * z.1)) +
      |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1 + 2 * z.2, z.2) +
          mggWeight (Real.sqrt 2) z (z.1 - 2 * z.2, z.2))
      ≤ 5 * Real.sqrt 2 / 2 := by
  have hne : nd z.1 ≠ 0 ∨ nd z.2 ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    apply hz
    have h1 : z.1.valMinAbs = 0 := Int.natAbs_eq_zero.1 h.1
    have h2 : z.2.valMinAbs = 0 := Int.natAbs_eq_zero.1 h.2
    rw [ZMod.valMinAbs_eq_zero] at h1 h2
    exact Prod.ext h1 h2
  have key := hcore (nd z.1) (nd z.2) (two_mul_nd_le _) (two_mul_nd_le _) hne
  rw [weight_snd, weight_snd, weight_fst, weight_fst, abs_cos_eq, abs_cos_eq,
    nd_add, nd_sub, nd_add, nd_sub]
  unfold Qcore at key
  rw [pair_sign (nd z.1) (nd z.2) _ _ (Int.natAbs_eq _) (Int.natAbs_eq _),
    pair_sign (nd z.2) (nd z.1) _ _ (Int.natAbs_eq _) (Int.natAbs_eq _)]
  exact key

end DetANNMGGD

-- ===== MGG_D3 =====
/-! MGG child D, sub-step D3: the trigonometric facts used in the six cases.
Throughout, `x, y` are naturals with `2x ≤ m`, `2y ≤ m`, so the angles `πx/m`, `πy/m` lie in
`[0, π/2]`. -/

namespace DetANNMGGD

open Real

variable {m : ℕ}

lemma angle_nonneg (x : ℕ) : 0 ≤ π * (x : ℝ) / m := by positivity

lemma angle_le_half_pi (hm : 0 < m) (x : ℕ) (hx : 2 * x ≤ m) : π * (x : ℝ) / m ≤ π / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx' : (2 * x : ℝ) ≤ m := by exact_mod_cast hx
  rw [div_le_div_iff₀ hm' (by norm_num)]
  nlinarith [pi_pos]

/-- **T1.** `0 ≤ cos(πx/m) ≤ 1`. -/
lemma cos_angle_nonneg (hm : 0 < m) (x : ℕ) (hx : 2 * x ≤ m) : 0 ≤ cos (π * (x : ℝ) / m) :=
  cos_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg (m := m) x, pi_pos], angle_le_half_pi hm x hx⟩

lemma cos_angle_le_one (x : ℕ) : cos (π * (x : ℝ) / m) ≤ 1 := cos_le_one _

/-- **T2.** `cos(πx/m) = 0` when `2x = m`. -/
lemma cos_angle_eq_zero (hm : 0 < m) (x : ℕ) (hx : 2 * x = m) : cos (π * (x : ℝ) / m) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have : π * (x : ℝ) / m = π / 2 := by
    rw [div_eq_div_iff hm' (by norm_num)]
    have : (2 * x : ℝ) = m := by exact_mod_cast hx
    rw [← this]; ring
  rw [this, cos_pi_div_two]

/-- **T3.** `cos(πx/m) ≤ √2/2` when `m ≤ 4x` (and `2x ≤ m`). -/
lemma cos_angle_le_sqrt_two_div_two (hm : 0 < m) (x : ℕ) (hx : 2 * x ≤ m) (h4 : m ≤ 4 * x) :
    cos (π * (x : ℝ) / m) ≤ √2 / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h4' : (m : ℝ) ≤ 4 * x := by exact_mod_cast h4
  rw [← cos_pi_div_four]
  apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · linarith [angle_le_half_pi hm x hx, pi_pos]
  · rw [div_le_div_iff₀ (by norm_num) hm']
    nlinarith [pi_pos]

/-- **T4.** `cos(πy/m) ≤ sin(πx/m)` when `m ≤ 2(x + y)` (and `2x, 2y ≤ m`). -/
lemma cos_angle_le_sin_angle (hm : 0 < m) (x y : ℕ) (hx : 2 * x ≤ m) (hy : 2 * y ≤ m)
    (hxy : m ≤ 2 * (x + y)) : cos (π * (y : ℝ) / m) ≤ sin (π * (x : ℝ) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hxy' : (m : ℝ) ≤ 2 * (x + y) := by exact_mod_cast hxy
  rw [← cos_pi_div_two_sub]
  apply cos_le_cos_of_nonneg_of_le_pi
  · linarith [angle_le_half_pi hm x hx]
  · linarith [angle_le_half_pi hm y hy, pi_pos]
  · have : π / 2 ≤ π * (x : ℝ) / m + π * (y : ℝ) / m := by
      rw [← add_div, div_le_div_iff₀ (by norm_num) hm']
      nlinarith [pi_pos]
    linarith

/-- **T5 (amplitude).** `A cos t + B sin t ≤ K` whenever `A² + B² ≤ K²` and `0 ≤ K`. -/
lemma amplitude_le (A B K t : ℝ) (hK : 0 ≤ K) (h : A ^ 2 + B ^ 2 ≤ K ^ 2) :
    A * cos t + B * sin t ≤ K := by
  have hid : (A * cos t + B * sin t) ^ 2 + (A * sin t - B * cos t) ^ 2 = A ^ 2 + B ^ 2 := by
    have := sin_sq_add_cos_sq t
    linear_combination (A ^ 2 + B ^ 2) * this
  have hsq : (A * cos t + B * sin t) ^ 2 ≤ K ^ 2 := by
    nlinarith [sq_nonneg (A * sin t - B * cos t)]
  exact (abs_le_of_sq_le_sq' hsq hK).2

end DetANNMGGD

-- ===== MGG_D4 =====
/-! MGG child D, sub-step D4: the six cases C0–C5 of the inequality `Qcore m x y ≤ 5√2/2`
-/

namespace DetANNMGGD

open Real

variable {m : ℕ} [NeZero m]
set_option linter.unusedSectionVars false

/-! ### `√2` and the three weight values -/

lemma sqrt2_pos : 0 < √2 := by positivity
lemma sqrt2_sq : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
lemma sqrt2_inv : (√2)⁻¹ = √2 / 2 := by
  have h : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  rw [eq_div_iff (by norm_num), inv_mul_eq_iff_eq_mul₀ sqrt2_pos.ne']
  exact h.symm
lemma four_thirds_le_sqrt2 : (4 / 3 : ℝ) ≤ √2 := by
  nlinarith [sqrt2_sq, sqrt2_pos]
lemma one_le_sqrt2 : (1 : ℝ) ≤ √2 := by linarith [four_thirds_le_sqrt2]

lemma wt_out' {r d : ℕ} (h : r < d) : wt r d = √2 / 2 := by
  unfold wt; rw [if_pos h, sqrt2_inv]
lemma wt_in' {r d : ℕ} (h : d < r) : wt r d = √2 := by
  unfold wt; rw [if_neg (by omega), if_pos h]
lemma wt_level' {r d : ℕ} (h : d = r) : wt r d = 1 := by
  unfold wt; rw [if_neg (by omega), if_neg (by omega)]
lemma wt_le_sqrt2 (r d : ℕ) : wt r d ≤ √2 := by
  unfold wt
  split_ifs
  · rw [sqrt2_inv]; linarith [sqrt2_pos]
  · exact le_refl _
  · exact one_le_sqrt2
lemma wt_nonneg (r d : ℕ) : 0 ≤ wt r d := by
  unfold wt
  split_ifs <;> positivity

/-! ### From distance facts to weights -/

/-- An outward move: `0 ≤ t ≤ m`, `r < t`, `r < m - t`. -/
lemma wt_out (r : ℕ) (t : ℤ) (h0 : 0 ≤ t) (h1 : t ≤ m) (ha : (r : ℤ) < t)
    (hb : (r : ℤ) < m - t) : wt r (dm m t) = √2 / 2 :=
  wt_out' ((lt_dm_iff t r h0 h1).2 ⟨ha, hb⟩)

lemma wt_out_neg (r : ℕ) (t : ℤ) (h0 : 0 ≤ -t) (h1 : -t ≤ m) (ha : (r : ℤ) < -t)
    (hb : (r : ℤ) < m - -t) : wt r (dm m t) = √2 / 2 := by
  rw [← dm_neg]; exact wt_out r (-t) h0 h1 ha hb

/-- An inward move: some multiple `k m` lies within distance `< r` of `t`. -/
lemma wt_in (r : ℕ) (t k : ℤ) (h1 : t - k * m < r) (h2 : -(r : ℤ) < t - k * m) :
    wt r (dm m t) = √2 := by
  apply wt_in'
  have hle := dm_le (m := m) t k
  have : ((t - k * m).natAbs : ℤ) < r := by
    rw [Int.natCast_natAbs]; exact abs_lt.2 ⟨h2, h1⟩
  have : (t - k * m).natAbs < r := by exact_mod_cast this
  omega

/-- A level move: `0 ≤ t ≤ m` and `min t (m - t) = r`. -/
lemma wt_level (r : ℕ) (t : ℤ) (h0 : 0 ≤ t) (h1 : t ≤ m) (h : min t (m - t) = r) :
    wt r (dm m t) = 1 := by
  apply wt_level'
  have := dm_eq_min (m := m) t h0 h1
  rw [h] at this
  exact_mod_cast this

lemma wt_level_neg (r : ℕ) (t : ℤ) (h0 : 0 ≤ -t) (h1 : -t ≤ m) (h : min (-t) (m - -t) = r) :
    wt r (dm m t) = 1 := by
  rw [← dm_neg]; exact wt_level r (-t) h0 h1 h

/-! ### The six cases (with `y ≤ x`, `x ≥ 1`) -/

lemma core_le_of_le (x y : ℕ) (hx : 2 * x ≤ m) (hy : 2 * y ≤ m) (hyx : y ≤ x) (hx0 : 0 < x) :
    Qcore m x y ≤ 5 * √2 / 2 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hr := sqrt2_pos
  have hr2 := sqrt2_sq
  have hr43 := four_thirds_le_sqrt2
  have hAx0 := cos_angle_nonneg hm x hx
  have hAy0 := cos_angle_nonneg hm y hy
  have hAx1 := cos_angle_le_one (m := m) x
  have hAy1 := cos_angle_le_one (m := m) y
  unfold Qcore
  set Ax := cos (π * (x : ℝ) / m) with hAx
  set Ay := cos (π * (y : ℝ) / m) with hAy
  rcases Nat.eq_zero_or_pos y with hy0 | hy0
  · -- C0: y = 0
    have hAy_one : Ay = 1 := by rw [hAy, hy0]; simp
    have e3 : wt x (dm m ((x : ℤ) + 2 * y)) = 1 := wt_level x _ (by omega) (by omega) (by omega)
    have e4 : wt x (dm m ((x : ℤ) - 2 * y)) = 1 := wt_level x _ (by omega) (by omega) (by omega)
    rw [hAy_one, e3, e4]
    rcases Nat.lt_or_ge (2 * x) m with h2x | h2x
    · have e1 : wt y (dm m ((y : ℤ) + 2 * x)) = √2 / 2 := wt_out y _ (by omega) (by omega)
        (by omega) (by omega)
      have e2 : wt y (dm m ((y : ℤ) - 2 * x)) = √2 / 2 := wt_out_neg y _ (by omega) (by omega)
        (by omega) (by omega)
      rw [e1, e2]
      nlinarith [mul_le_mul_of_nonneg_right hAx1 hr.le]
    · have hz : Ax = 0 := cos_angle_eq_zero hm x (by omega)
      rw [hz]
      nlinarith
  rcases Nat.lt_or_ge y x with hlt | hge
  swap
  · -- C1: y = x
    have hxy : y = x := le_antisymm hyx hge
    have e2 : wt y (dm m ((y : ℤ) - 2 * x)) = 1 :=
      wt_level_neg y _ (by omega) (by omega) (by omega)
    have e4 : wt x (dm m ((x : ℤ) - 2 * y)) = 1 :=
      wt_level_neg x _ (by omega) (by omega) (by omega)
    rw [e2, e4]
    rcases Nat.lt_or_ge (4 * x) m with h4 | h4
    · have e1 : wt y (dm m ((y : ℤ) + 2 * x)) = √2 / 2 := wt_out y _ (by omega) (by omega)
        (by omega) (by omega)
      have e3 : wt x (dm m ((x : ℤ) + 2 * y)) = √2 / 2 := wt_out x _ (by omega) (by omega)
        (by omega) (by omega)
      rw [e1, e3]
      nlinarith [mul_le_mul_of_nonneg_right hAx1 (by positivity : (0 : ℝ) ≤ √2 / 2 + 1),
        mul_le_mul_of_nonneg_right hAy1 (by positivity : (0 : ℝ) ≤ √2 / 2 + 1)]
    · have hAxs := cos_angle_le_sqrt_two_div_two hm x hx h4
      have hAys := cos_angle_le_sqrt_two_div_two hm y hy (by omega)
      have w1 := wt_le_sqrt2 y (dm m ((y : ℤ) + 2 * x))
      have w3 := wt_le_sqrt2 x (dm m ((x : ℤ) + 2 * y))
      have w1' := wt_nonneg y (dm m ((y : ℤ) + 2 * x))
      have w3' := wt_nonneg x (dm m ((x : ℤ) + 2 * y))
      have b1 : Ax * (wt y (dm m ((y : ℤ) + 2 * x)) + 1) ≤ √2 / 2 * (√2 + 1) :=
        mul_le_mul hAxs (by linarith) (by linarith) (by positivity)
      have b2 : Ay * (wt x (dm m ((x : ℤ) + 2 * y)) + 1) ≤ √2 / 2 * (√2 + 1) :=
        mul_le_mul hAys (by linarith) (by linarith) (by positivity)
      nlinarith
  -- now 0 < y < x
  rcases Nat.lt_or_ge (2 * x) m with h2x | h2x
  swap
  · -- C5: 2x = m
    have hz : Ax = 0 := cos_angle_eq_zero hm x (by omega)
    rw [hz, zero_mul, zero_add]
    have w3 := wt_le_sqrt2 x (dm m ((x : ℤ) + 2 * y))
    have w4 := wt_le_sqrt2 x (dm m ((x : ℤ) - 2 * y))
    have w3' := wt_nonneg x (dm m ((x : ℤ) + 2 * y))
    have w4' := wt_nonneg x (dm m ((x : ℤ) - 2 * y))
    have : Ay * (wt x (dm m ((x : ℤ) + 2 * y)) + wt x (dm m ((x : ℤ) - 2 * y))) ≤ 1 * (2 * √2) :=
      mul_le_mul hAy1 (by linarith) (by linarith) (by norm_num)
    nlinarith
  rcases lt_trichotomy (2 * (x + y)) m with hs | hs | hs
  · -- C2: strictly inside the diamond
    have e1 : wt y (dm m ((y : ℤ) + 2 * x)) = √2 / 2 := wt_out y _ (by omega) (by omega)
      (by omega) (by omega)
    have e2 : wt y (dm m ((y : ℤ) - 2 * x)) = √2 / 2 := wt_out_neg y _ (by omega) (by omega)
      (by omega) (by omega)
    have e3 : wt x (dm m ((x : ℤ) + 2 * y)) = √2 / 2 := wt_out x _ (by omega) (by omega)
      (by omega) (by omega)
    have e4 : wt x (dm m ((x : ℤ) - 2 * y)) = √2 := wt_in x _ 0 (by omega) (by omega)
    rw [e1, e2, e3, e4]
    nlinarith [mul_le_mul_of_nonneg_right hAx1 hr.le, mul_le_mul_of_nonneg_right hAy1 hr.le]
  · -- C3: on the diamond boundary
    have e1 : wt y (dm m ((y : ℤ) + 2 * x)) = 1 := wt_level y _ (by omega) (by omega) (by omega)
    have e2 : wt y (dm m ((y : ℤ) - 2 * x)) = √2 / 2 := wt_out_neg y _ (by omega) (by omega)
      (by omega) (by omega)
    have e3 : wt x (dm m ((x : ℤ) + 2 * y)) = 1 := wt_level x _ (by omega) (by omega) (by omega)
    have e4 : wt x (dm m ((x : ℤ) - 2 * y)) = √2 := wt_in x _ 0 (by omega) (by omega)
    rw [e1, e2, e3, e4]
    have hs' := cos_angle_le_sin_angle hm x y hx hy hs.ge
    have hamp := amplitude_le (1 + √2 / 2) (1 + √2) (5 * √2 / 2) (π * (x : ℝ) / m)
      (by positivity) (by nlinarith)
    have : Ay * (1 + √2) ≤ sin (π * (x : ℝ) / m) * (1 + √2) :=
      mul_le_mul_of_nonneg_right hs' (by positivity)
    nlinarith
  · -- C4: outside the diamond (wraparound)
    have e1 : wt y (dm m ((y : ℤ) + 2 * x)) = √2 := wt_in y _ 1 (by omega) (by omega)
    have e2 : wt y (dm m ((y : ℤ) - 2 * x)) = √2 / 2 := wt_out_neg y _ (by omega) (by omega)
      (by omega) (by omega)
    have e3 : wt x (dm m ((x : ℤ) + 2 * y)) = √2 := wt_in x _ 1 (by omega) (by omega)
    have e4 : wt x (dm m ((x : ℤ) - 2 * y)) = √2 := wt_in x _ 0 (by omega) (by omega)
    rw [e1, e2, e3, e4]
    have hs' := cos_angle_le_sin_angle hm x y hx hy hs.le
    have hamp := amplitude_le (3 * √2 / 2) (2 * √2) (5 * √2 / 2) (π * (x : ℝ) / m)
      (by positivity) (le_of_eq (by ring))
    have : Ay * (2 * √2) ≤ sin (π * (x : ℝ) / m) * (2 * √2) :=
      mul_le_mul_of_nonneg_right hs' (by positivity)
    nlinarith

lemma Qcore_comm (x y : ℕ) : Qcore m x y = Qcore m y x := by
  unfold Qcore; ring

/-- **D4.** The core inequality for all admissible `x, y`. -/
theorem core_le (x y : ℕ) (hx : 2 * x ≤ m) (hy : 2 * y ≤ m) (hne : x ≠ 0 ∨ y ≠ 0) :
    Qcore m x y ≤ 5 * √2 / 2 := by
  rcases le_total y x with h | h
  · exact core_le_of_le x y hx hy h (by omega)
  · rw [Qcore_comm]
    exact core_le_of_le y x hy hx h (by omega)

end DetANNMGGD

open DetANN DetANNMGGD in
theorem solution (m : ℕ) [NeZero m] (z : ZMod m × ZMod m) (hz : z ≠ 0) :
    |Real.cos (Real.pi * (z.1.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1, z.2 + 2 * z.1) +
          mggWeight (Real.sqrt 2) z (z.1, z.2 - 2 * z.1)) +
      |Real.cos (Real.pi * (z.2.valMinAbs : ℝ) / m)| *
        (mggWeight (Real.sqrt 2) z (z.1 + 2 * z.2, z.2) +
          mggWeight (Real.sqrt 2) z (z.1 - 2 * z.2, z.2))
      ≤ 5 * Real.sqrt 2 / 2 :=
  pointwise_of_core (fun x y hx hy hne => core_le x y hx hy hne) z hz
