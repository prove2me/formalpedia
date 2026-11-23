-- Prove2me | solution 1 for DelaunayStretch.lemma_3_6_chains_are_moves
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:56:28.181968+00:00
-- url     : https://prove2.me/submissions/9875e71e-7800-4150-971a-78bd8f0dc109

import Theorems.Thm_DelaunayStretch_lemma_3_3_exact_update
import Definitions.Def_DelaunayStretch_IsNextDisk

open DelaunayStretch Complex

namespace DelaunayStretch
namespace L36

/-! ## Elementary planar geometry -/

/-- Comparison of arguments, case `z.im > 0`. -/
theorem arg_le_of_im_pos {w z : ℂ} (hn : ‖w‖ = ‖z‖) (hz : 0 < z.im) (hre : z.re ≤ w.re) :
    Complex.arg w ≤ Complex.arg z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hn; linarith
  rw [Complex.arg_of_im_nonneg_of_ne_zero hz.le hz0]
  rcases le_or_gt 0 w.im with hw | hw
  · rw [Complex.arg_of_im_nonneg_of_ne_zero hw hw0, hn]
    exact Real.arccos_le_arccos (div_le_div_of_nonneg_right hre hzn.le)
  · have := Complex.arg_neg_iff.mpr hw
    have := Real.arccos_nonneg (z.re / ‖z‖)
    linarith

/-- Comparison of arguments, case `z.im < 0`. -/
theorem arg_le_of_im_neg {w z : ℂ} (hn : ‖w‖ = ‖z‖) (hz : z.im < 0) (hre : z.re ≤ w.re) :
    Complex.arg z ≤ Complex.arg w := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Complex.arg_of_im_neg hz]
  rcases le_or_gt 0 w.im with hw | hw
  · have := Complex.arg_nonneg_iff.mpr hw
    have := Real.arccos_nonneg (z.re / ‖z‖)
    linarith
  · rw [Complex.arg_of_im_neg hw, hn]
    have := Real.arccos_le_arccos (div_le_div_of_nonneg_right hre hzn.le)
    linarith

theorem dist_sq_eq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

/-- A point `u` of the circle `|p - o| = r` on the axis, with an axis point `c` of the closed
disk to its right, lies strictly left of the center (so `u = w₋`). -/
theorem left_of_center {o u c : ℂ} {r : ℝ} (hu : dist u o = r) (hui : u.im = 0)
    (hc : dist c o ≤ r) (hci : c.im = 0) (hlt : u.re < c.re) : u.re < o.re := by
  have h1 := dist_sq_eq u o
  have h2 := dist_sq_eq c o
  have h0 : 0 ≤ dist c o := dist_nonneg
  have h3 : dist c o ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hc 2
  rw [hu] at h1
  rw [hui] at h1; rw [hci] at h2
  by_contra h
  rw [not_lt] at h
  nlinarith

/-- Mirror image of `left_of_center` (so `v = w₊`). -/
theorem right_of_center {o v c : ℂ} {r : ℝ} (hv : dist v o = r) (hvi : v.im = 0)
    (hc : dist c o ≤ r) (hci : c.im = 0) (hlt : c.re < v.re) : o.re < v.re := by
  have h1 := dist_sq_eq v o
  have h2 := dist_sq_eq c o
  have h0 : 0 ≤ dist c o := dist_nonneg
  have h3 : dist c o ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hc 2
  rw [hv] at h1
  rw [hvi] at h1; rw [hci] at h2
  by_contra h
  rw [not_lt] at h
  nlinarith

theorem axisCrossing_im {a b : ℂ} (ha : 0 < a.im) (hb : b.im < 0) :
    (axisCrossing a b).im = 0 := by
  unfold axisCrossing
  have hne : a.im - b.im ≠ 0 := by linarith
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.sub_re, zero_mul, add_zero]
  field_simp
  ring

/-- The axis crossing of a chord of a circle lies in the closed disk. -/
theorem axisCrossing_dist {a b o : ℂ} {r : ℝ} (ha : 0 < a.im) (hb : b.im < 0)
    (hao : dist a o = r) (hbo : dist b o = r) : dist (axisCrossing a b) o ≤ r := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = a.im / (a.im - b.im) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg ha.le (by linarith)
  have ht1 : t ≤ 1 := by rw [ht]; exact (div_le_one (by linarith)).mpr (by linarith)
  have e : axisCrossing a b - o = ((1 - t : ℝ) : ℂ) * (a - o) + (t : ℂ) * (b - o) := by
    unfold axisCrossing; rw [← ht]; push_cast; ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * (a - o)‖ + ‖(t : ℂ) * (b - o)‖ := norm_add_le _ _
    _ = (1 - t) * r + t * r := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0, ← dist_eq_norm,
          ← dist_eq_norm, hao, hbo]
    _ = r := by ring

theorem norm_rot (O : Disk) {p : ℂ} (hp : p ∈ O.boundary) (s : ℂ) (hs : ‖s‖ = 1) :
    ‖(p - O.center) * s‖ = O.radius := by
  rw [norm_mul, hs, mul_one, ← dist_eq_norm]; exact hp

/-- Polar representation through the upper angle parameter. -/
theorem upper_repr (O : Disk) {p : ℂ} (hp : p ∈ O.boundary) :
    p - O.center = (O.radius : ℂ) * exp ((O.upperAngle p : ℂ) * I) := by
  have key := Complex.norm_mul_exp_arg_mul_I ((p - O.center) * (-I))
  rw [norm_rot O hp _ (by simp)] at key
  unfold Disk.upperAngle
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  calc p - O.center = I * ((p - O.center) * -I) := by
        linear_combination (p - O.center) * Complex.I_sq
    _ = I * ((O.radius : ℂ) * exp ((arg ((p - O.center) * -I) : ℂ) * I)) := by rw [key]
    _ = _ := by ring

/-- Polar representation through the lower angle parameter. -/
theorem lower_repr (O : Disk) {p : ℂ} (hp : p ∈ O.boundary) :
    p - O.center = (O.radius : ℂ) * exp ((O.lowerAngle p : ℂ) * I) := by
  have key := Complex.norm_mul_exp_arg_mul_I ((p - O.center) * I)
  rw [norm_rot O hp _ (by simp)] at key
  unfold Disk.lowerAngle
  have e3 : exp ((3 * (Real.pi : ℂ) / 2) * I) = -I := by
    have : (3 * (Real.pi : ℂ) / 2) * I = Real.pi * I + Real.pi / 2 * I := by ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]; ring
  push_cast
  rw [add_mul, Complex.exp_add, e3]
  calc p - O.center = -I * ((p - O.center) * I) := by
        linear_combination (p - O.center) * Complex.I_sq
    _ = -I * ((O.radius : ℂ) * exp ((arg ((p - O.center) * I) : ℂ) * I)) := by rw [key]
    _ = _ := by ring

/-- Chord length is at most `r` times the angle difference. -/
theorem chord_le {o p q : ℂ} {r θ φ : ℝ} (hr : 0 ≤ r) (hp : p - o = r * exp (θ * I))
    (hq : q - o = r * exp (φ * I)) : dist p q ≤ r * |θ - φ| := by
  have e1 : p - q = r * exp (φ * I) * (exp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    have : p - q = (p - o) - (q - o) := by ring
    rw [this, hp, hq]
    have e : exp (θ * I) = exp (φ * I) * exp (I * ((θ - φ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  rw [dist_eq_norm, e1, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  gcongr
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - φ)
  simpa [Real.norm_eq_abs] using this

/-! ## Index conventions -/

theorem A_zero (C : DiskChain) : C.A 0 = C.u := by simp [DiskChain.A]
theorem B_zero (C : DiskChain) : C.B 0 = C.u := by simp [DiskChain.B]
theorem c_zero (C : DiskChain) : C.c 0 = C.u := by simp [DiskChain.c]

theorem A_n (C : DiskChain) (h : 1 ≤ C.n) : C.A C.n = C.v := by
  unfold DiskChain.A; rw [if_neg (by omega), if_pos rfl]
theorem B_n (C : DiskChain) (h : 1 ≤ C.n) : C.B C.n = C.v := by
  unfold DiskChain.B; rw [if_neg (by omega), if_pos rfl]
theorem c_n (C : DiskChain) (h : 1 ≤ C.n) : C.c C.n = C.v := by
  unfold DiskChain.c; rw [if_neg (by omega), if_pos rfl]

theorem A_mid (C : DiskChain) {i : ℕ} (h1 : 1 ≤ i) (h2 : i < C.n) : C.A i = C.a i := by
  unfold DiskChain.A; rw [if_neg (by omega), if_neg (by omega)]
theorem B_mid (C : DiskChain) {i : ℕ} (h1 : 1 ≤ i) (h2 : i < C.n) : C.B i = C.b i := by
  unfold DiskChain.B; rw [if_neg (by omega), if_neg (by omega)]
theorem c_mid (C : DiskChain) {i : ℕ} (h1 : 1 ≤ i) (h2 : i < C.n) :
    C.c i = axisCrossing (C.a i) (C.b i) := by
  unfold DiskChain.c; rw [if_neg (by omega), if_neg (by omega)]

theorem gate_zero (C : DiskChain) : C.gateLength 0 = 0 := by
  simp [DiskChain.gateLength, A_zero, B_zero]

theorem gate_n (C : DiskChain) (h : 1 ≤ C.n) : C.gateLength C.n = 0 := by
  simp [DiskChain.gateLength, A_n C h, B_n C h]

theorem gate_nonneg (C : DiskChain) (i : ℕ) : 0 ≤ C.gateLength i := dist_nonneg

/-- (C1) unpacked. -/
theorem C1_facts (C : DiskChain) (hC : C.IsDiskChain) {i : ℕ} (h1 : 1 ≤ i) (h2 : i + 1 ≤ C.n) :
    C.a i ∈ (C.O i).boundary ∧ C.a i ∈ (C.O (i + 1)).boundary ∧
    C.b i ∈ (C.O i).boundary ∧ C.b i ∈ (C.O (i + 1)).boundary ∧
    0 < (C.a i).im ∧ (C.b i).im < 0 := by
  obtain ⟨-, -, -, -, -, -, -, hC1, -⟩ := hC
  obtain ⟨hs, ha, hb⟩ := hC1 i h1 h2
  have hA : C.a i ∈ (C.O i).boundary ∩ (C.O (i + 1)).boundary := by rw [hs]; simp
  have hB : C.b i ∈ (C.O i).boundary ∩ (C.O (i + 1)).boundary := by rw [hs]; simp
  exact ⟨hA.1, hA.2, hB.1, hB.2, ha, hb⟩

/-- Both ends of both rails of `Oᵢ` lie on `∂Oᵢ`. -/
theorem ends_mem (C : DiskChain) (hC : C.IsDiskChain) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ C.n) :
    C.A (i - 1) ∈ (C.O i).boundary ∧ C.A i ∈ (C.O i).boundary ∧
    C.B (i - 1) ∈ (C.O i).boundary ∧ C.B i ∈ (C.O i).boundary := by
  have hC' := hC
  obtain ⟨hn1, -, -, -, hu, hv, -⟩ := hC'
  have hl : C.A (i - 1) ∈ (C.O i).boundary ∧ C.B (i - 1) ∈ (C.O i).boundary := by
    rcases (show i = 1 ∨ 2 ≤ i by omega) with rfl | hi
    · simp only [Nat.sub_self, A_zero, B_zero]; exact ⟨hu, hu⟩
    · have := C1_facts C hC (i := i - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
      rw [A_mid C (by omega) (by omega), B_mid C (by omega) (by omega)]
      exact ⟨this.2.1, this.2.2.2.1⟩
  have hr : C.A i ∈ (C.O i).boundary ∧ C.B i ∈ (C.O i).boundary := by
    rcases (show i = C.n ∨ i + 1 ≤ C.n by omega) with rfl | hi
    · rw [A_n C hn1, B_n C hn1]; exact ⟨hv, hv⟩
    · have := C1_facts C hC (i := i) h1 hi
      rw [A_mid C h1 (by omega), B_mid C h1 (by omega)]
      exact ⟨this.1, this.2.2.1⟩
  exact ⟨hl.1, hr.1, hl.2, hr.2⟩

/-- `u` lies strictly left of the center of `O₁` (so `u = w₋(O₁)`). -/
theorem u_left (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    C.u.re < (C.O 1).center.re := by
  have hC' := hC
  obtain ⟨-, -, hu0, -, hu, -, -, -, -, hC3, -⟩ := hC'
  obtain ⟨ha1, -, hb1, -, hai, hbi⟩ := C1_facts C hC (i := 1) le_rfl (by omega)
  have hc3 := hC3 0 (by omega)
  rw [c_zero, show (0 : ℕ) + 1 = 1 from rfl, c_mid C le_rfl (by omega)] at hc3
  exact left_of_center hu hu0 (axisCrossing_dist hai hbi ha1 hb1) (axisCrossing_im hai hbi) hc3

/-- `v` lies strictly right of the center of `Oₙ` (so `v = w₊(Oₙ)`). -/
theorem v_right (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    (C.O C.n).center.re < C.v.re := by
  have hC' := hC
  obtain ⟨-, -, -, hv0, -, hv, -, -, -, hC3, -⟩ := hC'
  have hf := C1_facts C hC (i := C.n - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ C.n)] at hf
  obtain ⟨-, ha1, -, hb1, hai, hbi⟩ := hf
  have hc3 := hC3 (C.n - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ C.n), c_n C (by omega),
    c_mid C (by omega) (by omega)] at hc3
  exact right_of_center hv hv0 (axisCrossing_dist hai hbi ha1 hb1) (axisCrossing_im hai hbi) hc3

theorem u_eq_wMinus (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    C.u = (C.O 1).wMinus := by
  have hC' := hC
  obtain ⟨-, -, hu0, -, hu, -⟩ := hC'
  have hl := u_left C hC hn
  have h1 := dist_sq_eq C.u (C.O 1).center
  rw [show dist C.u (C.O 1).center = (C.O 1).radius from hu, hu0] at h1
  apply Complex.ext
  · simp only [Disk.wMinus, Disk.axisHalfChord]
    have : Real.sqrt ((C.O 1).radius ^ 2 - (C.O 1).center.im ^ 2) =
        (C.O 1).center.re - C.u.re := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by linarith)]; nlinarith
    rw [this]; ring
  · simp [Disk.wMinus, hu0]

theorem v_eq_wPlus (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    C.v = (C.O C.n).wPlus := by
  have hC' := hC
  obtain ⟨-, -, -, hv0, -, hv, -⟩ := hC'
  have hl := v_right C hC hn
  have h1 := dist_sq_eq C.v (C.O C.n).center
  rw [show dist C.v (C.O C.n).center = (C.O C.n).radius from hv, hv0] at h1
  apply Complex.ext
  · simp only [Disk.wPlus, Disk.axisHalfChord]
    have : Real.sqrt ((C.O C.n).radius ^ 2 - (C.O C.n).center.im ^ 2) =
        C.v.re - (C.O C.n).center.re := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by linarith)]; nlinarith
    rw [this]; ring
  · simp [Disk.wPlus, hv0]

/-- On the upper arc of `Oᵢ`, `aᵢ₋₁` does not come after `aᵢ` (also for `i = 1, n`). -/
theorem upper_order (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ C.n) : (C.O i).upperAngle (C.A i) ≤ (C.O i).upperAngle (C.A (i - 1)) := by
  have hC' := hC
  obtain ⟨-, -, hu0, hv0, hu, hv, -, -, -, -, hC4⟩ := hC'
  rcases (show i = 1 ∨ (2 ≤ i ∧ i + 1 ≤ C.n) ∨ i = C.n by omega) with rfl | ⟨hi2, hi3⟩ | rfl
  · simp only [Nat.sub_self, A_zero]
    rw [A_mid C le_rfl (by omega)]
    obtain ⟨ha1, -, -, -, hai, -⟩ := C1_facts C hC (i := 1) le_rfl (by omega)
    have hl := u_left C hC hn
    unfold Disk.upperAngle
    have := arg_le_of_im_pos (w := (C.a 1 - (C.O 1).center) * -I)
      (z := (C.u - (C.O 1).center) * -I)
      (by rw [norm_rot _ ha1 _ (by simp), norm_rot _ hu _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith
  · have := (hC4 i hi2 hi3).1
    rw [A_mid C (by omega) (by omega), A_mid C (by omega) (by omega)]
    exact this
  · rw [A_n C (by omega)]
    have hf := C1_facts C hC (i := C.n - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ C.n)] at hf
    obtain ⟨-, ha1, -, -, hai, -⟩ := hf
    rw [A_mid C (by omega) (by omega)]
    have hl := v_right C hC hn
    unfold Disk.upperAngle
    have := arg_le_of_im_neg (w := (C.a (C.n - 1) - (C.O C.n).center) * -I)
      (z := (C.v - (C.O C.n).center) * -I)
      (by rw [norm_rot _ ha1 _ (by simp), norm_rot _ hv _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith

/-- On the lower arc of `Oᵢ`, `bᵢ₋₁` does not come after `bᵢ` (also for `i = 1, n`). -/
theorem lower_order (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ C.n) : (C.O i).lowerAngle (C.B (i - 1)) ≤ (C.O i).lowerAngle (C.B i) := by
  have hC' := hC
  obtain ⟨-, -, hu0, hv0, hu, hv, -, -, -, -, hC4⟩ := hC'
  rcases (show i = 1 ∨ (2 ≤ i ∧ i + 1 ≤ C.n) ∨ i = C.n by omega) with rfl | ⟨hi2, hi3⟩ | rfl
  · simp only [Nat.sub_self, B_zero]
    rw [B_mid C le_rfl (by omega)]
    obtain ⟨-, -, hb1, -, -, hbi⟩ := C1_facts C hC (i := 1) le_rfl (by omega)
    have hl := u_left C hC hn
    unfold Disk.lowerAngle
    have := arg_le_of_im_neg (w := (C.b 1 - (C.O 1).center) * I)
      (z := (C.u - (C.O 1).center) * I)
      (by rw [norm_rot _ hb1 _ (by simp), norm_rot _ hu _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith
  · have := (hC4 i hi2 hi3).2
    rw [B_mid C (by omega) (by omega), B_mid C (by omega) (by omega)]
    exact this
  · rw [B_n C (by omega)]
    have hf := C1_facts C hC (i := C.n - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ C.n)] at hf
    obtain ⟨-, -, -, hb1, -, hbi⟩ := hf
    rw [B_mid C (by omega) (by omega)]
    have hl := v_right C hC hn
    unfold Disk.lowerAngle
    have := arg_le_of_im_pos (w := (C.b (C.n - 1) - (C.O C.n).center) * I)
      (z := (C.v - (C.O C.n).center) * I)
      (by rw [norm_rot _ hb1 _ (by simp), norm_rot _ hv _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith

theorem upperRail_ge_dist (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ C.n) :
    0 ≤ C.upperRail i ∧ dist (C.A (i - 1)) (C.A i) ≤ C.upperRail i := by
  have hr : 0 < (C.O i).radius := hC.2.1 i h1 h2
  have ho := upper_order C hC hn h1 h2
  obtain ⟨m1, m2, -, -⟩ := ends_mem C hC h1 h2
  have hc := chord_le hr.le (upper_repr _ m1) (upper_repr _ m2)
  rw [abs_of_nonneg (by linarith)] at hc
  exact ⟨mul_nonneg hr.le (by linarith), hc⟩

theorem lowerRail_ge_dist (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ C.n) :
    0 ≤ C.lowerRail i ∧ dist (C.B i) (C.B (i - 1)) ≤ C.lowerRail i := by
  have hr : 0 < (C.O i).radius := hC.2.1 i h1 h2
  have ho := lower_order C hC hn h1 h2
  obtain ⟨-, -, m1, m2⟩ := ends_mem C hC h1 h2
  have hc := chord_le hr.le (lower_repr _ m2) (lower_repr _ m1)
  rw [abs_of_nonneg (by linarith)] at hc
  exact ⟨mul_nonneg hr.le (by linarith), hc⟩

theorem upperRail_nonneg (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ C.n) : 0 ≤ C.upperRail i := (upperRail_ge_dist C hC hn h1 h2).1

theorem lowerRail_nonneg (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ C.n) : 0 ≤ C.lowerRail i := (lowerRail_ge_dist C hC hn h1 h2).1

/-- `|Gᵢ₋₁| ≤ αᵢ + βᵢ + |Gᵢ|`. -/
theorem gate_tri (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ C.n) :
    C.gateLength (i - 1) ≤ C.upperRail i + C.lowerRail i + C.gateLength i := by
  have ha := (upperRail_ge_dist C hC hn h1 h2).2
  have hb := (lowerRail_ge_dist C hC hn h1 h2).2
  unfold DiskChain.gateLength
  have t1 := dist_triangle (C.A (i - 1)) (C.A i) (C.B (i - 1))
  have t2 := dist_triangle (C.A i) (C.B i) (C.B (i - 1))
  linarith

/-! ## Combinatorial core -/

/-- The pair `(d⁺ⱼ, d⁻ⱼ)` defined by the recursion (3.5). -/
noncomputable def pm (C : DiskChain) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | j + 1 => (min ((pm C j).1 + C.upperRail (j + 1))
                ((pm C j).2 + C.lowerRail (j + 1) + C.gateLength (j + 1)),
              min ((pm C j).2 + C.lowerRail (j + 1))
                ((pm C j).1 + C.upperRail (j + 1) + C.gateLength (j + 1)))

theorem pm_zero (C : DiskChain) : pm C 0 = (0, 0) := rfl

theorem pm_succ_fst (C : DiskChain) (j : ℕ) : (pm C (j + 1)).1 =
    min ((pm C j).1 + C.upperRail (j + 1))
      ((pm C j).2 + C.lowerRail (j + 1) + C.gateLength (j + 1)) := rfl

theorem pm_succ_snd (C : DiskChain) (j : ℕ) : (pm C (j + 1)).2 =
    min ((pm C j).2 + C.lowerRail (j + 1))
      ((pm C j).1 + C.upperRail (j + 1) + C.gateLength (j + 1)) := rfl

theorem pm_diff (C : DiskChain) (j : ℕ) :
    (pm C j).1 - (pm C j).2 ≤ C.gateLength j ∧ (pm C j).2 - (pm C j).1 ≤ C.gateLength j := by
  have hg := gate_nonneg C j
  cases j with
  | zero => simp [pm_zero, hg]
  | succ j =>
    rw [pm_succ_fst, pm_succ_snd]
    constructor
    · have : min ((pm C j).1 + C.upperRail (j + 1))
          ((pm C j).2 + C.lowerRail (j + 1) + C.gateLength (j + 1)) ≤
          min ((pm C j).2 + C.lowerRail (j + 1))
            ((pm C j).1 + C.upperRail (j + 1) + C.gateLength (j + 1)) + C.gateLength (j + 1) := by
        rw [← min_add_add_right]
        exact le_min (min_le_right _ _) ((min_le_left _ _).trans (by linarith))
      linarith
    · have : min ((pm C j).2 + C.lowerRail (j + 1))
          ((pm C j).1 + C.upperRail (j + 1) + C.gateLength (j + 1)) ≤
          min ((pm C j).1 + C.upperRail (j + 1))
            ((pm C j).2 + C.lowerRail (j + 1) + C.gateLength (j + 1)) + C.gateLength (j + 1) := by
        rw [← min_add_add_right]
        exact le_min (min_le_right _ _) ((min_le_left _ _).trans (by linarith))
      linarith

theorem pm_n_eq (C : DiskChain) (h : 1 ≤ C.n) : (pm C C.n).1 = (pm C C.n).2 := by
  obtain ⟨j, hj⟩ : ∃ j, C.n = j + 1 := ⟨C.n - 1, by omega⟩
  have hg := gate_n C h
  rw [hj] at hg ⊢
  rw [pm_succ_fst, pm_succ_snd, hg, add_zero, add_zero, min_comm]

/-- The feasible potential. -/
noncomputable def pot (C : DiskChain) : LadderVertex → ℝ
  | .start => 0
  | .finish => (pm C C.n).1
  | .up i => (pm C i).1
  | .down i => (pm C i).2

theorem pot_top (C : DiskChain) {j : ℕ} : pot C (C.topV j) = (pm C j).1 := by
  unfold DiskChain.topV
  split_ifs with h0 hn
  · subst h0; rfl
  · subst hn; rfl
  · rfl

theorem pot_bot (C : DiskChain) (h : 1 ≤ C.n) {j : ℕ} : pot C (C.botV j) = (pm C j).2 := by
  unfold DiskChain.botV
  split_ifs with h0 hn
  · subst h0; rfl
  · subst hn; exact pm_n_eq C h
  · rfl

section Core

variable (C : DiskChain) (hn1 : 1 ≤ C.n)
  (hα : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.upperRail i)
  (hβ : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.lowerRail i)
  (htri : ∀ i, 1 ≤ i → i ≤ C.n →
    C.gateLength (i - 1) ≤ C.upperRail i + C.lowerRail i + C.gateLength i)
include hn1 hα hβ htri

theorem pot_edge {x y : LadderVertex} {w : ℝ} (he : C.LadderEdge x y w) :
    pot C y ≤ pot C x + w := by
  rcases he with ⟨i, h1, h2, hxy, rfl⟩ | ⟨i, h1, h2, hxy, rfl⟩ | ⟨i, h1, h2, hxy, rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hxy
    have ha := hα (j + 1) h1 h2
    have ht := htri (j + 1) h1 h2
    simp only [Nat.add_sub_cancel] at ht
    have hd := pm_diff C j
    have f1 : (pm C (j + 1)).1 ≤ (pm C j).1 + C.upperRail (j + 1) := by
      rw [pm_succ_fst]; exact min_le_left _ _
    have f2 : (pm C j).1 ≤ (pm C (j + 1)).1 + C.upperRail (j + 1) := by
      rw [pm_succ_fst, ← min_add_add_right]
      exact le_min (by linarith) (by linarith)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [pot_top, pot_top] <;> assumption
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hxy
    have ha := hβ (j + 1) h1 h2
    have ht := htri (j + 1) h1 h2
    simp only [Nat.add_sub_cancel] at ht
    have hd := pm_diff C j
    have f1 : (pm C (j + 1)).2 ≤ (pm C j).2 + C.lowerRail (j + 1) := by
      rw [pm_succ_snd]; exact min_le_left _ _
    have f2 : (pm C j).2 ≤ (pm C (j + 1)).2 + C.lowerRail (j + 1) := by
      rw [pm_succ_snd, ← min_add_add_right]
      exact le_min (by linarith) (by linarith)
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [pot_bot C hn1, pot_bot C hn1] <;> assumption
  · have hd := pm_diff C i
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show (pm C i).2 ≤ (pm C i).1 + C.gateLength i; linarith
    · show (pm C i).1 ≤ (pm C i).2 + C.gateLength i; linarith

theorem pot_walk {k : ℕ} {x y : LadderVertex} {L : ℝ} (hw : C.LadderWalk k x y L) :
    pot C y ≤ pot C x + L := by
  induction hw with
  | nil x => simp
  | cons he _ _ _ ih =>
    have := pot_edge C hn1 hα hβ htri he
    linarith

end Core

theorem walk_mono (C : DiskChain) {k k' : ℕ} (hk : k ≤ k') {x y : LadderVertex} {L : ℝ}
    (hw : C.LadderWalk k x y L) : C.LadderWalk k' x y L := by
  induction hw with
  | nil x => exact .nil x
  | cons he hx hy _ ih => exact .cons he (hx.trans hk) (hy.trans hk) ih

theorem walk_snoc (C : DiskChain) {k : ℕ} {x y z : LadderVertex} {L w : ℝ}
    (hw : C.LadderWalk k x y L) (he : C.LadderEdge y z w) (hy : C.column y ≤ k)
    (hz : C.column z ≤ k) : C.LadderWalk k x z (L + w) := by
  induction hw with
  | nil x =>
    have := DiskChain.LadderWalk.cons he hy hz (DiskChain.LadderWalk.nil z)
    simpa using this
  | cons he' hx hy' _ ih =>
    rw [add_assoc]
    exact .cons he' hx hy' (ih he hy)

theorem column_top (C : DiskChain) {j : ℕ} (h : j ≤ C.n) : C.column (C.topV j) = j := by
  unfold DiskChain.topV
  split_ifs with h0 hn
  · subst h0; rfl
  · subst hn; rfl
  · rfl

theorem column_bot (C : DiskChain) {j : ℕ} (h : j ≤ C.n) : C.column (C.botV j) = j := by
  unfold DiskChain.botV
  split_ifs with h0 hn
  · subst h0; rfl
  · subst hn; rfl
  · rfl

theorem walk_exists (C : DiskChain) (hn1 : 1 ≤ C.n) :
    ∀ j, j ≤ C.n → C.LadderWalk j .start (C.topV j) (pm C j).1 ∧
      C.LadderWalk j .start (C.botV j) (pm C j).2 := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : C.topV 0 = .start := by simp [DiskChain.topV]
    have h0' : C.botV 0 = .start := by simp [DiskChain.botV]
    rw [h0, h0', pm_zero]
    exact ⟨.nil _, .nil _⟩
  | succ j ih =>
    intro hj
    obtain ⟨Wp, Wm⟩ := ih (by omega)
    have Wp' := walk_mono C (Nat.le_succ j) Wp
    have Wm' := walk_mono C (Nat.le_succ j) Wm
    have eU : C.LadderEdge (C.topV j) (C.topV (j + 1)) (C.upperRail (j + 1)) :=
      Or.inl ⟨j + 1, by omega, hj, Or.inl ⟨by simp, rfl⟩, rfl⟩
    have eL : C.LadderEdge (C.botV j) (C.botV (j + 1)) (C.lowerRail (j + 1)) :=
      Or.inr (Or.inl ⟨j + 1, by omega, hj, Or.inl ⟨by simp, rfl⟩, rfl⟩)
    have ct0 := column_top C (j := j) (by omega)
    have ct1 := column_top C (j := j + 1) hj
    have cb0 := column_bot C (j := j) (by omega)
    have cb1 := column_bot C (j := j + 1) hj
    have WU := walk_snoc C Wp' eU (by omega) (by omega)
    have WL := walk_snoc C Wm' eL (by omega) (by omega)
    -- crossing the gate at column j+1
    have cross : ∀ (L : ℝ), C.LadderWalk (j + 1) .start (C.botV (j + 1)) L →
        C.LadderWalk (j + 1) .start (C.topV (j + 1)) (L + C.gateLength (j + 1)) := by
      intro L W
      rcases (show j + 1 = C.n ∨ j + 1 < C.n by omega) with h | h
      · have e1 : C.botV (j + 1) = C.topV (j + 1) := by
          simp [DiskChain.botV, DiskChain.topV, h]
        rw [h, gate_n C hn1, add_zero]; rw [h] at W e1; rw [← e1]; exact W
      · have e1 : C.botV (j + 1) = .down (j + 1) := by
          simp [DiskChain.botV]; omega
        have e2 : C.topV (j + 1) = .up (j + 1) := by
          simp [DiskChain.topV]; omega
        have eG : C.LadderEdge (.down (j + 1)) (.up (j + 1)) (C.gateLength (j + 1)) :=
          Or.inr (Or.inr ⟨j + 1, by omega, h, Or.inr ⟨rfl, rfl⟩, rfl⟩)
        rw [e1] at W; rw [e2]
        exact walk_snoc C W eG (by simp [DiskChain.column]) (by simp [DiskChain.column])
    have cross' : ∀ (L : ℝ), C.LadderWalk (j + 1) .start (C.topV (j + 1)) L →
        C.LadderWalk (j + 1) .start (C.botV (j + 1)) (L + C.gateLength (j + 1)) := by
      intro L W
      rcases (show j + 1 = C.n ∨ j + 1 < C.n by omega) with h | h
      · have e1 : C.botV (j + 1) = C.topV (j + 1) := by
          simp [DiskChain.botV, DiskChain.topV, h]
        rw [h, gate_n C hn1, add_zero]; rw [h] at W e1; rw [e1]; exact W
      · have e1 : C.botV (j + 1) = .down (j + 1) := by
          simp [DiskChain.botV]; omega
        have e2 : C.topV (j + 1) = .up (j + 1) := by
          simp [DiskChain.topV]; omega
        have eG : C.LadderEdge (.up (j + 1)) (.down (j + 1)) (C.gateLength (j + 1)) :=
          Or.inr (Or.inr ⟨j + 1, by omega, h, Or.inl ⟨rfl, rfl⟩, rfl⟩)
        rw [e2] at W; rw [e1]
        exact walk_snoc C W eG (by simp [DiskChain.column]) (by simp [DiskChain.column])
    rw [pm_succ_fst, pm_succ_snd]
    constructor
    · rcases min_cases ((pm C j).1 + C.upperRail (j + 1))
          ((pm C j).2 + C.lowerRail (j + 1) + C.gateLength (j + 1)) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact WU
      · rw [h]; exact cross _ WL
    · rcases min_cases ((pm C j).2 + C.lowerRail (j + 1))
          ((pm C j).1 + C.upperRail (j + 1) + C.gateLength (j + 1)) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact WL
      · rw [h]; exact cross' _ WU

section Core2

variable (C : DiskChain) (hn1 : 1 ≤ C.n)
  (hα : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.upperRail i)
  (hβ : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.lowerRail i)
  (htri : ∀ i, 1 ≤ i → i ≤ C.n →
    C.gateLength (i - 1) ≤ C.upperRail i + C.lowerRail i + C.gateLength i)
include hn1 hα hβ htri

theorem dPlus_eq {j : ℕ} (hj : j ≤ C.n) : C.dPlus j = (pm C j).1 := by
  unfold DiskChain.dPlus DiskChain.ladderDist
  apply IsLeast.csInf_eq
  refine ⟨(walk_exists C hn1 j hj).1, ?_⟩
  intro L hL
  have := pot_walk C hn1 hα hβ htri hL
  rw [pot_top] at this
  simpa [pot] using this

theorem dMinus_eq {j : ℕ} (hj : j ≤ C.n) : C.dMinus j = (pm C j).2 := by
  unfold DiskChain.dMinus DiskChain.ladderDist
  apply IsLeast.csInf_eq
  refine ⟨(walk_exists C hn1 j hj).2, ?_⟩
  intro L hL
  have := pot_walk C hn1 hα hβ htri hL
  rw [pot_bot C hn1] at this
  simpa [pot] using this

end Core2

/-! ## The identities (3.4) -/

theorem clip_identity (A B h : ℝ) (hh : 0 ≤ h) :
    min A (B + h) - min B (A + h) = clip h (A - B) := by
  unfold clip
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem sum_identity (A B h : ℝ) (hh : 0 ≤ h) :
    min A (B + h) + min B (A + h) = A + B - max (|A - B| - h) 0 := by
  rcases abs_cases (A - B) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith

theorem abs_clip_le (h t : ℝ) (hh : 0 ≤ h) : |clip h t| ≤ h := by
  unfold clip
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem tele (F : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.Ico 1 m, (F (i + 1) - F i) = F m - F 1 := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [Finset.sum_Ico_succ_top hm, ih]; ring

theorem mu_delta_zero (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    C.mu 0 = 0 ∧ C.delta 0 = 0 := by
  have hn1 : 1 ≤ C.n := by omega
  have hα : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.upperRail i :=
    fun i h1 h2 => upperRail_nonneg C hC hn h1 h2
  have hβ : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.lowerRail i :=
    fun i h1 h2 => lowerRail_nonneg C hC hn h1 h2
  have htri : ∀ i, 1 ≤ i → i ≤ C.n →
      C.gateLength (i - 1) ≤ C.upperRail i + C.lowerRail i + C.gateLength i :=
    fun i h1 h2 => gate_tri C hC hn h1 h2
  have dP := dPlus_eq C hn1 hα hβ htri (j := 0) (by omega)
  have dM := dMinus_eq C hn1 hα hβ htri (j := 0) (by omega)
  unfold DiskChain.mu DiskChain.delta
  rw [dP, dM, pm_zero]
  simp

end L36
end DelaunayStretch

open DelaunayStretch.L36 in
theorem solution (C : DiskChain) (hC : C.IsDiskChain) (hn : 2 ≤ C.n) :
    let s : ℕ → GateState := fun i => ⟨C.O (i + 1), C.a i, C.b i, C.delta i⟩
    ((∀ i, 1 ≤ i → i + 1 ≤ C.n → (s i).IsGateState) ∧
      IsInitialPair (C.O 1) (C.O 2) (C.a 1) (C.b 1) ∧
      initialState (C.O 1) (C.O 2) (C.a 1) (C.b 1) = s 1 ∧
      (∀ i, 1 ≤ i → i + 2 ≤ C.n →
        IsNextDisk (s i) (C.O (i + 2)) (C.a (i + 1)) (C.b (i + 1)) ∧
          stepState (s i) (C.O (i + 2)) (C.a (i + 1)) (C.b (i + 1)) = s (i + 1)) ∧
      (s (C.n - 1)).O.wPlus = C.v) ∧
    (initialCost (C.O 1) (C.a 1) (C.b 1) = C.mu 1 - C.mu 0 ∧
      initialProgress (C.O 1) (C.a 1) (C.b 1) = (C.c 1).re - (C.c 0).re ∧
      (∀ i, 2 ≤ i → i + 1 ≤ C.n →
        stepCost (s (i - 1)) (C.a i) (C.b i) = C.mu i - C.mu (i - 1) ∧
          stepProgress (s (i - 1)) (C.a i) (C.b i) = (C.c i).re - (C.c (i - 1)).re) ∧
      finalCost (s (C.n - 1)) = C.mu C.n - C.mu (C.n - 1) ∧
      finalProgress (s (C.n - 1)) = (C.c C.n).re - (C.c (C.n - 1)).re) ∧
    (∀ U : ℝ, C.shortestPath - U * dist C.u C.v =
      (initialCost (C.O 1) (C.a 1) (C.b 1) - U * initialProgress (C.O 1) (C.a 1) (C.b 1)) +
        (∑ i ∈ Finset.Ico 1 (C.n - 1),
          (stepCost (s i) (C.a (i + 1)) (C.b (i + 1)) -
            U * stepProgress (s i) (C.a (i + 1)) (C.b (i + 1)))) +
        (finalCost (s (C.n - 1)) - U * finalProgress (s (C.n - 1)))) := by
  intro s
  have hn1 : 1 ≤ C.n := by omega
  obtain ⟨hrec, hP, hfin⟩ := lemma_3_3_exact_update C hC hn
  obtain ⟨hmu0, hdel0⟩ := mu_delta_zero C hC hn
  have hC' := hC
  obtain ⟨-, hrad, hu0, hv0, -, -, huv, hC1, hC2, hC3, hC4⟩ := hC'
  have hu := u_eq_wMinus C hC hn
  have hv := v_eq_wPlus C hC hn
  have hsn : s (C.n - 1) = ⟨C.O C.n, C.a (C.n - 1), C.b (C.n - 1), C.delta (C.n - 1)⟩ := by
    simp only [s, Nat.sub_add_cancel hn1]
  -- costs and progresses
  have cost1 : initialCost (C.O 1) (C.a 1) (C.b 1) = C.mu 1 - C.mu 0 := by
    have h := (hrec 0 (by omega)).2
    simp only [zero_add] at h
    unfold initialCost moveCost
    rw [h, hdel0]
    unfold DiskChain.upperRail DiskChain.lowerRail DiskChain.gateLength
    rw [Nat.sub_self, A_zero, B_zero, A_mid C le_rfl (by omega), B_mid C le_rfl (by omega), ← hu]
    ring
  have prog1 : initialProgress (C.O 1) (C.a 1) (C.b 1) = (C.c 1).re - (C.c 0).re := by
    unfold initialProgress
    rw [c_zero, c_mid C le_rfl (by omega), ← hu]
  have stepc : ∀ i, 1 ≤ i → i + 2 ≤ C.n →
      stepCost (s i) (C.a (i + 1)) (C.b (i + 1)) = C.mu (i + 1) - C.mu i ∧
        stepProgress (s i) (C.a (i + 1)) (C.b (i + 1)) = (C.c (i + 1)).re - (C.c i).re := by
    intro i h1 h2
    constructor
    · have h := (hrec i (by omega)).2
      simp only [s, stepCost, moveCost]
      rw [h]
      unfold DiskChain.upperRail DiskChain.lowerRail DiskChain.gateLength
      rw [Nat.add_sub_cancel, A_mid C h1 (by omega), B_mid C h1 (by omega),
        A_mid C (by omega) (by omega), B_mid C (by omega) (by omega)]
      ring
    · simp only [s, stepProgress, GateState.crossing]
      rw [c_mid C h1 (by omega), c_mid C (by omega) (by omega)]
  have costn : finalCost (s (C.n - 1)) = C.mu C.n - C.mu (C.n - 1) := by
    rw [hsn, hfin]
    unfold finalCost DiskChain.upperRail DiskChain.lowerRail
    simp only
    rw [A_n C hn1, B_n C hn1, A_mid C (by omega) (by omega), B_mid C (by omega) (by omega), ← hv]
    ring
  have progn : finalProgress (s (C.n - 1)) = (C.c C.n).re - (C.c (C.n - 1)).re := by
    rw [hsn]
    unfold finalProgress GateState.crossing
    simp only
    rw [c_n C hn1, c_mid C (by omega) (by omega), ← hv]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨cost1, prog1, ?_, costn, progn⟩, ?_⟩
  · -- gate states
    intro i h1 h2
    obtain ⟨-, ha, -, hb, hai, hbi⟩ := C1_facts C hC h1 h2
    have hd := (hrec (i - 1) (by omega)).1
    rw [Nat.sub_add_cancel h1] at hd
    refine ⟨hrad (i + 1) (by omega) h2, ha, hb, hai, hbi, ?_⟩
    show |C.delta i| ≤ dist (C.a i) (C.b i)
    rw [hd]
    have hg : C.gateLength i = dist (C.a i) (C.b i) := by
      unfold DiskChain.gateLength
      rw [A_mid C h1 (by omega), B_mid C h1 (by omega)]
    rw [hg]
    exact abs_clip_le _ _ dist_nonneg
  · obtain ⟨hs, ha, hb⟩ := hC1 1 le_rfl (by omega)
    exact ⟨hs, ha, hb, hC2 1 le_rfl (by omega)⟩
  · have h := (hrec 0 (by omega)).1
    simp only [zero_add] at h
    simp only [s, initialState, initialDiff, moveNewDiff]
    rw [h, hdel0]
    unfold DiskChain.upperRail DiskChain.lowerRail DiskChain.gateLength
    rw [Nat.sub_self, A_zero, B_zero, A_mid C le_rfl (by omega), B_mid C le_rfl (by omega), ← hu]
  · intro i h1 h2
    constructor
    · obtain ⟨hs, ha, hb⟩ := hC1 (i + 1) (by omega) (by omega)
      have h4 := hC4 (i + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at h4
      have h3 := hC3 i (by omega)
      rw [c_mid C h1 (by omega), c_mid C (by omega) (by omega)] at h3
      exact ⟨hs, ha, hb, hC2 (i + 1) (by omega) (by omega), h3, h4.1, h4.2⟩
    · have h := (hrec i (by omega)).1
      simp only [s, stepState, stepDiff, moveNewDiff]
      rw [h]
      unfold DiskChain.upperRail DiskChain.lowerRail DiskChain.gateLength
      rw [Nat.add_sub_cancel, A_mid C h1 (by omega), B_mid C h1 (by omega),
        A_mid C (by omega) (by omega), B_mid C (by omega) (by omega)]
  · rw [hsn]; exact hv.symm
  · intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact stepc j (by omega) (by omega)
  · intro U
    have hsum : ∑ i ∈ Finset.Ico 1 (C.n - 1),
        (stepCost (s i) (C.a (i + 1)) (C.b (i + 1)) -
          U * stepProgress (s i) (C.a (i + 1)) (C.b (i + 1))) =
        ∑ i ∈ Finset.Ico 1 (C.n - 1),
          ((C.mu (i + 1) - U * (C.c (i + 1)).re) - (C.mu i - U * (C.c i).re)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      obtain ⟨e1, e2⟩ := stepc i hi.1 (by omega)
      rw [e1, e2]; ring
    rw [hsum, tele (fun i => C.mu i - U * (C.c i).re) (C.n - 1) (by omega), cost1, prog1, costn,
      progn, hP, hmu0, c_zero, c_n C hn1]
    have hd : dist C.u C.v = C.v.re - C.u.re := by
      rw [Complex.dist_of_im_eq (by rw [hu0, hv0]), Real.dist_eq, abs_of_neg (by linarith)]
      ring
    rw [hd]
    ring
