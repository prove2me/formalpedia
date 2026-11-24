-- Prove2me | solution 1 for DelaunayStretch.lemma_A_3_A_4_generated_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:16:09.449371+00:00
-- url     : https://prove2.me/submissions/58b19494-0732-4014-892f-a3a14e90d3e2

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_delaunayGraph
import Theorems.Thm_DelaunayStretch_lemma_A_1_faces
import Theorems.Thm_DelaunayStretch_lemma_A_2_segment_decomposition


open DelaunayStretch Complex

namespace DelaunayStretch
namespace A34

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

end A34
end DelaunayStretch


open DelaunayStretch Complex

set_option linter.unusedSimpArgs false

namespace DelaunayStretch
namespace A34

/-! ## Basic planar geometry in coordinates -/

theorem dist_sq' (p o : ℂ) : dist p o ^ 2 = (p.re - o.re) ^ 2 + (p.im - o.im) ^ 2 :=
  dist_sq_eq p o

theorem two_circles {o o' : ℂ} {r r' : ℝ} {p₁ p₂ p₃ : ℂ} (h12 : p₁ ≠ p₂) (h31 : p₃ ≠ p₁)
    (h32 : p₃ ≠ p₂) (h1 : dist p₁ o = r) (h2 : dist p₂ o = r) (h3 : dist p₃ o = r)
    (h1' : dist p₁ o' = r') (h2' : dist p₂ o' = r') (h3' : dist p₃ o' = r') :
    o = o' ∧ r = r' := by
  by_contra hne
  have hs : (⟨o, r⟩ : EuclideanGeometry.Sphere ℂ) ≠ ⟨o', r'⟩ := by
    intro h
    apply hne
    cases h
    exact ⟨rfl, rfl⟩
  have := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two (V := ℂ) (P := ℂ)
    Complex.finrank_real_complex hs h12 (EuclideanGeometry.mem_sphere.2 h1)
    (EuclideanGeometry.mem_sphere.2 h2) (EuclideanGeometry.mem_sphere.2 h3)
    (EuclideanGeometry.mem_sphere.2 h1') (EuclideanGeometry.mem_sphere.2 h2')
    (EuclideanGeometry.mem_sphere.2 h3')
  tauto

theorem lm_re (u v : ℂ) (t : ℝ) : (AffineMap.lineMap u v t : ℂ).re = u.re + t * (v.re - u.re) := by
  rw [AffineMap.lineMap_apply_module']
  simp; ring

theorem lm_im (u v : ℂ) (t : ℝ) : (AffineMap.lineMap u v t : ℂ).im = u.im + t * (v.im - u.im) := by
  rw [AffineMap.lineMap_apply_module']
  simp; ring

theorem mem_line_of_im {u v p : ℂ} (hu : u.im = 0) (hv : v.im = 0) (huv : u.re < v.re)
    (hp : p.im = 0) : p ∈ line[ℝ, u, v] := by
  have h : p = AffineMap.lineMap u v ((p.re - u.re) / (v.re - u.re)) := by
    apply Complex.ext
    · have hne : v.re - u.re ≠ 0 := by linarith
      rw [lm_re, div_mul_cancel₀ _ hne]; ring
    · rw [lm_im, hu, hv, hp]; ring
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem openSeg_coords {e e' z : ℂ} (hz : z ∈ openSegment ℝ e e') :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β = 1 ∧ z.re = α * e.re + β * e'.re ∧
      z.im = α * e.im + β * e'.im := by
  obtain ⟨α, β, ha, hb, hab, rfl⟩ := hz
  exact ⟨α, β, ha, hb, hab, by simp, by simp⟩

/-- The two ends of a chord crossing the axis in its relative interior. -/
theorem gate_signs {e e' z : ℂ} (hz : z ∈ openSegment ℝ e e') (hz0 : z.im = 0)
    (hnot : ¬ (e.im = 0 ∧ e'.im = 0)) :
    (0 < e.im ∧ e'.im < 0) ∨ (e.im < 0 ∧ 0 < e'.im) := by
  obtain ⟨α, β, ha, hb, hab, -, him⟩ := openSeg_coords hz
  rw [hz0] at him
  rcases lt_trichotomy e.im 0 with h | h | h
  · right; refine ⟨h, ?_⟩; nlinarith
  · exfalso; apply hnot; refine ⟨h, ?_⟩; rw [h] at him
    have : β * e'.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · left; refine ⟨h, ?_⟩; nlinarith

/-- The axis crossing of a chord is the point of its relative interior on the axis. -/
theorem axisCrossing_eq {a b z : ℂ} (ha : 0 < a.im) (hb : b.im < 0)
    (hz : z ∈ openSegment ℝ a b) (hz0 : z.im = 0) : axisCrossing a b = z := by
  obtain ⟨α, β, h1, h2, hab, hre, him⟩ := openSeg_coords hz
  have hne : a.im - b.im ≠ 0 := by linarith
  have hβ : β = a.im / (a.im - b.im) := by
    field_simp; nlinarith
  have him' : α * a.im + β * b.im = 0 := by rw [← him, hz0]
  unfold axisCrossing
  rw [← hβ]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero]
    rw [hre]; linear_combination (-a.re) * hab
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero]
    rw [hz0]; linear_combination him' - a.im * hab

/-- A point of the open chord between two distinct points of a circle is strictly inside. -/
theorem openSeg_inside {a b c o : ℂ} {r : ℝ} (ha : dist a o = r) (hb : dist b o = r)
    (hab : a ≠ b) (hc : c ∈ openSegment ℝ a b) : dist c o < r := by
  obtain ⟨α, β, h1, h2, h12, rfl⟩ := hc
  rw [dist_eq_norm]
  have e : α • a + β • b - o = α • (a - o) + β • (b - o) := by
    calc α • a + β • b - o = α • a + β • b - (α + β) • o := by rw [h12, one_smul]
      _ = _ := by rw [add_smul, smul_sub, smul_sub]; abel
  rw [e]
  apply norm_combo_lt_of_ne (by rw [← dist_eq_norm, ha]) (by rw [← dist_eq_norm, hb])
    (by intro h; apply hab; simpa using h) h1 h2 h12

/-! ## Affine functions and convexity -/

theorem convex_aff (A B K : ℝ) : Convex ℝ {p : ℂ | A * p.re + B * p.im + K ≤ 0} := by
  have h : {p : ℂ | A * p.re + B * p.im + K ≤ 0} = {p : ℂ | A * p.re + B * p.im ≤ -K} := by
    ext p; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [h]
  apply convex_halfSpace_le
  constructor
  · intro x y; simp; ring
  · intro c x; simp; ring

/-- An affine function vanishing at two distinct points is a multiple of the side function. -/
noncomputable def side (x y p : ℂ) : ℝ :=
  (y.re - x.re) * (p.im - x.im) - (y.im - x.im) * (p.re - x.re)

theorem aff_eq_side {a b k : ℝ} {x y : ℂ} (hxy : x ≠ y)
    (hx : a * x.re + b * x.im + k = 0) (hy : a * y.re + b * y.im + k = 0) :
    ∃ l : ℝ, ∀ p : ℂ, a * p.re + b * p.im + k = l * side x y p := by
  have hd : (y.re - x.re) ^ 2 + (y.im - x.im) ^ 2 ≠ 0 := by
    intro h
    apply hxy
    apply Complex.ext <;> nlinarith [sq_nonneg (y.re - x.re), sq_nonneg (y.im - x.im)]
  refine ⟨-(a * (y.im - x.im) - b * (y.re - x.re)) /
    ((y.re - x.re) ^ 2 + (y.im - x.im) ^ 2), fun p => ?_⟩
  unfold side
  field_simp
  linear_combination ((y.re - x.re) * (p.re - x.re) + (y.im - x.im) * (p.im - x.im)) * (hy - hx) +
    ((y.re - x.re) ^ 2 + (y.im - x.im) ^ 2) * hx

/-! ## Trigonometry on a circle -/

theorem repr_coords {o p : ℂ} {r θ : ℝ} (h : p - o = (r : ℂ) * exp ((θ : ℂ) * I)) :
    p.re = o.re + r * Real.cos θ ∧ p.im = o.im + r * Real.sin θ := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  rw [Complex.sub_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im] at h1
  rw [Complex.sub_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im] at h2
  constructor <;> linarith

theorem side_circle {o x y p : ℂ} {r α β φ : ℝ}
    (hx : x.re = o.re + r * Real.cos α ∧ x.im = o.im + r * Real.sin α)
    (hy : y.re = o.re + r * Real.cos β ∧ y.im = o.im + r * Real.sin β)
    (hp : p.re = o.re + r * Real.cos φ ∧ p.im = o.im + r * Real.sin φ) :
    side x y p = 4 * r ^ 2 * Real.sin ((β - α) / 2) * Real.sin ((φ - α) / 2) *
      Real.sin ((φ - β) / 2) := by
  have e5 : Real.sin ((φ - β) / 2) = Real.sin ((φ + α) / 2) * Real.cos ((β + α) / 2) -
      Real.cos ((φ + α) / 2) * Real.sin ((β + α) / 2) := by
    rw [← Real.sin_sub]; congr 1; ring
  have h : side x y p = r ^ 2 * ((Real.cos β - Real.cos α) * (Real.sin φ - Real.sin α) -
      (Real.sin β - Real.sin α) * (Real.cos φ - Real.cos α)) := by
    unfold side; rw [hx.1, hx.2, hy.1, hy.2, hp.1, hp.2]; ring
  rw [h, e5, Real.cos_sub_cos, Real.sin_sub_sin, Real.sin_sub_sin, Real.cos_sub_cos]
  ring

theorem half_sin_pos {d : ℝ} (h0 : 0 < d) (h1 : d < 2 * Real.pi) : 0 < Real.sin (d / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem half_sin_neg {d : ℝ} (h0 : d < 0) (h1 : -(2 * Real.pi) < d) : Real.sin (d / 2) < 0 :=
  Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

theorem half_sin_nonneg {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 2 * Real.pi) : 0 ≤ Real.sin (d / 2) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

theorem half_sin_nonpos {d : ℝ} (h0 : d ≤ 0) (h1 : -(2 * Real.pi) < d) : Real.sin (d / 2) ≤ 0 :=
  Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)

/-- Sign of `sin((φ-A)/2) sin((φ-B)/2)` for `B < A` in a window of length `2π`. -/
theorem prod_in {A B φ : ℝ} (hw1 : A - B < 2 * Real.pi) (h1 : B < φ) (h2 : φ < A) :
    Real.sin ((φ - A) / 2) * Real.sin ((φ - B) / 2) < 0 :=
  mul_neg_of_neg_of_pos (half_sin_neg (by linarith) (by linarith))
    (half_sin_pos (by linarith) (by linarith))

theorem prod_out_strict {A B φ : ℝ} (hBA : B < A) (hw1 : |φ - B| < 2 * Real.pi)
    (hw2 : |φ - A| < 2 * Real.pi) (h : φ < B ∨ A < φ) :
    0 < Real.sin ((φ - A) / 2) * Real.sin ((φ - B) / 2) := by
  rw [abs_lt] at hw1 hw2
  rcases h with h | h
  · exact mul_pos_of_neg_of_neg (half_sin_neg (by linarith) (by linarith))
      (half_sin_neg (by linarith) (by linarith))
  · exact mul_pos (half_sin_pos (by linarith) (by linarith))
      (half_sin_pos (by linarith) (by linarith))

theorem prod_out {A B φ : ℝ} (hBA : B < A) (hw1 : |φ - B| < 2 * Real.pi)
    (hw2 : |φ - A| < 2 * Real.pi) (h : φ ≤ B ∨ A ≤ φ) :
    0 ≤ Real.sin ((φ - A) / 2) * Real.sin ((φ - B) / 2) := by
  rw [abs_lt] at hw1 hw2
  rcases h with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (half_sin_nonpos (by linarith) (by linarith))
      (half_sin_nonpos (by linarith) (by linarith))
  · exact mul_nonneg (half_sin_nonneg (by linarith) (by linarith))
      (half_sin_nonneg (by linarith) (by linarith))

end A34
end DelaunayStretch


open DelaunayStretch Complex

namespace DelaunayStretch
namespace A34

/-! ## Faces and their circumdisks -/

/-- `F` is a face with circumdisk of center `o` and radius `r`. -/
structure FD (S : Finset ℂ) (D : Finset (Finset ℂ)) (F : Set ℂ) (o : ℂ) (r : ℝ) : Prop where
  isFace : IsFace S D F
  pos : 0 < r
  emp : ∀ q ∈ S, r ≤ dist q o
  eq : F = convexHull ℝ ((S : Set ℂ) ∩ Metric.sphere o r)
  ext : Set.extremePoints ℝ F = (S : Set ℂ) ∩ Metric.sphere o r

theorem face_data {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
    {F : Set ℂ} (hF : IsFace S D F) : ∃ o r, FD S D F o r := by
  obtain ⟨T, hT, rfl⟩ := hF
  obtain ⟨hcard, -, -⟩ := hD.1 T hT
  obtain ⟨o, r, hTo, hS⟩ := hD.2.2.2.2 T hT
  have hA1 := ((lemma_A_1_faces S D hD).1 T hT).1
  obtain ⟨p₁, p₂, p₃, h12, h13, h23, hTe⟩ := Finset.card_eq_three.1 hcard
  have m1 : dist p₁ o = r := hTo _ (by rw [hTe]; simp)
  have m2 : dist p₂ o = r := hTo _ (by rw [hTe]; simp)
  have m3 : dist p₃ o = r := hTo _ (by rw [hTe]; simp)
  have hcirc : circumcircle T = Metric.sphere o r := by
    ext p
    constructor
    · rintro ⟨o', r', h', hp⟩
      obtain ⟨rfl, rfl⟩ := two_circles h12 h13.symm h23.symm
        (h' _ (by rw [hTe]; simp)) (h' _ (by rw [hTe]; simp)) (h' _ (by rw [hTe]; simp))
        m1 m2 m3
      exact hp
    · intro hp
      exact ⟨o, r, hTo, hp⟩
  have hpos : 0 < r := by
    rcases (dist_nonneg (x := p₁) (y := o)).lt_or_eq with h | h
    · rwa [m1] at h
    · exfalso; apply h12
      rw [m1] at h
      have e1 : p₁ = o := dist_eq_zero.1 (by rw [m1, h])
      have e2 : p₂ = o := dist_eq_zero.1 (by rw [m2, h])
      rw [e1, e2]
  refine ⟨o, r, ⟨⟨T, hT, rfl⟩, hpos, hS, by rw [face, hcirc], by rw [hA1, hcirc]⟩⟩

theorem FD.mem_of_vertex {S : Finset ℂ} {D : Finset (Finset ℂ)} {F : Set ℂ} {o : ℂ} {r : ℝ}
    (h : FD S D F o r) {p : ℂ} (hp : p ∈ Set.extremePoints ℝ F) : p ∈ S ∧ dist p o = r := by
  rw [h.ext] at hp; exact hp

theorem FD.vertex_mem {S : Finset ℂ} {D : Finset (Finset ℂ)} {F : Set ℂ} {o : ℂ} {r : ℝ}
    (h : FD S D F o r) {p : ℂ} (hp : p ∈ S) (hp' : dist p o = r) : p ∈ F := by
  rw [h.eq]; exact subset_convexHull ℝ _ ⟨hp, hp'⟩

/-! ## Powers of points -/

/-- `pow_O(p) − pow_O'(p)`, an affine function of `p`. -/
noncomputable def psi (o : ℂ) (r : ℝ) (o' : ℂ) (r' : ℝ) (p : ℂ) : ℝ :=
  2 * (o'.re - o.re) * p.re + 2 * (o'.im - o.im) * p.im +
    (o.re ^ 2 + o.im ^ 2 - r ^ 2 - o'.re ^ 2 - o'.im ^ 2 + r' ^ 2)

theorem psi_eq (o : ℂ) (r : ℝ) (o' : ℂ) (r' : ℝ) (p : ℂ) :
    psi o r o' r' p = (dist p o ^ 2 - r ^ 2) - (dist p o' ^ 2 - r' ^ 2) := by
  unfold psi; rw [dist_sq', dist_sq']; ring

theorem psi_swap (o : ℂ) (r : ℝ) (o' : ℂ) (r' : ℝ) (p : ℂ) :
    psi o' r' o r p = - psi o r o' r' p := by
  unfold psi; ring

theorem psi_le_of_mem {S : Finset ℂ} {D : Finset (Finset ℂ)} {F F' : Set ℂ} {o o' : ℂ}
    {r r' : ℝ} (h : FD S D F o r) (h' : FD S D F' o' r') {p : ℂ} (hp : p ∈ F) :
    psi o r o' r' p ≤ 0 := by
  rw [h.eq] at hp
  have hc : Convex ℝ {q : ℂ | psi o r o' r' q ≤ 0} :=
    convex_aff (2 * (o'.re - o.re)) (2 * (o'.im - o.im))
      (o.re ^ 2 + o.im ^ 2 - r ^ 2 - o'.re ^ 2 - o'.im ^ 2 + r' ^ 2)
  have hsub : (S : Set ℂ) ∩ Metric.sphere o r ⊆ {q : ℂ | psi o r o' r' q ≤ 0} := by
    rintro q ⟨hqS, hq⟩
    have hq' : dist q o = r := hq
    show psi o r o' r' q ≤ 0
    rw [psi_eq, hq']
    have := h'.emp q hqS
    have := h'.pos
    nlinarith
  exact convexHull_min hsub hc hp

/-! ## (C1) and (C2) -/

theorem C1_lemma {S : Finset ℂ} {D : Finset (Finset ℂ)} {F F' : Set ℂ} {o o' : ℂ} {r r' : ℝ}
    (h : FD S D F o r) (h' : FD S D F' o' r') (hne : F ≠ F') {e e' : ℂ} (hee : e ≠ e')
    (he : dist e o = r) (he' : dist e' o = r) (hf : dist e o' = r') (hf' : dist e' o' = r') :
    Metric.sphere o r ∩ Metric.sphere o' r' = {e, e'} := by
  ext p
  constructor
  · rintro ⟨hp, hp'⟩
    by_contra hpe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hpe
    obtain ⟨rfl, rfl⟩ := two_circles hee hpe.1 hpe.2 he he' hp hf hf' hp'
    exact hne (by rw [h.eq, h'.eq])
  · rintro (rfl | rfl)
    · exact ⟨he, hf⟩
    · exact ⟨he', hf'⟩

theorem C2_lemma {S : Finset ℂ} {D : Finset (Finset ℂ)} {F F' : Set ℂ} {o o' : ℂ} {r r' : ℝ}
    (h : FD S D F o r) (h' : FD S D F' o' r') (hne : F ≠ F') {e : ℂ} (he0 : e.im ≠ 0)
    (he : dist e o = r) (hf : dist e o' = r') {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ F) (hz₂ : z₂ ∈ F')
    (h1 : z₁.im = 0) (h2 : z₂.im = 0) (hlt : z₁.re < z₂.re) : o.re < o'.re := by
  have a := psi_le_of_mem h h' hz₁
  have b := psi_le_of_mem h' h hz₂
  have pe : psi o r o' r' e = 0 := by rw [psi_eq, he, hf]; ring
  unfold psi at a b pe
  rw [h1] at a; rw [h2] at b
  by_contra hle
  push Not at hle
  have hA : o'.re - o.re = 0 := by nlinarith
  have hre : o'.re = o.re := by linarith
  rw [hre] at a b pe
  have hK : o.re ^ 2 + o.im ^ 2 - r ^ 2 - o.re ^ 2 - o'.im ^ 2 + r' ^ 2 = 0 := by nlinarith
  have him : o'.im = o.im := by
    have : 2 * (o'.im - o.im) * e.im = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h3 | h3
    · linarith
    · exact absurd h3 he0
  rw [him] at hK
  have hr : r = r' := by
    have := h.pos; have := h'.pos
    nlinarith
  have hoo : o = o' := Complex.ext hre.symm him.symm
  exact hne (by rw [h.eq, h'.eq, hoo, hr])

/-! ## Walk lengths -/

theorem wl_nil {G : SimpleGraph ℂ} {a : ℂ} : walkLength (SimpleGraph.Walk.nil : G.Walk a a) = 0 := by
  simp [walkLength]

theorem wl_cons {G : SimpleGraph ℂ} {a b c : ℂ} (h : G.Adj a b) (w : G.Walk b c) :
    walkLength (SimpleGraph.Walk.cons h w) = dist a b + walkLength w := by
  simp [walkLength, SimpleGraph.Walk.darts_cons]

theorem wl_append {G : SimpleGraph ℂ} {a b c : ℂ} (w₁ : G.Walk a b) (w₂ : G.Walk b c) :
    walkLength (w₁.append w₂) = walkLength w₁ + walkLength w₂ := by
  unfold walkLength
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]

theorem wl_reverse {G : SimpleGraph ℂ} {a b : ℂ} (w : G.Walk a b) :
    walkLength w.reverse = walkLength w := by
  unfold walkLength
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro d _
  simp [dist_comm]

theorem wl_edge {G : SimpleGraph ℂ} {a b : ℂ} (h : G.Adj a b) :
    walkLength h.toWalk = dist a b := by
  simp [walkLength, SimpleGraph.Adj.toWalk]

theorem dist_le_wl {G : SimpleGraph ℂ} {a b : ℂ} (w : G.Walk a b) : dist a b ≤ walkLength w := by
  induction w with
  | nil => simp [wl_nil]
  | cons h p ih =>
    rw [wl_cons]
    exact (dist_triangle _ _ _).trans (by linarith)

theorem adj_of_edge {D : Finset (Finset ℂ)} {x y : ℂ} (h : IsEdgeOf D x y) :
    (delaunayGraph D).Adj x y := by
  obtain ⟨hne, T, hT, hx, hy⟩ := h
  simp only [delaunayGraph, SimpleGraph.fromRel_adj]
  exact ⟨hne, Or.inl ⟨T, hT, hx, hy⟩⟩

/-! ## Rails replaced by paths of `D` (Lemma A.4) -/

section Rail

variable {S : Finset ℂ} {D : Finset (Finset ℂ)} (hD : IsDelaunayTriangulation S D)
  {F : Set ℂ} {o : ℂ} {r : ℝ} (h : FD S D F o r) (θ : ℂ → ℝ) (L : ℝ)
  (hrep : ∀ p, dist p o = r → p - o = (r : ℂ) * exp ((θ p : ℂ) * I))
  (hwin : ∀ p, dist p o = r → L < θ p ∧ θ p ≤ L + 2 * Real.pi)
include hD h hrep hwin

omit hD h hrep hwin in
theorem side_seg' {x y p : ℂ} (hp : p ∈ segment ℝ x y) : side x y p = 0 := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hp
  unfold side
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  linear_combination ((y.re - x.re) * x.im - (y.im - x.im) * x.re) * hab

theorem rail_faceEdge {x y : ℂ} (hxS : x ∈ S) (hx : dist x o = r) (hyS : y ∈ S)
    (hy : dist y o = r) (hlt : θ y < θ x)
    (hnone : ∀ w ∈ S, dist w o = r → ¬ (θ y < θ w ∧ θ w < θ x)) : IsFaceEdge F x y := by
  have hne : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
  refine ⟨by rw [h.ext]; exact ⟨hxS, hx⟩, by rw [h.ext]; exact ⟨hyS, hy⟩, hne, ?_⟩
  intro p hp
  have hpF : p ∈ F := by
    rw [h.eq]
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ ((S : Set ℂ) ∩ Metric.sphere o r) ⟨hxS, hx⟩)
      (subset_convexHull ℝ ((S : Set ℂ) ∩ Metric.sphere o r) ⟨hyS, hy⟩) hp
  -- F lies in the closed half-plane `side x y ≤ 0`
  have hc : Convex ℝ {q : ℂ | side x y q ≤ 0} := by
    have := convex_aff (-(y.im - x.im)) (y.re - x.re) ((y.im - x.im) * x.re - (y.re - x.re) * x.im)
    convert this using 1
    ext q
    simp only [Set.mem_ofPred_eq, side]
    constructor <;> intro h <;> linarith
  have hx' := repr_coords (hrep x hx)
  have hy' := repr_coords (hrep y hy)
  obtain ⟨wx1, wx2⟩ := hwin x hx
  obtain ⟨wy1, wy2⟩ := hwin y hy
  have hsub : (S : Set ℂ) ∩ Metric.sphere o r ⊆ {q : ℂ | side x y q ≤ 0} := by
    rintro w ⟨hwS, hw⟩
    have hw' : dist w o = r := hw
    show side x y w ≤ 0
    rw [side_circle hx' hy' (repr_coords (hrep w hw'))]
    obtain ⟨ww1, ww2⟩ := hwin w hw'
    have hs : Real.sin ((θ y - θ x) / 2) < 0 := half_sin_neg (by linarith) (by linarith)
    have hP : 0 ≤ Real.sin ((θ w - θ x) / 2) * Real.sin ((θ w - θ y) / 2) := by
      apply prod_out hlt
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
      · by_contra hc'
        push Not at hc'
        exact hnone w hwS hw' hc'
    have e : 4 * r ^ 2 * Real.sin ((θ y - θ x) / 2) * Real.sin ((θ w - θ x) / 2) *
        Real.sin ((θ w - θ y) / 2) = (4 * r ^ 2) * (Real.sin ((θ y - θ x) / 2) *
        (Real.sin ((θ w - θ x) / 2) * Real.sin ((θ w - θ y) / 2))) := by ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonpos_of_nonneg hs.le hP)
  have hFsub : F ⊆ {q : ℂ | side x y q ≤ 0} := by
    rw [h.eq]; exact convexHull_min hsub hc
  refine ⟨subset_closure hpF, ?_⟩
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  set t : ℝ := ε / (2 * ‖y - x‖) with ht
  have htpos : 0 < t := by positivity
  set q : ℂ := p + (t : ℂ) * (I * (y - x)) with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_I, one_mul, Real.norm_of_nonneg htpos.le, ht]
    field_simp
    linarith
  have hq' := hFsub (hball hqball)
  have hside : side x y q = side x y p + t * ((y.re - x.re) ^ 2 + (y.im - x.im) ^ 2) := by
    rw [hq]; unfold side
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
    ring
  have hsq : 0 < (y.re - x.re) ^ 2 + (y.im - x.im) ^ 2 := by
    by_contra hc'
    apply hne
    apply Complex.ext <;> nlinarith [sq_nonneg (y.re - x.re), sq_nonneg (y.im - x.im)]
  have := side_seg' hp
  simp only [Set.mem_ofPred_eq] at hq'
  rw [hside, this] at hq'
  nlinarith

theorem rail_edge {x y : ℂ} (hxS : x ∈ S) (hx : dist x o = r) (hyS : y ∈ S)
    (hy : dist y o = r) (hle : θ y ≤ θ x)
    (hnone : ∀ w ∈ S, dist w o = r → ¬ (θ y < θ w ∧ θ w < θ x)) :
    ∃ w : (delaunayGraph D).Walk x y, walkLength w ≤ r * (θ x - θ y) := by
  rcases hle.lt_or_eq with hlt | heq
  · have hfe := rail_faceEdge hD h θ L hrep hwin hxS hx hyS hy hlt hnone
    have hed := (lemma_A_1_faces S D hD).2.2.1 F h.isFace x y hfe
    refine ⟨(adj_of_edge hed).toWalk, ?_⟩
    rw [wl_edge]
    have := chord_le h.pos.le (hrep x hx) (hrep y hy)
    rwa [abs_of_pos (by linarith)] at this
  · have hxy : x = y := by
      have e1 := hrep x hx
      have e2 := hrep y hy
      rw [heq] at e2
      have : x - o = y - o := by rw [e1, e2]
      exact sub_left_injective this
    subst hxy
    exact ⟨SimpleGraph.Walk.nil, by rw [wl_nil, heq, sub_self, mul_zero]⟩

theorem rail_walk_aux (N : ℕ) : ∀ x y : ℂ, x ∈ S → dist x o = r → y ∈ S → dist y o = r →
    θ y ≤ θ x →
    (S.filter (fun w => dist w o = r ∧ θ y < θ w ∧ θ w < θ x)).card ≤ N →
    ∃ w : (delaunayGraph D).Walk x y, walkLength w ≤ r * (θ x - θ y) := by
  classical
  induction N with
  | zero =>
    intro x y hxS hx hyS hy hle hcard
    apply rail_edge hD h θ L hrep hwin hxS hx hyS hy hle
    intro w hwS hw hb
    have hmem : w ∈ S.filter (fun w => dist w o = r ∧ θ y < θ w ∧ θ w < θ x) :=
      Finset.mem_filter.2 ⟨hwS, hw, hb⟩
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)] at hmem
    simp at hmem
  | succ N ih =>
    intro x y hxS hx hyS hy hle hcard
    by_cases hex : ∃ w ∈ S, dist w o = r ∧ θ y < θ w ∧ θ w < θ x
    · obtain ⟨w, hwS, hw, h1, h2⟩ := hex
      have hmem : w ∈ S.filter (fun w => dist w o = r ∧ θ y < θ w ∧ θ w < θ x) :=
        Finset.mem_filter.2 ⟨hwS, hw, h1, h2⟩
      have c1 : (S.filter (fun q => dist q o = r ∧ θ w < θ q ∧ θ q < θ x)).card ≤ N := by
        have : S.filter (fun q => dist q o = r ∧ θ w < θ q ∧ θ q < θ x) ⊂
            S.filter (fun w => dist w o = r ∧ θ y < θ w ∧ θ w < θ x) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨w, hmem, ?_⟩
            intro hc; simp at hc
          · intro q hq
            simp only [Finset.mem_filter] at hq ⊢
            exact ⟨hq.1, hq.2.1, by linarith, hq.2.2.2⟩
        have := Finset.card_lt_card this
        omega
      have c2 : (S.filter (fun q => dist q o = r ∧ θ y < θ q ∧ θ q < θ w)).card ≤ N := by
        have : S.filter (fun q => dist q o = r ∧ θ y < θ q ∧ θ q < θ w) ⊂
            S.filter (fun w => dist w o = r ∧ θ y < θ w ∧ θ w < θ x) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨w, hmem, ?_⟩
            intro hc; simp at hc
          · intro q hq
            simp only [Finset.mem_filter] at hq ⊢
            exact ⟨hq.1, hq.2.1, hq.2.2.1, by linarith⟩
        have := Finset.card_lt_card this
        omega
      obtain ⟨w₁, hw₁⟩ := ih x w hxS hx hwS hw h2.le c1
      obtain ⟨w₂, hw₂⟩ := ih w y hwS hw hyS hy h1.le c2
      refine ⟨w₁.append w₂, ?_⟩
      rw [wl_append]
      nlinarith
    · push Not at hex
      apply rail_edge hD h θ L hrep hwin hxS hx hyS hy hle
      intro w hwS hw hb
      exact absurd hb.2 (not_lt.2 (hex w hwS hw hb.1))

theorem rail_walk {x y : ℂ} (hxS : x ∈ S) (hx : dist x o = r) (hyS : y ∈ S)
    (hy : dist y o = r) (hle : θ y ≤ θ x) :
    ∃ w : (delaunayGraph D).Walk x y, walkLength w ≤ r * (θ x - θ y) := by
  classical
  exact rail_walk_aux hD h θ L hrep hwin _ x y hxS hx hyS hy hle le_rfl

end Rail

theorem upper_win (O : Disk) (p : ℂ) :
    -(Real.pi / 2) < O.upperAngle p ∧ O.upperAngle p ≤ -(Real.pi / 2) + 2 * Real.pi := by
  unfold Disk.upperAngle
  have := Complex.neg_pi_lt_arg ((p - O.center) * -I)
  have := Complex.arg_le_pi ((p - O.center) * -I)
  constructor <;> linarith

theorem lower_win (O : Disk) (p : ℂ) :
    Real.pi / 2 < O.lowerAngle p ∧ O.lowerAngle p ≤ Real.pi / 2 + 2 * Real.pi := by
  unfold Disk.lowerAngle
  have := Complex.neg_pi_lt_arg ((p - O.center) * I)
  have := Complex.arg_le_pi ((p - O.center) * I)
  constructor <;> linarith

end A34
end DelaunayStretch


open DelaunayStretch Complex

namespace DelaunayStretch
namespace A34

/-! ## Arcs and signs of `sin`: the real-variable core of (C4) -/

theorem range_core {ω ω' θ s : ℝ} (hω : -(Real.pi / 2) < ω) (hω2 : ω ≤ 3 * Real.pi / 2)
    (hω' : -(Real.pi / 2) < ω') (hω'2 : ω' ≤ 3 * Real.pi / 2)
    (hθ1 : -(Real.pi / 2) < θ) (hθ2 : θ ≤ 3 * Real.pi / 2)
    (hc : 0 < Real.cos ω) (hc' : Real.cos ω' < 0) (hs : Real.sin ω = s)
    (hs' : Real.sin ω' = s) :
    (s < Real.sin θ → ω < θ ∧ θ < ω') ∧ (Real.sin θ < s → θ < ω ∨ ω' < θ) := by
  have hωlt : ω < Real.pi / 2 := by
    by_contra h; push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    linarith
  have hω'gt : Real.pi / 2 < ω' := by
    by_contra h; push Not at h
    have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le hω'.le h
    linarith
  constructor
  · intro hsθ
    constructor
    · by_contra h; push Not at h
      have := Real.sin_le_sin_of_le_of_le_pi_div_two hθ1.le hωlt.le h
      linarith
    · by_contra h; push Not at h
      have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi - θ) (y := Real.pi - ω')
        (by linarith) (by linarith) (by linarith)
      rw [Real.sin_pi_sub, Real.sin_pi_sub] at this
      linarith
  · intro hsθ
    by_contra h; push Not at h
    obtain ⟨h1, h2⟩ := h
    rcases le_or_gt θ (Real.pi / 2) with h3 | h3
    · have := Real.sin_le_sin_of_le_of_le_pi_div_two hω.le h3 h1
      linarith
    · have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi - ω') (y := Real.pi - θ)
        (by linarith) (by linarith) (by linarith)
      rw [Real.sin_pi_sub, Real.sin_pi_sub] at this
      linarith

theorem range_core_lower {ν ν' θ s : ℝ} (hν : Real.pi / 2 < ν) (hν2 : ν ≤ 5 * Real.pi / 2)
    (hν' : Real.pi / 2 < ν') (hν'2 : ν' ≤ 5 * Real.pi / 2)
    (hθ1 : Real.pi / 2 < θ) (hθ2 : θ ≤ 5 * Real.pi / 2)
    (hc : Real.cos ν < 0) (hc' : 0 < Real.cos ν') (hs : Real.sin ν = s)
    (hs' : Real.sin ν' = s) :
    (Real.sin θ < s → ν < θ ∧ θ < ν') ∧ (s < Real.sin θ → θ < ν ∨ ν' < θ) := by
  have key := range_core (ω := ν - Real.pi) (ω' := ν' - Real.pi) (θ := θ - Real.pi) (s := -s)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by rw [Real.cos_sub_pi]; linarith) (by rw [Real.cos_sub_pi]; linarith)
    (by rw [Real.sin_sub_pi, hs]) (by rw [Real.sin_sub_pi, hs'])
  rw [Real.sin_sub_pi] at key
  constructor
  · intro h
    have := key.1 (by linarith)
    constructor <;> linarith
  · intro h
    rcases key.2 (by linarith) with h' | h'
    · left; linarith
    · right; linarith

section Signs

variable {L A B : ℝ} (hA : L < A ∧ A ≤ L + 2 * Real.pi) (hB : L < B ∧ B ≤ L + 2 * Real.pi)
include hA hB

theorem P_in {φ : ℝ} (h : (A < φ ∧ φ < B) ∨ (B < φ ∧ φ < A)) :
    Real.sin ((φ - A) / 2) * Real.sin ((φ - B) / 2) < 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [mul_comm]; exact prod_in (by linarith) h1 h2
  · exact prod_in (by linarith) h1 h2

theorem P_out {φ : ℝ} (hφ : L < φ ∧ φ ≤ L + 2 * Real.pi) (hAB : A ≠ B)
    (h : (φ < A ∧ φ < B) ∨ (A < φ ∧ B < φ)) :
    0 < Real.sin ((φ - A) / 2) * Real.sin ((φ - B) / 2) := by
  have w1 : |φ - B| < 2 * Real.pi := by rw [abs_lt]; constructor <;> linarith
  have w2 : |φ - A| < 2 * Real.pi := by rw [abs_lt]; constructor <;> linarith
  rcases lt_or_gt_of_ne hAB with hlt | hlt
  · rw [mul_comm]
    apply prod_out_strict hlt w2 w1
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · left; exact h1
    · right; exact h2
  · apply prod_out_strict hlt w1 w2
    rcases h with ⟨-, h1⟩ | ⟨h2, -⟩
    · left; exact h1
    · right; exact h2

end Signs

theorem neg_of_mul_pos_of_neg {κ P : ℝ} (h : 0 < κ * P) (hP : P < 0) : κ < 0 := by
  by_contra hk; push Not at hk
  have := mul_nonpos_of_nonneg_of_nonpos hk hP.le
  linarith

theorem pos_of_mul_pos_of_pos {κ P : ℝ} (h : 0 < κ * P) (hP : 0 < P) : 0 < κ := by
  by_contra hk; push Not at hk
  have := mul_nonpos_of_nonpos_of_nonneg hk hP.le
  linarith

theorem C4_real_upper {L κ A B τ ω ω' : ℝ} (wA : L < A ∧ A ≤ L + 2 * Real.pi)
    (wB : L < B ∧ B ≤ L + 2 * Real.pi) (wτ : L < τ ∧ τ ≤ L + 2 * Real.pi)
    (wω : L < ω ∧ ω ≤ L + 2 * Real.pi)
    (hA : ω < A ∧ A < ω') (hB : B < ω ∨ ω' < B) (hτ : ω < τ ∧ τ < ω')
    (hW : 0 < κ * (Real.sin ((ω - A) / 2) * Real.sin ((ω - B) / 2)))
    (hT : 0 ≤ κ * (Real.sin ((τ - A) / 2) * Real.sin ((τ - B) / 2))) : τ ≤ A := by
  by_contra hτA; push Not at hτA
  have hAB : A ≠ B := by rintro rfl; rcases hB with h | h <;> linarith [hA.1, hA.2]
  rcases hB with hB | hB
  · have p1 := P_in wA wB (φ := ω) (Or.inr ⟨hB, hA.1⟩)
    have p2 := P_out wA wB wτ hAB (Or.inr ⟨hτA, by linarith⟩)
    have hκ := neg_of_mul_pos_of_neg hW p1
    have := mul_neg_of_neg_of_pos hκ p2
    linarith
  · have p1 := P_out wA wB wω hAB (Or.inl ⟨hA.1, by linarith⟩)
    have p2 := P_in wA wB (φ := τ) (Or.inl ⟨hτA, by linarith⟩)
    have hκ := pos_of_mul_pos_of_pos hW p1
    have := mul_neg_of_pos_of_neg hκ p2
    linarith

theorem C4_real_lower {L κ A B τ ν ν' : ℝ} (wA : L < A ∧ A ≤ L + 2 * Real.pi)
    (wB : L < B ∧ B ≤ L + 2 * Real.pi) (wτ : L < τ ∧ τ ≤ L + 2 * Real.pi)
    (wν : L < ν' ∧ ν' ≤ L + 2 * Real.pi)
    (hA : ν < A ∧ A < ν') (hB : B < ν ∨ ν' < B) (hτ : ν < τ ∧ τ < ν')
    (hW : 0 < κ * (Real.sin ((ν' - A) / 2) * Real.sin ((ν' - B) / 2)))
    (hT : 0 ≤ κ * (Real.sin ((τ - A) / 2) * Real.sin ((τ - B) / 2))) : A ≤ τ := by
  by_contra hτA; push Not at hτA
  have hAB : A ≠ B := by rintro rfl; rcases hB with h | h <;> linarith [hA.1, hA.2]
  rcases hB with hB | hB
  · have p1 := P_out wA wB wν hAB (Or.inr ⟨hA.2, by linarith⟩)
    have p2 := P_in wA wB (φ := τ) (Or.inr ⟨by linarith, hτA⟩)
    have hκ := pos_of_mul_pos_of_pos hW p1
    have := mul_neg_of_pos_of_neg hκ p2
    linarith
  · have p1 := P_in wA wB (φ := ν') (Or.inl ⟨hA.2, hB⟩)
    have p2 := P_out wA wB wτ hAB (Or.inl ⟨hτA, by linarith⟩)
    have hκ := neg_of_mul_pos_of_neg hW p1
    have := mul_neg_of_neg_of_pos hκ p2
    linarith

/-! ## Geometry of (C4) -/

section C4

variable {S : Finset ℂ} {o o' a' b' c : ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
  (hemp' : ∀ q ∈ S, r' ≤ dist q o')
  (ha1 : dist a' o = r) (ha2 : dist a' o' = r') (hb1 : dist b' o = r) (hb2 : dist b' o' = r')
  (ha0 : 0 < a'.im) (hb0 : b'.im < 0) (hc : c ∈ openSegment ℝ a' b') (hc0 : c.im = 0)
  (hlt : o'.re < o.re)

include hr hr' ha1 ha2 hb1 hb2 ha0 hb0 hc hc0 hlt in
theorem C4_prep :
    0 < (Disk.mk o r).axisHalfChord ∧ dist (Disk.mk o r).wPlus o = r ∧
    dist (Disk.mk o r).wMinus o = r ∧
    psi o' r' o r a' = 0 ∧ psi o' r' o r b' = 0 ∧ 0 < psi o' r' o r (Disk.mk o r).wPlus := by
  have hab : a' ≠ b' := by rintro rfl; linarith
  have hin := openSeg_inside ha1 hb1 hab hc
  have hin2 : dist c o ^ 2 < r ^ 2 := by
    have := dist_nonneg (x := c) (y := o)
    nlinarith
  rw [dist_sq', hc0] at hin2
  have hpos : 0 < r ^ 2 - o.im ^ 2 := by nlinarith [sq_nonneg (c.re - o.re)]
  set h := (Disk.mk o r).axisHalfChord with hh
  have hhdef : h = Real.sqrt (r ^ 2 - o.im ^ 2) := rfl
  have hh0 : 0 < h := by rw [hhdef]; exact Real.sqrt_pos.2 hpos
  have hhsq : h ^ 2 = r ^ 2 - o.im ^ 2 := by rw [hhdef]; exact Real.sq_sqrt hpos.le
  have wPre : (Disk.mk o r).wPlus.re = o.re + h := rfl
  have wPim : (Disk.mk o r).wPlus.im = 0 := rfl
  have wMre : (Disk.mk o r).wMinus.re = o.re - h := rfl
  have wMim : (Disk.mk o r).wMinus.im = 0 := rfl
  have hpa : psi o' r' o r a' = 0 := by rw [psi_eq, ha1, ha2]; ring
  have hpb : psi o' r' o r b' = 0 := by rw [psi_eq, hb1, hb2]; ring
  refine ⟨hh0, ?_, ?_, hpa, hpb, ?_⟩
  · have : dist (Disk.mk o r).wPlus o ^ 2 = r ^ 2 := by
      rw [dist_sq', wPre, wPim]; nlinarith
    have := dist_nonneg (x := (Disk.mk o r).wPlus) (y := o)
    nlinarith
  · have : dist (Disk.mk o r).wMinus o ^ 2 = r ^ 2 := by
      rw [dist_sq', wMre, wMim]; nlinarith
    have := dist_nonneg (x := (Disk.mk o r).wMinus) (y := o)
    nlinarith
  · -- psi vanishes at c, and is increasing along the axis
    obtain ⟨α, β, h1, h2, h12, hre, him⟩ := openSeg_coords hc
    have hpc : psi o' r' o r c = 0 := by
      unfold psi at hpa hpb ⊢
      rw [hre, him]
      linear_combination α * hpa + β * hpb -
        (o'.re ^ 2 + o'.im ^ 2 - r' ^ 2 - o.re ^ 2 - o.im ^ 2 + r ^ 2) * h12
    have hcw : c.re < o.re + h := by
      rcases lt_or_ge (c.re - o.re) 0 with h3 | h3
      · linarith
      · have : (c.re - o.re) ^ 2 < h ^ 2 := by rw [hhsq]; linarith
        by_contra hge; push Not at hge
        have := pow_le_pow_left₀ hh0.le (show h ≤ c.re - o.re by linarith) 2
        linarith
    unfold psi at hpc ⊢
    rw [wPre, wPim]
    rw [hc0] at hpc
    have key : 2 * (o.re - o'.re) * (o.re + h) + 2 * (o.im - o'.im) * 0 +
        (o'.re ^ 2 + o'.im ^ 2 - r' ^ 2 - o.re ^ 2 - o.im ^ 2 + r ^ 2) =
        2 * (o.re - o'.re) * ((o.re + h) - c.re) := by linear_combination hpc
    rw [key]
    exact mul_pos (by linarith) (by linarith)

end C4

theorem C4_upper {S : Finset ℂ} {o o' a' b' c p : ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hemp' : ∀ q ∈ S, r' ≤ dist q o')
    (ha1 : dist a' o = r) (ha2 : dist a' o' = r') (hb1 : dist b' o = r) (hb2 : dist b' o' = r')
    (ha0 : 0 < a'.im) (hb0 : b'.im < 0) (hc : c ∈ openSegment ℝ a' b') (hc0 : c.im = 0)
    (hlt : o'.re < o.re) (hpS : p ∈ S) (hp : dist p o = r) (hp0 : 0 < p.im) :
    (Disk.mk o r).upperAngle p ≤ (Disk.mk o r).upperAngle a' := by
  obtain ⟨hh0, hwP, hwM, hpa, hpb, hpW⟩ :=
    C4_prep hr hr' ha1 ha2 hb1 hb2 ha0 hb0 hc hc0 hlt
  have hab : a' ≠ b' := by rintro rfl; linarith
  set θ := (Disk.mk o r).upperAngle with hθ
  have hrep : ∀ q, dist q o = r → q - o = (r : ℂ) * exp ((θ q : ℂ) * I) :=
    fun q hq => upper_repr (Disk.mk o r) hq
  obtain ⟨l, hl⟩ := aff_eq_side (a := 2 * (o.re - o'.re)) (b := 2 * (o.im - o'.im))
    (k := o'.re ^ 2 + o'.im ^ 2 - r' ^ 2 - o.re ^ 2 - o.im ^ 2 + r ^ 2) hab hpa hpb
  have hpsi : ∀ q, psi o' r' o r q = l * side a' b' q := hl
  set κ := l * (4 * r ^ 2 * Real.sin ((θ b' - θ a') / 2)) with hκ
  have hval : ∀ q, dist q o = r → psi o' r' o r q =
      κ * (Real.sin ((θ q - θ a') / 2) * Real.sin ((θ q - θ b') / 2)) := by
    intro q hq
    rw [hpsi, side_circle (repr_coords (hrep a' ha1)) (repr_coords (hrep b' hb1))
      (repr_coords (hrep q hq)), hκ]
    ring
  have hW := hval _ hwP
  rw [hW] at hpW
  have hT : 0 ≤ psi o' r' o r p := by
    rw [psi_eq, hp]; have := hemp' p hpS; nlinarith
  rw [hval p hp] at hT
  -- positions on the circle
  set ω := θ (Disk.mk o r).wPlus
  set ω' := θ (Disk.mk o r).wMinus
  have cP := repr_coords (hrep _ hwP)
  have cM := repr_coords (hrep _ hwM)
  have ca := repr_coords (hrep _ ha1)
  have cb := repr_coords (hrep _ hb1)
  have cp := repr_coords (hrep _ hp)
  have e1 : (Disk.mk o r).wPlus.re = o.re + (Disk.mk o r).axisHalfChord := rfl
  have e2 : (Disk.mk o r).wPlus.im = 0 := rfl
  have e3 : (Disk.mk o r).wMinus.re = o.re - (Disk.mk o r).axisHalfChord := rfl
  have e4 : (Disk.mk o r).wMinus.im = 0 := rfl
  have hcos : 0 < Real.cos ω := by
    have : 0 < r * Real.cos ω := by linarith [cP.1]
    exact pos_of_mul_pos_right this hr.le
  have hcos' : Real.cos ω' < 0 := by
    have : r * Real.cos ω' < 0 := by linarith [cM.1]
    by_contra h; push Not at h; nlinarith
  have hsin : Real.sin ω' = Real.sin ω := by
    have : r * Real.sin ω' = r * Real.sin ω := by linarith [cP.2, cM.2]
    exact mul_left_cancel₀ hr.ne' this
  have win := fun q => upper_win (Disk.mk o r) q
  have W : ∀ q, -(Real.pi / 2) < θ q ∧ θ q ≤ 3 * Real.pi / 2 := by
    intro q; have := win q; constructor <;> linarith [this.1, this.2]
  have rc := fun q => range_core (W _).1 (W _).2 (W _).1 (W _).2 (W q).1 (W q).2 hcos hcos'
    rfl hsin
  have sa : Real.sin ω < Real.sin (θ a') := by
    have : r * Real.sin ω < r * Real.sin (θ a') := by linarith [cP.2, ca.2]
    exact lt_of_mul_lt_mul_left this hr.le
  have sb : Real.sin (θ b') < Real.sin ω := by
    have : r * Real.sin (θ b') < r * Real.sin ω := by linarith [cP.2, cb.2]
    exact lt_of_mul_lt_mul_left this hr.le
  have sp : Real.sin ω < Real.sin (θ p) := by
    have : r * Real.sin ω < r * Real.sin (θ p) := by linarith [cP.2, cp.2]
    exact lt_of_mul_lt_mul_left this hr.le
  exact C4_real_upper (win a') (win b') (win p) (win _) ((rc a').1 sa) ((rc b').2 sb)
    ((rc p).1 sp) hpW hT

theorem C4_lower {S : Finset ℂ} {o o' a' b' c p : ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hemp' : ∀ q ∈ S, r' ≤ dist q o')
    (ha1 : dist a' o = r) (ha2 : dist a' o' = r') (hb1 : dist b' o = r) (hb2 : dist b' o' = r')
    (ha0 : 0 < a'.im) (hb0 : b'.im < 0) (hc : c ∈ openSegment ℝ a' b') (hc0 : c.im = 0)
    (hlt : o'.re < o.re) (hpS : p ∈ S) (hp : dist p o = r) (hp0 : p.im < 0) :
    (Disk.mk o r).lowerAngle b' ≤ (Disk.mk o r).lowerAngle p := by
  obtain ⟨hh0, hwP, hwM, hpa, hpb, hpW⟩ :=
    C4_prep hr hr' ha1 ha2 hb1 hb2 ha0 hb0 hc hc0 hlt
  have hab : b' ≠ a' := by rintro rfl; linarith
  set θ := (Disk.mk o r).lowerAngle with hθ
  have hrep : ∀ q, dist q o = r → q - o = (r : ℂ) * exp ((θ q : ℂ) * I) :=
    fun q hq => lower_repr (Disk.mk o r) hq
  obtain ⟨l, hl⟩ := aff_eq_side (a := 2 * (o.re - o'.re)) (b := 2 * (o.im - o'.im))
    (k := o'.re ^ 2 + o'.im ^ 2 - r' ^ 2 - o.re ^ 2 - o.im ^ 2 + r ^ 2) hab hpb hpa
  have hpsi : ∀ q, psi o' r' o r q = l * side b' a' q := hl
  set κ := l * (4 * r ^ 2 * Real.sin ((θ a' - θ b') / 2)) with hκ
  have hval : ∀ q, dist q o = r → psi o' r' o r q =
      κ * (Real.sin ((θ q - θ b') / 2) * Real.sin ((θ q - θ a') / 2)) := by
    intro q hq
    rw [hpsi, side_circle (repr_coords (hrep b' hb1)) (repr_coords (hrep a' ha1))
      (repr_coords (hrep q hq)), hκ]
    ring
  have hW := hval _ hwP
  rw [hW] at hpW
  have hT : 0 ≤ psi o' r' o r p := by
    rw [psi_eq, hp]; have := hemp' p hpS; nlinarith
  rw [hval p hp] at hT
  set ν := θ (Disk.mk o r).wMinus
  set ν' := θ (Disk.mk o r).wPlus
  have cP := repr_coords (hrep _ hwP)
  have cM := repr_coords (hrep _ hwM)
  have ca := repr_coords (hrep _ ha1)
  have cb := repr_coords (hrep _ hb1)
  have cp := repr_coords (hrep _ hp)
  have e1 : (Disk.mk o r).wPlus.re = o.re + (Disk.mk o r).axisHalfChord := rfl
  have e2 : (Disk.mk o r).wPlus.im = 0 := rfl
  have e3 : (Disk.mk o r).wMinus.re = o.re - (Disk.mk o r).axisHalfChord := rfl
  have e4 : (Disk.mk o r).wMinus.im = 0 := rfl
  have hcos' : 0 < Real.cos ν' := by
    have : 0 < r * Real.cos ν' := by linarith [cP.1]
    exact pos_of_mul_pos_right this hr.le
  have hcos : Real.cos ν < 0 := by
    have : r * Real.cos ν < 0 := by linarith [cM.1]
    by_contra h; push Not at h; nlinarith
  have hsin : Real.sin ν' = Real.sin ν := by
    have : r * Real.sin ν' = r * Real.sin ν := by linarith [cP.2, cM.2]
    exact mul_left_cancel₀ hr.ne' this
  have win := fun q => lower_win (Disk.mk o r) q
  have W : ∀ q, Real.pi / 2 < θ q ∧ θ q ≤ 5 * Real.pi / 2 := by
    intro q; have := win q; constructor <;> linarith [this.1, this.2]
  have rc := fun q => range_core_lower (W _).1 (W _).2 (W _).1 (W _).2 (W q).1 (W q).2 hcos
    hcos' rfl hsin
  have sb : Real.sin (θ b') < Real.sin ν := by
    have : r * Real.sin (θ b') < r * Real.sin ν := by linarith [cM.2, cb.2]
    exact lt_of_mul_lt_mul_left this hr.le
  have sa : Real.sin ν < Real.sin (θ a') := by
    have : r * Real.sin ν < r * Real.sin (θ a') := by linarith [cM.2, ca.2]
    exact lt_of_mul_lt_mul_left this hr.le
  have sp : Real.sin (θ p) < Real.sin ν := by
    have : r * Real.sin (θ p) < r * Real.sin ν := by linarith [cM.2, cp.2]
    exact lt_of_mul_lt_mul_left this hr.le
  exact C4_real_lower (win b') (win a') (win p) (win _) ((rc b').1 sb) ((rc a').2 sa)
    ((rc p).1 sp) hpW hT

end A34
end DelaunayStretch


open DelaunayStretch Complex

namespace DelaunayStretch
namespace A34

/-! ## From ladder walks to walks in `D` -/

/-- The point of the plane carried by a ladder vertex. -/
noncomputable def pt (C : DiskChain) : LadderVertex → ℂ
  | .start => C.u
  | .finish => C.v
  | .up i => C.a i
  | .down i => C.b i

theorem pt_top (C : DiskChain) (j : ℕ) : pt C (C.topV j) = C.A j := by
  unfold DiskChain.topV DiskChain.A
  split_ifs <;> rfl

theorem pt_bot (C : DiskChain) (j : ℕ) : pt C (C.botV j) = C.B j := by
  unfold DiskChain.botV DiskChain.B
  split_ifs <;> rfl

section Ladder

variable (C : DiskChain) (D : Finset (Finset ℂ)) (hn1 : 1 ≤ C.n)
  (hrU : ∀ i, 1 ≤ i → i ≤ C.n →
    ∃ w : (delaunayGraph D).Walk (C.A (i - 1)) (C.A i), walkLength w ≤ C.upperRail i)
  (hrL : ∀ i, 1 ≤ i → i ≤ C.n →
    ∃ w : (delaunayGraph D).Walk (C.B (i - 1)) (C.B i), walkLength w ≤ C.lowerRail i)
  (hg : ∀ i, 1 ≤ i → i + 1 ≤ C.n → (delaunayGraph D).Adj (C.a i) (C.b i))

include hrU hrL hg in
theorem edge_walk {x y : LadderVertex} {w : ℝ} (he : C.LadderEdge x y w) :
    ∃ W : (delaunayGraph D).Walk (pt C x) (pt C y), walkLength W ≤ w := by
  rcases he with ⟨i, h1, h2, hxy, rfl⟩ | ⟨i, h1, h2, hxy, rfl⟩ | ⟨i, h1, h2, hxy, rfl⟩
  · obtain ⟨W, hW⟩ := hrU i h1 h2
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [pt_top, pt_top]; exact ⟨W, hW⟩
    · rw [pt_top, pt_top]; exact ⟨W.reverse, by rw [wl_reverse]; exact hW⟩
  · obtain ⟨W, hW⟩ := hrL i h1 h2
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [pt_bot, pt_bot]; exact ⟨W, hW⟩
    · rw [pt_bot, pt_bot]; exact ⟨W.reverse, by rw [wl_reverse]; exact hW⟩
  · have hgl : C.gateLength i = dist (C.a i) (C.b i) := by
      unfold DiskChain.gateLength; rw [A_mid C h1 (by omega), B_mid C h1 (by omega)]
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show ∃ W : (delaunayGraph D).Walk (C.a i) (C.b i), walkLength W ≤ C.gateLength i
      exact ⟨(hg i h1 h2).toWalk, by rw [wl_edge, hgl]⟩
    · show ∃ W : (delaunayGraph D).Walk (C.b i) (C.a i), walkLength W ≤ C.gateLength i
      exact ⟨(hg i h1 h2).symm.toWalk, by rw [wl_edge, hgl, dist_comm]⟩

include hrU hrL hg in
theorem ladder_to_walk {k : ℕ} {x y : LadderVertex} {L : ℝ} (hw : C.LadderWalk k x y L) :
    ∃ W : (delaunayGraph D).Walk (pt C x) (pt C y), walkLength W ≤ L := by
  induction hw with
  | nil x => exact ⟨SimpleGraph.Walk.nil, by rw [wl_nil]⟩
  | cons he _ _ _ ih =>
    obtain ⟨W₁, h₁⟩ := edge_walk C D hrU hrL hg he
    obtain ⟨W₂, h₂⟩ := ih
    exact ⟨W₁.append W₂, by rw [wl_append]; linarith⟩

include hn1 hrU hrL hg in
theorem walk_le_shortestPath :
    ∃ W : (delaunayGraph D).Walk C.u C.v, walkLength W ≤ C.shortestPath := by
  have hα : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.upperRail i := by
    intro i h1 h2
    obtain ⟨W, hW⟩ := hrU i h1 h2
    exact (dist_nonneg.trans (dist_le_wl W)).trans hW
  have hβ : ∀ i, 1 ≤ i → i ≤ C.n → 0 ≤ C.lowerRail i := by
    intro i h1 h2
    obtain ⟨W, hW⟩ := hrL i h1 h2
    exact (dist_nonneg.trans (dist_le_wl W)).trans hW
  have htri : ∀ i, 1 ≤ i → i ≤ C.n →
      C.gateLength (i - 1) ≤ C.upperRail i + C.lowerRail i + C.gateLength i := by
    intro i h1 h2
    obtain ⟨W, hW⟩ := hrU i h1 h2
    obtain ⟨W', hW'⟩ := hrL i h1 h2
    have d1 := dist_le_wl W
    have d2 := dist_le_wl W'
    unfold DiskChain.gateLength
    have t1 := dist_triangle (C.A (i - 1)) (C.A i) (C.B (i - 1))
    have t2 := dist_triangle (C.A i) (C.B i) (C.B (i - 1))
    rw [dist_comm (C.B i) (C.B (i - 1))] at t2
    linarith
  have hP : C.shortestPath = (pm C C.n).1 := by
    have h1 : C.shortestPath = C.dPlus C.n := by
      unfold DiskChain.shortestPath DiskChain.dPlus
      have : C.topV C.n = .finish := by simp [DiskChain.topV]; omega
      rw [this]
    rw [h1, dPlus_eq C hn1 hα hβ htri le_rfl]
  have hw := (walk_exists C hn1 C.n le_rfl).1
  have : C.topV C.n = .finish := by simp [DiskChain.topV]; omega
  rw [this] at hw
  obtain ⟨W, hW⟩ := ladder_to_walk C D hrU hrL hg hw
  exact ⟨W, by rw [hP]; exact hW⟩

end Ladder

/-! ## The one-disk order -/

theorem one_order {o u v : ℂ} {r : ℝ} (hu : dist u o = r) (hv : dist v o = r) (hu0 : u.im = 0)
    (hv0 : v.im = 0) (huv : u.re < v.re) :
    (Disk.mk o r).upperAngle v ≤ (Disk.mk o r).upperAngle u ∧
      (Disk.mk o r).lowerAngle u ≤ (Disk.mk o r).lowerAngle v := by
  have h1 := dist_sq' u o
  have h2 := dist_sq' v o
  rw [hu, hu0] at h1; rw [hv, hv0] at h2
  have hmid : (u.re - v.re) * (u.re + v.re - 2 * o.re) = 0 := by nlinarith
  have hm : u.re + v.re - 2 * o.re = 0 := by
    rcases mul_eq_zero.1 hmid with h | h
    · exact absurd h (by linarith)
    · exact h
  have hl : u.re < o.re := by linarith
  have hr : o.re < v.re := by linarith
  have hu' : u ∈ (Disk.mk o r).boundary := hu
  have hv' : v ∈ (Disk.mk o r).boundary := hv
  constructor
  · unfold Disk.upperAngle
    have := arg_le_of_im_pos (w := (v - (Disk.mk o r).center) * -I)
      (z := (u - (Disk.mk o r).center) * -I)
      (by rw [norm_rot _ hv' _ (by simp), norm_rot _ hu' _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith
  · unfold Disk.lowerAngle
    have := arg_le_of_im_neg (w := (v - (Disk.mk o r).center) * I)
      (z := (u - (Disk.mk o r).center) * I)
      (by rw [norm_rot _ hv' _ (by simp), norm_rot _ hu' _ (by simp)])
      (by simp; linarith) (by simp; linarith)
    linarith

/-! ## Choice of the upper and lower ends of a gate -/

theorem gate_choice {e e' z : ℂ} (hz : z ∈ openSegment ℝ e e') (hz0 : z.im = 0)
    (hnot : ¬ (e.im = 0 ∧ e'.im = 0)) :
    0 < (if 0 < e.im then e else e').im ∧ (if 0 < e.im then e' else e).im < 0 ∧
      z ∈ openSegment ℝ (if 0 < e.im then e else e') (if 0 < e.im then e' else e) ∧
      (((if 0 < e.im then e else e') = e ∧ (if 0 < e.im then e' else e) = e') ∨
       ((if 0 < e.im then e else e') = e' ∧ (if 0 < e.im then e' else e) = e)) := by
  rcases gate_signs hz hz0 hnot with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [if_pos h1]
    exact ⟨h1, h2, hz, by simp⟩
  · have : ¬ 0 < e.im := by linarith
    simp only [if_neg this]
    exact ⟨h2, h1, by rw [openSegment_symm]; exact hz, by simp⟩

end A34
end DelaunayStretch


open DelaunayStretch Complex

namespace DelaunayStretch
namespace A34

theorem main (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ IsEdgeOf D u v)
    (huim : u.im = 0) (hvim : v.im = 0) (huv : u.re < v.re) :
    ∃ C : DiskChain, C.IsDiskChain ∧ C.u = u ∧ C.v = v ∧
      ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ C.shortestPath := by
  classical
  have huv' : u ≠ v := by rintro rfl; exact lt_irrefl _ huv
  obtain ⟨m, F, t, e, e', hm1, hFace, hFdist, ht0, htm, htmono, hseg, hedge, huF, hvF, -⟩ :=
    lemma_A_2_segment_decomposition S D hD u v hu hv huv' hopen hnot
  have hFD : ∀ i, ∃ (o : ℂ) (r : ℝ), (1 ≤ i → i ≤ m → FD S D (F i) o r) := by
    intro i
    by_cases h : 1 ≤ i ∧ i ≤ m
    · obtain ⟨o, r, hfd⟩ := face_data hD (hFace i h.1 h.2)
      exact ⟨o, r, fun _ _ => hfd⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose o r hfd using hFD
  obtain ⟨z, hz_def⟩ : ∃ z : ℕ → ℂ, ∀ i, z i = AffineMap.lineMap u v (t i) := ⟨_, fun i => rfl⟩
  have hzim : ∀ i, (z i).im = 0 := fun i => by rw [hz_def, lm_im, huim, hvim]; ring
  have hzre : ∀ i, (z i).re = u.re + t i * (v.re - u.re) := fun i => by rw [hz_def, lm_re]
  have htlt : ∀ k i, i < k → k ≤ m → t i < t k := by
    intro k
    induction k with
    | zero => intro i h; omega
    | succ k ih =>
      intro i hik hkm
      rcases (show i = k ∨ i < k by omega) with rfl | h
      · exact htmono i (by omega)
      · exact (ih i h (by omega)).trans (htmono k (by omega))
  have hzlt : ∀ i k, i < k → k ≤ m → (z i).re < (z k).re := by
    intro i k hik hkm
    rw [hzre, hzre]
    have := htlt k i hik hkm
    have : 0 < v.re - u.re := by linarith
    nlinarith
  obtain ⟨a, ha_def⟩ : ∃ a : ℕ → ℂ, ∀ j, a j = if 0 < (e j).im then e j else e' j :=
    ⟨_, fun j => rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℕ → ℂ, ∀ j, b j = if 0 < (e j).im then e' j else e j :=
    ⟨_, fun j => rfl⟩
  have hgate : ∀ j, 1 ≤ j → j + 1 ≤ m →
      0 < (a j).im ∧ (b j).im < 0 ∧ z j ∈ openSegment ℝ (a j) (b j) ∧
      a j ∈ S ∧ dist (a j) (o j) = r j ∧ dist (a j) (o (j + 1)) = r (j + 1) ∧
      b j ∈ S ∧ dist (b j) (o j) = r j ∧ dist (b j) (o (j + 1)) = r (j + 1) ∧
      (delaunayGraph D).Adj (a j) (b j) := by
    intro j h1 h2
    obtain ⟨hfe1, hfe2, hzo, hnl⟩ := hedge j h1 h2
    have hnot0 : ¬ ((e j).im = 0 ∧ (e' j).im = 0) := by
      rintro ⟨h3, h4⟩
      exact hnl ⟨mem_line_of_im huim hvim huv h3, mem_line_of_im huim hvim huv h4⟩
    rw [← hz_def] at hzo
    obtain ⟨ha0, hb0, hzab, hch⟩ := gate_choice hzo (hzim j) hnot0
    simp only [← ha_def j, ← hb_def j] at ha0 hb0 hzab hch
    have f1 := hfd j h1 (by omega)
    have f2 := hfd (j + 1) (by omega) h2
    obtain ⟨v1S, v1⟩ := f1.mem_of_vertex hfe1.1
    obtain ⟨v1S', v1'⟩ := f1.mem_of_vertex hfe1.2.1
    obtain ⟨-, v2⟩ := f2.mem_of_vertex hfe2.1
    obtain ⟨-, v2'⟩ := f2.mem_of_vertex hfe2.2.1
    have hadj := adj_of_edge ((lemma_A_1_faces S D hD).2.2.1 (F j) f1.isFace _ _ hfe1)
    rcases hch with ⟨hae, hbe⟩ | ⟨hae, hbe⟩
    · refine ⟨ha0, hb0, hzab, ?_⟩
      rw [hae, hbe]
      exact ⟨v1S, v1, v2, v1S', v1', v2', hadj⟩
    · refine ⟨ha0, hb0, hzab, ?_⟩
      rw [hae, hbe]
      exact ⟨v1S', v1', v2', v1S, v1, v2, hadj.symm⟩
  have hzF : ∀ j, 1 ≤ j → j ≤ m → z (j - 1) ∈ F j ∧ z j ∈ F j := by
    intro j h1 h2
    have hs := hseg j h1 h2
    have m1 : AffineMap.lineMap u v (t (j - 1)) ∈ segment ℝ u v ∩ F j := by
      rw [hs]; exact left_mem_segment ℝ _ _
    have m2 : AffineMap.lineMap u v (t j) ∈ segment ℝ u v ∩ F j := by
      rw [hs]; exact right_mem_segment ℝ _ _
    rw [hz_def, hz_def]
    exact ⟨m1.2, m2.2⟩
  have hC2 : ∀ j, 1 ≤ j → j + 1 ≤ m → (o j).re < (o (j + 1)).re := by
    intro j h1 h2
    obtain ⟨ha0, -, -, -, ha1, ha2, -⟩ := hgate j h1 h2
    exact C2_lemma (hfd j h1 (by omega)) (hfd (j + 1) (by omega) h2)
      (hFdist j (j + 1) h1 (by omega) (by omega) h2 (by omega)) (ne_of_gt ha0) ha1 ha2
      (hzF j h1 (by omega)).1 (hzF (j + 1) (by omega) h2).2 (hzim _) (hzim _)
      (hzlt _ _ (by omega) h2)
  -- the chain
  obtain ⟨C, hC⟩ : ∃ C : DiskChain, C = ⟨m, fun i => ⟨o i, r i⟩, u, v, a, b⟩ := ⟨_, rfl⟩
  have hCn : C.n = m := by rw [hC]
  have hCO : ∀ i, C.O i = ⟨o i, r i⟩ := by intro i; rw [hC]
  have hCu : C.u = u := by rw [hC]
  have hCv : C.v = v := by rw [hC]
  have hCa : C.a = a := by rw [hC]
  have hCb : C.b = b := by rw [hC]
  have hc : ∀ j, j ≤ m → C.c j = z j := by
    intro j hj
    unfold DiskChain.c
    rw [hCu, hCv, hCn, hCa, hCb]
    split_ifs with h0 hm'
    · rw [h0, hz_def, ht0, AffineMap.lineMap_apply_zero]
    · rw [hm', hz_def, htm, AffineMap.lineMap_apply_one]
    · obtain ⟨ha0, hb0, hzab, -⟩ := hgate j (by omega) (by omega)
      exact axisCrossing_eq ha0 hb0 hzab (hzim j)
  have hCdc : C.IsDiskChain := by
    unfold DiskChain.IsDiskChain
    rw [hCn, hCu, hCv]
    refine ⟨hm1, ?_, huim, hvim, ?_, ?_, huv, ?_, ?_, ?_, ?_⟩
    · intro i h1 h2; rw [hCO]; exact (hfd i h1 h2).pos
    · rw [hCO]; exact ((hfd 1 le_rfl hm1).mem_of_vertex huF).2
    · rw [hCO]; exact ((hfd m hm1 le_rfl).mem_of_vertex hvF).2
    · intro i h1 h2
      rw [hCO, hCO, hCa, hCb]
      obtain ⟨ha0, hb0, -, -, ha1, ha2, -, hb1, hb2, -⟩ := hgate i h1 h2
      have hab : a i ≠ b i := by intro h; rw [h] at ha0; linarith
      exact ⟨C1_lemma (hfd i h1 (by omega)) (hfd (i + 1) (by omega) h2)
        (hFdist i (i + 1) h1 (by omega) (by omega) h2 (by omega)) hab ha1 hb1 ha2 hb2, ha0, hb0⟩
    · intro i h1 h2
      rw [hCO, hCO]
      exact hC2 i h1 h2
    · intro i hi
      rw [hc i (by omega), hc (i + 1) hi]
      exact hzlt _ _ (by omega) hi
    · intro i h2 h3
      rw [hCO, hCa, hCb]
      have g := hgate (i - 1) (by omega) (by omega)
      have l := hC2 (i - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at g l
      obtain ⟨ha0, hb0, hzab, -, ha2, ha1, -, hb2, hb1, -⟩ := g
      obtain ⟨ha0', hb0', -, haS', ha1', -, hbS', hb1', -⟩ := hgate i (by omega) h3
      have fi := hfd i (by omega) (by omega)
      have fi' := hfd (i - 1) (by omega) (by omega)
      exact ⟨C4_upper fi.pos fi'.pos fi'.emp ha1 ha2 hb1 hb2 ha0 hb0 hzab (hzim _) l
          haS' ha1' ha0',
        C4_lower fi.pos fi'.pos fi'.emp ha1 ha2 hb1 hb2 ha0 hb0 hzab (hzim _) l
          hbS' hb1' hb0'⟩
  refine ⟨C, hCdc, hCu, hCv, ?_⟩
  -- ends of the rails are vertices of the faces
  have hAend : ∀ i, 1 ≤ i → i ≤ m → (C.A (i - 1) ∈ S ∧ dist (C.A (i - 1)) (o i) = r i) ∧
      (C.A i ∈ S ∧ dist (C.A i) (o i) = r i) := by
    intro i h1 h2
    constructor
    · rcases (show i = 1 ∨ 2 ≤ i by omega) with h | hi
      · rw [h, Nat.sub_self, A_zero, hCu]; exact (hfd 1 le_rfl hm1).mem_of_vertex huF
      · rw [A_mid C (by omega) (by rw [hCn]; omega), hCa]
        have g := hgate (i - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at g
        obtain ⟨-, -, -, haS, -, ha, -⟩ := g
        exact ⟨haS, ha⟩
    · rcases (show i = m ∨ i + 1 ≤ m by omega) with h | hi
      · have e1 : C.A m = v := by rw [← hCn]; exact (A_n C (by omega)).trans hCv
        rw [h, e1]; exact (hfd _ hm1 le_rfl).mem_of_vertex hvF
      · rw [A_mid C h1 (by rw [hCn]; omega), hCa]
        obtain ⟨-, -, -, haS, ha, -⟩ := hgate i h1 hi
        exact ⟨haS, ha⟩
  have hBend : ∀ i, 1 ≤ i → i ≤ m → (C.B (i - 1) ∈ S ∧ dist (C.B (i - 1)) (o i) = r i) ∧
      (C.B i ∈ S ∧ dist (C.B i) (o i) = r i) := by
    intro i h1 h2
    constructor
    · rcases (show i = 1 ∨ 2 ≤ i by omega) with h | hi
      · rw [h, Nat.sub_self, B_zero, hCu]; exact (hfd 1 le_rfl hm1).mem_of_vertex huF
      · rw [B_mid C (by omega) (by rw [hCn]; omega), hCb]
        have g := hgate (i - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at g
        obtain ⟨-, -, -, -, -, -, hbS, -, hb, -⟩ := g
        exact ⟨hbS, hb⟩
    · rcases (show i = m ∨ i + 1 ≤ m by omega) with h | hi
      · have e1 : C.B m = v := by rw [← hCn]; exact (B_n C (by omega)).trans hCv
        rw [h, e1]; exact (hfd _ hm1 le_rfl).mem_of_vertex hvF
      · rw [B_mid C h1 (by rw [hCn]; omega), hCb]
        obtain ⟨-, -, -, -, -, -, hbS, hb, -⟩ := hgate i h1 hi
        exact ⟨hbS, hb⟩
  -- order of the ends on the arcs
  have hord : ∀ i, 1 ≤ i → i ≤ m →
      (Disk.mk (o i) (r i)).upperAngle (C.A i) ≤ (Disk.mk (o i) (r i)).upperAngle (C.A (i - 1)) ∧
      (Disk.mk (o i) (r i)).lowerAngle (C.B (i - 1)) ≤ (Disk.mk (o i) (r i)).lowerAngle (C.B i) := by
    intro i h1 h2
    rcases (show m = 1 ∨ 2 ≤ m by omega) with hm | hm
    · have hi : i = 1 := by omega
      subst hi
      have eA0 : C.A (1 - 1) = u := by rw [Nat.sub_self, A_zero, hCu]
      have eB0 : C.B (1 - 1) = u := by rw [Nat.sub_self, B_zero, hCu]
      have eA1 : C.A 1 = v := by
        have := A_n C (by omega); rw [hCn, hm] at this; rw [this, hCv]
      have eB1 : C.B 1 = v := by
        have := B_n C (by omega); rw [hCn, hm] at this; rw [this, hCv]
      rw [eA0, eB0, eA1, eB1]
      have hu1 := ((hfd 1 le_rfl hm1).mem_of_vertex huF).2
      have hv1 := ((hfd m hm1 le_rfl).mem_of_vertex hvF).2
      rw [hm] at hv1
      exact one_order hu1 hv1 huim hvim huv
    · have h1' := upper_order C hCdc (by rw [hCn]; exact hm) h1 (by rw [hCn]; exact h2)
      have h2' := lower_order C hCdc (by rw [hCn]; exact hm) h1 (by rw [hCn]; exact h2)
      rw [hCO] at h1' h2'
      exact ⟨h1', h2'⟩
  have hrU : ∀ i, 1 ≤ i → i ≤ C.n →
      ∃ w : (delaunayGraph D).Walk (C.A (i - 1)) (C.A i), walkLength w ≤ C.upperRail i := by
    intro i h1 h2
    rw [hCn] at h2
    obtain ⟨⟨xS, hx⟩, ⟨yS, hy⟩⟩ := hAend i h1 h2
    unfold DiskChain.upperRail Disk.upperArcLength
    rw [hCO]
    exact rail_walk hD (hfd i h1 h2) (Disk.mk (o i) (r i)).upperAngle (-(Real.pi / 2))
      (fun p hp => upper_repr (Disk.mk (o i) (r i)) hp)
      (fun p _ => upper_win (Disk.mk (o i) (r i)) p) xS hx yS hy (hord i h1 h2).1
  have hrL : ∀ i, 1 ≤ i → i ≤ C.n →
      ∃ w : (delaunayGraph D).Walk (C.B (i - 1)) (C.B i), walkLength w ≤ C.lowerRail i := by
    intro i h1 h2
    rw [hCn] at h2
    obtain ⟨⟨xS, hx⟩, ⟨yS, hy⟩⟩ := hBend i h1 h2
    unfold DiskChain.lowerRail Disk.lowerArcLength
    rw [hCO]
    obtain ⟨W, hW⟩ := rail_walk hD (hfd i h1 h2) (Disk.mk (o i) (r i)).lowerAngle (Real.pi / 2)
      (fun p hp => lower_repr (Disk.mk (o i) (r i)) hp)
      (fun p _ => lower_win (Disk.mk (o i) (r i)) p) yS hy xS hx (hord i h1 h2).2
    exact ⟨W.reverse, by rw [wl_reverse]; exact hW⟩
  have hg : ∀ i, 1 ≤ i → i + 1 ≤ C.n → (delaunayGraph D).Adj (C.a i) (C.b i) := by
    intro i h1 h2
    rw [hCn] at h2
    rw [hCa, hCb]
    exact (hgate i h1 h2).2.2.2.2.2.2.2.2.2
  have := walk_le_shortestPath C D (by rw [hCn]; exact hm1) hrU hrL hg
  rw [hCu, hCv] at this
  exact this

end A34
end DelaunayStretch

theorem solution (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : DelaunayStretch.IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ DelaunayStretch.IsEdgeOf D u v)
    (huim : u.im = 0) (hvim : v.im = 0) (huv : u.re < v.re) :
    ∃ C : DelaunayStretch.DiskChain, C.IsDiskChain ∧ C.u = u ∧ C.v = v ∧
      ∃ w : (DelaunayStretch.delaunayGraph D).Walk u v,
        DelaunayStretch.walkLength w ≤ C.shortestPath :=
  DelaunayStretch.A34.main S D hD u v hu hv hopen hnot huim hvim huv
