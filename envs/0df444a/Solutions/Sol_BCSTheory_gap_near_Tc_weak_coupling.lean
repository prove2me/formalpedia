-- Prove2me | solution 1 for BCSTheory.gap_near_Tc_weak_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-11T07:21:05.231147+00:00
-- url     : https://prove2.me/submissions/39142009-54e5-4889-8d8c-7f25ba168642

import Mathlib
import Definitions.Def_BCSTheory_GapEquation

section Dev_TanhSeries

open Filter Topology Complex

namespace BCSAux

/-- Mittag-Leffler expansion of `coth`. -/
theorem hasSum_coth (y : ℝ) (hy : y ≠ 0) :
    HasSum (fun n : ℕ => 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2))
      (Real.pi * Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) - 1 / y) := by
  have him : ∀ z : ℂ, z.im ≠ 0 → z ≠ 0 := fun z hz h0 => hz (by rw [h0]; rfl)
  have hx : (y : ℂ) * I ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    apply hy
    simpa using this.symm
  have h := (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hx)).mpr
    (tendsto_logDeriv_euler_cot_sub hx)
  have h2 := h.mul_left I
  rw [← Complex.hasSum_ofReal]
  have hs : Real.sinh (Real.pi * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hy
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hf : (fun n : ℕ => (((2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) : ℝ) : ℂ)) =
      fun i => I * cotTerm ((y : ℂ) * I) i := by
    ext n
    have h1 : (y : ℂ) * I - ((n : ℂ) + 1) ≠ 0 := him _ (by simpa using hy)
    have h3 : (y : ℂ) * I + ((n : ℂ) + 1) ≠ 0 := him _ (by simpa using hy)
    have h4 : ((y : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < y ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
      exact_mod_cast this.ne'
    simp only [cotTerm]
    push_cast
    field_simp
    all_goals try ring_nf
    all_goals try rw [Complex.I_sq]
    all_goals try ring
  have hv : (((Real.pi * Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) - 1 / y) : ℝ) : ℂ) =
      I * ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * ((y : ℂ) * I)) - 1 / ((y : ℂ) * I)) := by
    have e1 : (Real.pi : ℂ) * (y * I) = ((Real.pi * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [Complex.cot_eq_cos_div_sin, e1, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    have hsc : ((Real.sinh (Real.pi * y) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    all_goals try ring_nf
    all_goals try rw [Complex.I_sq]
    all_goals try ring
  rw [hf, hv]
  exact h2

/-- `π tanh(π y) = ∑ 2y / (y² + (k+1/2)²)`. -/
theorem hasSum_tanh_aux (y : ℝ) (hy : y ≠ 0) :
    HasSum (fun k : ℕ => 2 * y / (y ^ 2 + ((k : ℝ) + 1 / 2) ^ 2))
      (Real.pi * Real.tanh (Real.pi * y)) := by
  have h2y : 2 * y ≠ 0 := mul_ne_zero two_ne_zero hy
  have hA := (hasSum_coth (2 * y) h2y).mul_left 2
  have hB := hasSum_coth y hy
  set f : ℕ → ℝ := fun m => 2 * (2 * (2 * y) / ((2 * y) ^ 2 + ((m : ℝ) + 1) ^ 2)) with hf
  have hfs : Summable f := hA.summable
  have hev : Summable (fun k : ℕ => f (2 * k)) :=
    hfs.comp_injective (fun a b h => by simpa using h)
  have hodd : (fun k : ℕ => f (2 * k + 1)) =
      (fun n : ℕ => 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
    ext k
    simp only [hf]
    push_cast
    have : (0:ℝ) < y ^ 2 + ((k:ℝ) + 1) ^ 2 := by positivity
    field_simp
    try ring
  have heq : (fun k : ℕ => f (2 * k)) =
      (fun k : ℕ => 2 * y / (y ^ 2 + ((k : ℝ) + 1 / 2) ^ 2)) := by
    ext k
    simp only [hf]
    push_cast
    have : (0:ℝ) < y ^ 2 + ((k:ℝ) + 1/2) ^ 2 := by positivity
    field_simp
    try ring
  have hsum := HasSum.even_add_odd hev.hasSum (hodd ▸ hB)
  have huniq := hsum.unique hA
  rw [← heq]
  convert hev.hasSum using 1
  -- compute the value
  have hc1 : Real.sinh (Real.pi * y) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero hy
  have hc2 : Real.sinh (Real.pi * (2 * y)) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero h2y
  have hch : Real.cosh (Real.pi * y) ≠ 0 := (Real.cosh_pos _).ne'
  have key : Real.pi * Real.tanh (Real.pi * y) =
      2 * (Real.pi * Real.cosh (Real.pi * (2 * y)) / Real.sinh (Real.pi * (2 * y)) - 1 / (2 * y))
        - (Real.pi * Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) - 1 / y) := by
    have e1 : Real.pi * (2 * y) = 2 * (Real.pi * y) := by ring
    rw [e1, Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp
    have := Real.cosh_sq_sub_sinh_sq (Real.pi * y)
    nlinarith [this]
  rw [key]
  linarith [huniq]

/-- Partial fraction expansion: for `s ≠ 0`,
`tanh s / s = ∑ 2 / (s² + ((k + 1/2) π)²)`. -/
theorem hasSum_tanh_div (s : ℝ) (hs : s ≠ 0) :
    HasSum (fun k : ℕ => 2 / (s ^ 2 + (((k : ℝ) + 1 / 2) * Real.pi) ^ 2))
      (Real.tanh s / s) := by
  have hy : s / Real.pi ≠ 0 := div_ne_zero hs Real.pi_ne_zero
  have h := (hasSum_tanh_aux (s / Real.pi) hy).mul_left (1 / (Real.pi * s))
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e : Real.pi * (s / Real.pi) = s := by field_simp
  have hf : (fun k : ℕ => 2 / (s ^ 2 + (((k : ℝ) + 1 / 2) * Real.pi) ^ 2)) =
      fun i : ℕ => 1 / (Real.pi * s) * (2 * (s / Real.pi) / ((s / Real.pi) ^ 2 +
        ((i : ℝ) + 1 / 2) ^ 2)) := by
    ext k
    have : (0:ℝ) < s ^ 2 + (((k : ℝ) + 1 / 2) * Real.pi) ^ 2 := by positivity
    have : (0:ℝ) < (s / Real.pi) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 := by positivity
    field_simp
    all_goals try ring
  have hv : Real.tanh s / s = 1 / (Real.pi * s) * (Real.pi * Real.tanh (Real.pi * (s / Real.pi))) := by
    rw [e]
    field_simp
  rw [hf, hv]
  exact h

end BCSAux
end Dev_TanhSeries

section Dev_TanhInt

open Filter Topology

namespace BCSAux

/-- The Matsubara-type frequencies `b_k = (k + 1/2) π`. -/
noncomputable def bk (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * Real.pi

lemma bk_pos (k : ℕ) : 0 < bk k := by unfold bk; positivity

lemma summable_inv_bk_sq : Summable (fun k : ℕ => 2 / bk k ^ 2) := by
  have h : Summable (fun k : ℕ => (8 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)) := by
    apply Summable.mul_left
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr this |>.congr (fun n => by push_cast; ring)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) h
  · have := bk_pos k; positivity
  · unfold bk
    have hpi := Real.pi_pos
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg ((k:ℝ)), mul_pos hpi hpi]

/-- The integral `∫₀^X tanh x / x dx`. -/
noncomputable def tanhInt (X : ℝ) : ℝ := ∫ x in (0 : ℝ)..X, Real.tanh x / x

lemma hasDerivAt_arctan_term (b : ℝ) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (fun X => 2 / b * Real.arctan (X / b)) (2 / (b ^ 2 + x ^ 2)) x := by
  have h : HasDerivAt (fun X => 2 / b * Real.arctan (X / b))
      (2 / b * (1 / (1 + (x / b) ^ 2) * (1 / b))) x :=
    ((hasDerivAt_id x).div_const b).arctan.const_mul (2 / b)
  refine h.congr_deriv ?_
  field_simp
  all_goals try ring

/-- The series `∑ 2 / (b_k² + x²)`, equal to `tanh x / x` for `x ≠ 0`. -/
noncomputable def tanhSeries (x : ℝ) : ℝ := ∑' k : ℕ, 2 / (bk k ^ 2 + x ^ 2)

lemma tanhSeries_bound (k : ℕ) (x : ℝ) : ‖2 / (bk k ^ 2 + x ^ 2)‖ ≤ 2 / bk k ^ 2 := by
  have := bk_pos k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [sq_nonneg x]

lemma hasDerivAt_arctanSeries (x : ℝ) :
    HasDerivAt (fun X => ∑' k : ℕ, 2 / bk k * Real.arctan (X / bk k)) (tanhSeries x) x := by
  apply hasDerivAt_tsum summable_inv_bk_sq
    (fun k y => hasDerivAt_arctan_term (bk k) (bk_pos k) y) tanhSeries_bound (y₀ := 0)
  simp

lemma tanhSeries_pos (x : ℝ) : 0 < tanhSeries x := by
  unfold tanhSeries
  have hs : Summable (fun k : ℕ => 2 / (bk k ^ 2 + x ^ 2)) :=
    Summable.of_norm_bounded summable_inv_bk_sq (tanhSeries_bound · x)
  apply hs.tsum_pos (fun k => by have := bk_pos k; positivity) 0
  have := bk_pos 0; positivity

theorem tanhInt_eq_tsum (X : ℝ) :
    tanhInt X = ∑' k : ℕ, 2 / bk k * Real.arctan (X / bk k) := by
  set F : ℝ → ℝ := fun X => ∑' k : ℕ, 2 / bk k * Real.arctan (X / bk k) with hF
  set f' : ℝ → ℝ := fun x => ∑' k : ℕ, 2 / (bk k ^ 2 + x ^ 2) with hf'
  have hbound : ∀ (k : ℕ) (x : ℝ), ‖2 / (bk k ^ 2 + x ^ 2)‖ ≤ 2 / bk k ^ 2 := by
    intro k x
    have := bk_pos k
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [sq_nonneg x]
  have hderiv : ∀ x, HasDerivAt F (f' x) x := by
    intro x
    apply hasDerivAt_tsum summable_inv_bk_sq
      (fun k y => hasDerivAt_arctan_term (bk k) (bk_pos k) y) hbound (y₀ := 0)
    simp
  have hcont : Continuous f' := by
    apply continuous_tsum (fun k => ?_) summable_inv_bk_sq hbound
    have := bk_pos k
    apply Continuous.div continuous_const (by fun_prop)
    intro x; positivity
  have hF0 : F 0 = 0 := by simp [hF]
  have h1 : ∫ x in (0:ℝ)..X, f' x = F X - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable _ _)
  rw [hF0, sub_zero] at h1
  change tanhInt X = F X
  rw [← h1]
  unfold tanhInt
  apply intervalIntegral.integral_congr_ae
  have : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (0:ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [this] with x hx _
  rw [(hasSum_tanh_div x hx).tsum_eq.symm]
  simp only [hf', bk]
  apply tsum_congr
  intro k
  ring

end BCSAux

namespace BCSAux

theorem tanhInt_eq_tsum' : tanhInt = fun X => ∑' k : ℕ, 2 / bk k * Real.arctan (X / bk k) :=
  funext tanhInt_eq_tsum

theorem hasDerivAt_tanhInt (x : ℝ) : HasDerivAt tanhInt (tanhSeries x) x := by
  rw [tanhInt_eq_tsum']
  exact hasDerivAt_arctanSeries x

theorem strictMono_tanhInt : StrictMono tanhInt :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanhInt tanhSeries_pos

theorem continuous_tanhInt : Continuous tanhInt :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanhInt x).continuousAt)

theorem tanhInt_zero : tanhInt 0 = 0 := by simp [tanhInt]

end BCSAux
end Dev_TanhInt

section Dev_Riemann

open Filter Topology

namespace BCSAux

/-- `atnc t = ∫₀¹ du / (1 + t² u²)`, which equals `arctan t / t` for `t ≠ 0` and `1` at `0`. -/
noncomputable def atnc (t : ℝ) : ℝ := ∫ u in (0:ℝ)..1, 1 / (1 + t ^ 2 * u ^ 2)

lemma atnc_eq (t : ℝ) (ht : t ≠ 0) : atnc t = Real.arctan t / t := by
  unfold atnc
  have hd : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun u => Real.arctan (t * u) / t) (1 / (1 + t ^ 2 * u ^ 2)) u := by
    intro u _
    have h : HasDerivAt (fun u => Real.arctan (t * u) / t)
        (1 / (1 + (t * u) ^ 2) * (t * 1) / t) u :=
      (((hasDerivAt_id u).const_mul t).arctan).div_const t
    refine h.congr_deriv ?_
    field_simp
    all_goals try ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u _; positivity

lemma continuous_atnc : Continuous atnc := by
  unfold atnc
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.div continuous_const (by fun_prop)
  intro p; positivity

lemma atnc_nonneg (t : ℝ) : 0 ≤ atnc t := by
  unfold atnc
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u _; positivity

lemma atnc_le_one (t : ℝ) : atnc t ≤ 1 := by
  have : ∫ u in (0:ℝ)..1, (1:ℝ) = 1 := by simp
  refine le_trans ?_ this.le
  unfold atnc
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u _; positivity
  · simp
  · intro u _
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (t * u)]

lemma atnc_zero : atnc 0 = 1 := by simp [atnc]

lemma atnc_antitoneOn : AntitoneOn atnc (Set.Ici 0) := by
  intro s hs t ht hst
  unfold atnc
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u _; positivity
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u _; positivity
  · intro u _
    apply one_div_le_one_div_of_le (by positivity)
    have hs' : (0:ℝ) ≤ s := hs
    have : s ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith [sq_nonneg u]

/-- Midpoint Riemann sums of an antitone function. -/
lemma riemann_antitone (f : ℝ → ℝ) (a δ : ℝ) (hδ : 0 < δ) (m : ℕ)
    (hf : AntitoneOn f (Set.Icc a (a + m * δ))) :
    |δ * ∑ k ∈ Finset.range m, f (a + ((k : ℝ) + 1 / 2) * δ) - ∫ x in a..a + m * δ, f x|
      ≤ δ * (f a - f (a + m * δ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsub : Set.Icc a (a + m * δ) ⊆ Set.Icc a (a + ((m + 1 : ℕ) : ℝ) * δ) := by
      apply Set.Icc_subset_Icc le_rfl
      push_cast; nlinarith
    have ih' := ih (hf.mono hsub)
    set L := a + m * δ with hL
    set R := a + ((m + 1 : ℕ) : ℝ) * δ with hR
    have hLR : R = L + δ := by rw [hR, hL]; push_cast; ring
    have hpiece : Set.Icc L R ⊆ Set.Icc a R := by
      apply Set.Icc_subset_Icc _ le_rfl
      rw [hL]; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hfp : AntitoneOn f (Set.Icc L R) := hf.mono hpiece
    have hLle : L ≤ R := by rw [hLR]; linarith
    have hint : IntervalIntegrable f MeasureTheory.volume L R := by
      apply AntitoneOn.intervalIntegrable
      rwa [Set.uIcc_of_le hLle]
    have hint1 : IntervalIntegrable f MeasureTheory.volume a L := by
      apply AntitoneOn.intervalIntegrable
      rw [Set.uIcc_of_le (by rw [hL]; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])]
      exact hf.mono hsub
    have hsplit : ∫ x in a..R, f x = (∫ x in a..L, f x) + ∫ x in L..R, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hint1 hint).symm
    have hmid_mem : a + ((m : ℝ) + 1 / 2) * δ ∈ Set.Icc L R := by
      constructor <;> [rw [hL]; rw [hLR, hL]] <;> nlinarith
    have hLmem : L ∈ Set.Icc L R := ⟨le_rfl, hLle⟩
    have hRmem : R ∈ Set.Icc L R := ⟨hLle, le_rfl⟩
    have hup : ∫ x in L..R, f x ≤ δ * f L := by
      have : ∫ x in L..R, f x ≤ ∫ x in L..R, f L := by
        apply intervalIntegral.integral_mono_on hLle hint (by simp)
        intro x hx
        exact hfp hLmem hx hx.1
      simpa [hLR, mul_comm] using this
    have hlo : δ * f R ≤ ∫ x in L..R, f x := by
      have : ∫ x in L..R, f R ≤ ∫ x in L..R, f x := by
        apply intervalIntegral.integral_mono_on hLle (by simp) hint
        intro x hx
        exact hfp hx hRmem hx.2
      simpa [hLR, mul_comm] using this
    have hm1 : f (a + ((m : ℝ) + 1 / 2) * δ) ≤ f L := hfp hLmem hmid_mem hmid_mem.1
    have hm2 : f R ≤ f (a + ((m : ℝ) + 1 / 2) * δ) := hfp hmid_mem hRmem hmid_mem.2
    rw [Finset.sum_range_succ, hsplit]
    have e : δ * (∑ k ∈ Finset.range m, f (a + ((k : ℝ) + 1 / 2) * δ) +
        f (a + ((m : ℝ) + 1 / 2) * δ)) - ((∫ x in a..L, f x) + ∫ x in L..R, f x) =
        (δ * ∑ k ∈ Finset.range m, f (a + ((k : ℝ) + 1 / 2) * δ) - ∫ x in a..L, f x) +
        (δ * f (a + ((m : ℝ) + 1 / 2) * δ) - ∫ x in L..R, f x) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h2 : |δ * f (a + ((m : ℝ) + 1 / 2) * δ) - ∫ x in L..R, f x| ≤ δ * (f L - f R) := by
      rw [abs_le]; constructor <;> nlinarith
    linarith

end BCSAux
end Dev_Riemann

section Dev_Asymp

open Filter Topology

namespace BCSAux

lemma sum_inv_half (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) =
      2 * (harmonic (2 * n) : ℝ) - (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have e : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [e, harmonic_succ, harmonic_succ, harmonic_succ]
    push_cast
    field_simp
    ring

lemma tendsto_sum_inv_half :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2) - Real.log n) atTop
      (𝓝 (Real.eulerMascheroniConstant + 2 * Real.log 2)) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Tendsto (fun n : ℕ => (harmonic (2 * n) : ℝ) - Real.log ((2 * n : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    h1.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have h3 := ((h2.const_mul 2).sub h1).add_const (2 * Real.log 2)
  have e : Real.eulerMascheroniConstant + 2 * Real.log 2 =
      2 * Real.eulerMascheroniConstant - Real.eulerMascheroniConstant + 2 * Real.log 2 := by ring
  rw [e]
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [sum_inv_half]
  have : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [this, Real.log_mul (by norm_num) (by exact_mod_cast hn.ne')]
  ring

lemma riemann_atnc (n : ℕ) (hn : 0 < n) :
    |1 / (n : ℝ) * ∑ k ∈ Finset.range n, atnc (((k : ℝ) + 1 / 2) / n) -
      ∫ x in (0:ℝ)..1, atnc x| ≤ 1 / n := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have h := riemann_antitone atnc 0 (1 / n) (by positivity) n
    (atnc_antitoneOn.mono (fun x hx => hx.1))
  have e1 : (0:ℝ) + n * (1 / n) = 1 := by rw [zero_add]; field_simp
  rw [e1] at h
  have e2 : ∀ k : ℕ, (0:ℝ) + ((k : ℝ) + 1 / 2) * (1 / n) = ((k : ℝ) + 1 / 2) / n := by
    intro k; ring
  simp only [e2] at h
  refine h.trans ?_
  have := atnc_nonneg 1
  rw [atnc_zero]
  have : 1 / (n:ℝ) * (1 - atnc 1) ≤ 1 / n * 1 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

lemma tendsto_riemann_atnc :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) * ∑ k ∈ Finset.range n, atnc (((k : ℝ) + 1 / 2) / n))
      atTop (𝓝 (∫ x in (0:ℝ)..1, atnc x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact riemann_atnc n hn
  · simpa using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- The tail function `h t = arctan (1/t) / t`. -/
noncomputable def tailFn (t : ℝ) : ℝ := Real.arctan (1 / t) / t

lemma tailFn_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ tailFn t := by
  unfold tailFn
  apply div_nonneg _ ht
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · exact (Real.arctan_pos.mpr (by positivity)).le

lemma tailFn_antitoneOn : AntitoneOn tailFn (Set.Ici 1) := by
  intro s hs t ht hst
  have hs' : (1:ℝ) ≤ s := hs
  have ht' : (1:ℝ) ≤ t := ht
  unfold tailFn
  have h1 : Real.arctan (1 / t) ≤ Real.arctan (1 / s) :=
    Real.arctan_strictMono.monotone (one_div_le_one_div_of_le (by linarith) hst)
  have h2 : 0 ≤ Real.arctan (1 / t) := (Real.arctan_pos.mpr (by positivity)).le
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma tailFn_one : tailFn 1 = Real.pi / 4 := by simp [tailFn]

lemma arctan_le_self' (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]; simp
  · have h1 := atnc_le_one x
    rw [atnc_eq x h.ne', div_le_one h] at h1
    exact h1

lemma summable_arctan_terms (X : ℝ) (hX : 0 ≤ X) :
    Summable (fun k : ℕ => 2 / bk k * Real.arctan (X / bk k)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_inv_bk_sq.mul_left X)
  · have := bk_pos k
    have : 0 ≤ Real.arctan (X / bk k) := Real.arctan_nonneg.mpr (by positivity)
    positivity
  · have hb := bk_pos k
    have h1 := arctan_le_self' (X / bk k) (by positivity)
    calc 2 / bk k * Real.arctan (X / bk k) ≤ 2 / bk k * (X / bk k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = X * (2 / bk k ^ 2) := by field_simp

lemma integral_tailFn (A : ℝ) (hA : 1 ≤ A) :
    ∫ t in (1:ℝ)..A, tailFn t = ∫ x in (1 / A)..1, atnc x := by
  have hpos : ∀ x ∈ Set.uIcc (1:ℝ) A, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc (1:ℝ) A,
      HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv (hpos x hx).ne'
  have hcont : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (Set.uIcc (1:ℝ) A) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; exact pow_ne_zero _ (hpos x hx).ne'
  have h := intervalIntegral.integral_comp_mul_deriv hderiv hcont continuous_atnc
  simp only [inv_one] at h
  rw [one_div, intervalIntegral.integral_symm 1 A⁻¹, ← h, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 := hpos x hx
  simp only [Function.comp, tailFn]
  rw [atnc_eq _ (inv_ne_zero hx0.ne')]
  field_simp

lemma tail_bound (n : ℕ) (hn : 0 < n) :
    Summable (fun j : ℕ => tailFn (1 + ((j : ℝ) + 1 / 2) / n)) ∧
    |1 / (n : ℝ) * ∑' j : ℕ, tailFn (1 + ((j : ℝ) + 1 / 2) / n) -
      ∫ x in (0:ℝ)..1, atnc x| ≤ 1 / n * (Real.pi / 4) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := 1 / n with hδ
  have hδp : 0 < δ := by positivity
  set u : ℕ → ℝ := fun j => tailFn (1 + ((j : ℝ) + 1 / 2) / n) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => tailFn_nonneg _ (by positivity)
  have hJ : ∀ M : ℕ, |δ * ∑ j ∈ Finset.range M, u j -
      ∫ x in (1 / (1 + M * δ))..1, atnc x| ≤ δ * (Real.pi / 4) := by
    intro M
    have h := riemann_antitone tailFn 1 δ hδp M (tailFn_antitoneOn.mono (fun x hx => hx.1))
    rw [integral_tailFn _ (by nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)])] at h
    have e2 : ∀ k : ℕ, (1:ℝ) + ((k:ℝ) + 1 / 2) * δ = 1 + ((k:ℝ) + 1 / 2) / n := by
      intro k; rw [hδ]; ring
    simp only [e2] at h
    refine h.trans ?_
    have := tailFn_nonneg (1 + M * δ) (by positivity)
    rw [tailFn_one]
    nlinarith
  have hint_le : ∀ M : ℕ, ∫ x in (1 / (1 + M * δ))..1, atnc x ≤ 1 := by
    intro M
    have ha : 1 / (1 + M * δ) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
    have ha0 : 0 < 1 / (1 + M * δ) := by positivity
    have : ∫ x in (1 / (1 + M * δ))..1, atnc x ≤ ∫ x in (1 / (1 + M * δ))..1, (1:ℝ) :=
      intervalIntegral.integral_mono_on ha (continuous_atnc.intervalIntegrable _ _)
        (by simp) (fun x _ => atnc_le_one x)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    linarith
  have hsum : Summable u := by
    apply summable_of_sum_range_le hu0 (c := n * (1 + δ * (Real.pi / 4)))
    intro M
    have h1 := hJ M
    have h2 := hint_le M
    rw [abs_le] at h1
    have h3 : δ * ∑ j ∈ Finset.range M, u j ≤ 1 + δ * (Real.pi / 4) := by linarith [h1.2]
    have h4 : (n:ℝ) * δ = 1 := by rw [hδ]; field_simp
    calc ∑ j ∈ Finset.range M, u j = (n * δ) * ∑ j ∈ Finset.range M, u j := by rw [h4, one_mul]
      _ = n * (δ * ∑ j ∈ Finset.range M, u j) := by ring
      _ ≤ n * (1 + δ * (Real.pi / 4)) := mul_le_mul_of_nonneg_left h3 hnr.le
  refine ⟨hsum, ?_⟩
  have hS : Tendsto (fun M : ℕ => δ * ∑ j ∈ Finset.range M, u j) atTop
      (𝓝 (δ * ∑' j, u j)) := (hsum.hasSum.tendsto_sum_nat).const_mul δ
  have hc : Continuous (fun a => ∫ x in a..1, atnc x) := by
    have := intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
      (fun a b => continuous_atnc.intervalIntegrable a b) 1
    convert this.neg using 1
    ext a
    rw [intervalIntegral.integral_symm]
    rfl
  have hlim : Tendsto (fun M : ℕ => 1 / (1 + (M : ℝ) * δ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => 1 + (M : ℝ) * δ) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.atTop_mul_const hδp)
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp h1
  have hI : Tendsto (fun M : ℕ => ∫ x in (1 / (1 + (M : ℝ) * δ))..1, atnc x) atTop
      (𝓝 (∫ x in (0:ℝ)..1, atnc x)) := (hc.tendsto 0).comp hlim
  exact le_of_tendsto' ((hS.sub hI).abs) hJ

lemma tendsto_tail :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) * ∑' j : ℕ, tailFn (1 + ((j : ℝ) + 1 / 2) / n))
      atTop (𝓝 (∫ x in (0:ℝ)..1, atnc x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (tail_bound n hn).2
  · have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ).mul_const (Real.pi / 4)
    simpa using this

lemma tanhInt_nat_decomp (n : ℕ) (hn : 0 < n) :
    tanhInt (n * Real.pi) =
      ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1 / 2)
      - 2 / Real.pi * (1 / (n : ℝ) * ∑ k ∈ Finset.range n, atnc (((k : ℝ) + 1 / 2) / n))
      + 2 / Real.pi * (1 / (n : ℝ) * ∑' j : ℕ, tailFn (1 + ((j : ℝ) + 1 / 2) / n)) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hsplit := Summable.sum_add_tsum_nat_add n
    (summable_arctan_terms (n * Real.pi) (by positivity))
  rw [tanhInt_eq_tsum, ← hsplit]
  have h1 : ∀ k ∈ Finset.range n, 2 / bk k * Real.arctan (n * Real.pi / bk k) =
      1 / ((k:ℝ) + 1 / 2) - 2 / Real.pi * (1 / n * atnc (((k:ℝ) + 1 / 2) / n)) := by
    intro k _
    have hk : (0:ℝ) < (k:ℝ) + 1 / 2 := by positivity
    have e : n * Real.pi / bk k = (((k:ℝ) + 1 / 2) / n)⁻¹ := by
      unfold bk; field_simp
    rw [e, Real.arctan_inv_of_pos (by positivity), atnc_eq _ (by positivity)]
    unfold bk
    field_simp
    all_goals try ring
  have h2 : ∀ j : ℕ, 2 / bk (j + n) * Real.arctan (n * Real.pi / bk (j + n)) =
      2 / Real.pi * (1 / n * tailFn (1 + ((j:ℝ) + 1 / 2) / n)) := by
    intro j
    have hj : (0:ℝ) < (j:ℝ) + 1 / 2 := by positivity
    have e : n * Real.pi / bk (j + n) = 1 / (1 + ((j:ℝ) + 1 / 2) / n) := by
      unfold bk; push_cast; field_simp; ring
    rw [e]
    unfold tailFn bk
    push_cast
    field_simp
    all_goals try ring
  have hs1 := Finset.sum_congr (rfl : Finset.range n = Finset.range n) h1
  have hs2 : ∑' j : ℕ, 2 / bk (j + n) * Real.arctan (n * Real.pi / bk (j + n)) =
      ∑' j : ℕ, 2 / Real.pi * (1 / n * tailFn (1 + ((j:ℝ) + 1 / 2) / n)) := tsum_congr h2
  rw [hs1, hs2, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, tsum_mul_left,
    tsum_mul_left]
  all_goals ring

/-- The constant `log (4 e^γ / π)`. -/
noncomputable def tanhConst : ℝ :=
  Real.eulerMascheroniConstant + 2 * Real.log 2 - Real.log Real.pi

lemma tendsto_tanhInt_nat :
    Tendsto (fun n : ℕ => tanhInt (n * Real.pi) - Real.log (n * Real.pi)) atTop
      (𝓝 tanhConst) := by
  have h := ((tendsto_sum_inv_half.sub_const (Real.log Real.pi)).sub
    (tendsto_riemann_atnc.const_mul (2 / Real.pi))).add (tendsto_tail.const_mul (2 / Real.pi))
  have e : tanhConst = Real.eulerMascheroniConstant + 2 * Real.log 2 - Real.log Real.pi -
      2 / Real.pi * (∫ x in (0:ℝ)..1, atnc x) + 2 / Real.pi * (∫ x in (0:ℝ)..1, atnc x) := by
    unfold tanhConst; ring
  rw [e]
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [tanhInt_nat_decomp n hn, Real.log_mul (by exact_mod_cast hn.ne') Real.pi_ne_zero]
  ring

lemma tanhInt_mono {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) : tanhInt X ≤ tanhInt Y := by
  rw [tanhInt_eq_tsum, tanhInt_eq_tsum]
  apply Summable.tsum_le_tsum _ (summable_arctan_terms X hX)
    (summable_arctan_terms Y (hX.trans hXY))
  intro k
  have hb := bk_pos k
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.arctan_strictMono.monotone
  exact div_le_div_of_nonneg_right hXY hb.le

theorem tendsto_tanhInt_sub_log :
    Tendsto (fun X => tanhInt X - Real.log X) atTop (𝓝 tanhConst) := by
  have hpi := Real.pi_pos
  have hratio : Tendsto (fun n : ℕ => Real.log (((n:ℝ) + 1) * Real.pi) -
      Real.log ((n:ℝ) * Real.pi)) atTop (𝓝 0) := by
    have := (Real.tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp]
    rw [Real.log_mul (by positivity) hpi.ne', Real.log_mul hn'.ne' hpi.ne']
    ring
  have hnat := tendsto_tanhInt_nat
  have hnat1 : Tendsto (fun n : ℕ => tanhInt (((n:ℝ) + 1) * Real.pi) -
      Real.log (((n:ℝ) + 1) * Real.pi)) atTop (𝓝 tanhConst) := by
    have := hnat.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    push_cast
    ring_nf
  have hlo : Tendsto (fun n : ℕ => tanhInt ((n:ℝ) * Real.pi) -
      Real.log (((n:ℝ) + 1) * Real.pi)) atTop (𝓝 tanhConst) := by
    have := hnat.sub hratio
    rw [sub_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hhi : Tendsto (fun n : ℕ => tanhInt (((n:ℝ) + 1) * Real.pi) -
      Real.log ((n:ℝ) * Real.pi)) atTop (𝓝 tanhConst) := by
    have := hnat1.add hratio
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hfloor : Tendsto (fun X : ℝ => ⌊X / Real.pi⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hpi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlo.comp hfloor) (hhi.comp hfloor)
  · filter_upwards [eventually_ge_atTop Real.pi] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le hpi hX
    have hq : 0 ≤ X / Real.pi := by positivity
    have h1 : (⌊X / Real.pi⌋₊ : ℝ) * Real.pi ≤ X := by
      have := Nat.floor_le hq
      rwa [le_div_iff₀ hpi] at this
    have h2 : X < ((⌊X / Real.pi⌋₊ : ℝ) + 1) * Real.pi := by
      have := Nat.lt_floor_add_one (X / Real.pi)
      rwa [div_lt_iff₀ hpi] at this
    simp only [Function.comp]
    have := tanhInt_mono (by positivity) h1
    have := Real.log_le_log hX0 h2.le
    linarith
  · filter_upwards [eventually_ge_atTop Real.pi] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le hpi hX
    have hq : 0 ≤ X / Real.pi := by positivity
    have hn1 : 1 ≤ ⌊X / Real.pi⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hpi]; linarith)
    have hn1' : (1:ℝ) ≤ ⌊X / Real.pi⌋₊ := by exact_mod_cast hn1
    have h1 : (⌊X / Real.pi⌋₊ : ℝ) * Real.pi ≤ X := by
      have := Nat.floor_le hq
      rwa [le_div_iff₀ hpi] at this
    have h2 : X < ((⌊X / Real.pi⌋₊ : ℝ) + 1) * Real.pi := by
      have := Nat.lt_floor_add_one (X / Real.pi)
      rwa [div_lt_iff₀ hpi] at this
    simp only [Function.comp]
    have := tanhInt_mono hX0.le h2.le
    have := Real.log_le_log (by positivity) h1
    linarith

end BCSAux
end Dev_Asymp

section Dev_ZeroTemp

open Filter Topology

namespace BCSAux
open BCSTheory

theorem gapIntegralZeroTemp_eq_arsinh (hbarOmegaD Δ : ℝ) (hω : 0 < hbarOmegaD)
    (hΔ : 0 < Δ) :
    gapIntegralZeroTemp hbarOmegaD Δ = Real.arsinh (hbarOmegaD / Δ) := by
  unfold gapIntegralZeroTemp quasiparticleEnergy
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) hbarOmegaD,
      HasDerivAt (fun η => Real.arsinh (η / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun η => Real.arsinh (η / Δ))
        ((Real.sqrt (1 + (x / Δ) ^ 2))⁻¹ • (1 / Δ)) x :=
      ((hasDerivAt_id x).div_const Δ).arsinh
    convert h1 using 1
    have hpos : 0 < x ^ 2 + Δ ^ 2 := by positivity
    have : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
      have e : 1 + (x / Δ) ^ 2 = (x ^ 2 + Δ ^ 2) / Δ ^ 2 := by
        field_simp; ring
      rw [e, Real.sqrt_div' _ (sq_nonneg Δ), Real.sqrt_sq hΔ.le]
    rw [this, smul_eq_mul]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro x _
      positivity

theorem zeroTemperatureGap_eq (hbarOmegaD coupling : ℝ) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    (∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling))) ∧
    zeroTemperatureGap hbarOmegaD coupling = hbarOmegaD / Real.sinh (1 / coupling) := by
  have hs : 0 < Real.sinh (1 / coupling) := Real.sinh_pos_iff.mpr (by positivity)
  have key : ∀ Δ : ℝ, 0 < Δ →
      (gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling ↔
        Δ = hbarOmegaD / Real.sinh (1 / coupling)) := by
    intro Δ hΔ
    rw [gapIntegralZeroTemp_eq_arsinh _ _ hω hΔ]
    constructor
    · intro h
      have := congrArg Real.sinh h
      rw [Real.sinh_arsinh] at this
      rw [← this]
      field_simp
    · intro h
      rw [h, div_div_cancel₀ hω.ne', Real.arsinh_sinh]
  refine ⟨key, ?_⟩
  unfold zeroTemperatureGap
  have : {Δ : ℝ | 0 < Δ ∧ gapIntegralZeroTemp hbarOmegaD Δ = 1 / coupling} =
      {hbarOmegaD / Real.sinh (1 / coupling)} := by
    ext Δ
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact (key Δ h1).mp h2
    · intro h
      have hp : 0 < Δ := by rw [h]; positivity
      exact ⟨hp, (key Δ hp).mpr h⟩
  rw [this, csSup_singleton]

theorem zeroTemperatureGap_weak_coupling (hbarOmegaD : ℝ) (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        zeroTemperatureGap hbarOmegaD coupling / (2 * hbarOmegaD * Real.exp (-1 / coupling)))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim : Tendsto (fun coupling : ℝ => Real.exp (-1 / coupling)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun coupling : ℝ => -1 / coupling) (𝓝[>] 0) atBot := by
      have h := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
      convert tendsto_neg_atTop_atBot.comp h using 1
      ext x
      simp [div_eq_mul_inv]
    exact Real.tendsto_exp_atBot.comp this
  have h2 : Tendsto (fun coupling : ℝ => (1 - Real.exp (-1 / coupling) ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).sub (hlim.pow 2)).inv₀ (by norm_num)
    simpa using this
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with c (hc : 0 < c)
  rw [(zeroTemperatureGap_eq hbarOmegaD c hω hc).2, Real.sinh_eq]
  have e2 : Real.exp (1 / c) = (Real.exp (-1 / c))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have e3 : Real.exp (-(1 / c)) = Real.exp (-1 / c) := by ring_nf
  rw [e2, e3]
  have hpos := Real.exp_pos (-1 / c)
  have hlt : Real.exp (-1 / c) < 1 := Real.exp_lt_one_iff.mpr (by
      have : 0 < 1 / c := by positivity
      rw [neg_div]; linarith)
  generalize Real.exp (-1 / c) = u at hpos hlt ⊢
  have h1 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have h4 : u⁻¹ - u ≠ 0 := by
    intro h
    have := mul_inv_cancel₀ hpos.ne'
    nlinarith
  field_simp

end BCSAux
end Dev_ZeroTemp

section Dev_Tc

open Filter Topology

namespace BCSAux

open BCSTheory

lemma tanh_abs_div_abs (a η : ℝ) :
    Real.tanh (|η| / a) / |η| = Real.tanh (η / a) / η := by
  rcases le_or_gt 0 η with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, neg_div, Real.tanh_neg, neg_div_neg_eq]

lemma quasiparticleEnergy_zero (η : ℝ) : quasiparticleEnergy η 0 = |η| := by
  simp [quasiparticleEnergy, Real.sqrt_sq_eq_abs]

/-- The critical-temperature integral in terms of `tanhInt`. -/
theorem gapIntegral_zero_eq (kB hbarOmegaD T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    gapIntegral kB hbarOmegaD 0 T = tanhInt (hbarOmegaD / (2 * kB * T)) := by
  have ha : 0 < 2 * kB * T := by positivity
  unfold gapIntegral tanhInt
  simp only [quasiparticleEnergy_zero, tanh_abs_div_abs]
  have h := intervalIntegral.integral_comp_div (fun x => Real.tanh x / x) ha.ne'
    (a := 0) (b := hbarOmegaD)
  simp only [zero_div, smul_eq_mul] at h
  have e : ∀ η : ℝ, Real.tanh (η / (2 * kB * T)) / η =
      (1 / (2 * kB * T)) * (Real.tanh (η / (2 * kB * T)) / (η / (2 * kB * T))) := by
    intro η
    rcases eq_or_ne η 0 with h0 | h0
    · simp [h0]
    · field_simp
  simp only [e]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

theorem tendsto_tanhInt_atTop : Tendsto tanhInt atTop atTop := by
  have h := tendsto_tanhInt_sub_log.add_atTop Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards with X
  ring

/-- For `λ > 0` there is a unique `X > 0` with `tanhInt X = 1/λ`. -/
theorem exists_tanhInt_eq (c : ℝ) (hc : 0 < c) : ∃ X : ℝ, 0 < X ∧ tanhInt X = 1 / c := by
  obtain ⟨M, hM⟩ := (tendsto_atTop.mp tendsto_tanhInt_atTop) (1 / c + 1) |>.exists_forall_of_atTop
  have hM' := hM (max M 1) (le_max_left _ _)
  have h0 : tanhInt 0 ≤ 1 / c := by rw [tanhInt_zero]; positivity
  have h1 : 1 / c ≤ tanhInt (max M 1) := by linarith
  obtain ⟨X, hX, hXeq⟩ := intermediate_value_Icc (le_trans zero_le_one (le_max_right M 1))
    continuous_tanhInt.continuousOn ⟨h0, h1⟩
  refine ⟨X, ?_, hXeq⟩
  rcases hX.1.eq_or_lt with h | h
  · rw [← h, tanhInt_zero] at hXeq
    have : 0 < 1 / c := by positivity
    linarith
  · exact h

/-- The unique `X_c(λ) > 0` with `tanhInt X_c = 1/λ` (junk value for `λ ≤ 0`). -/
noncomputable def Xc (c : ℝ) : ℝ :=
  if h : 0 < c then Classical.choose (exists_tanhInt_eq c h) else 1

lemma Xc_spec (c : ℝ) (hc : 0 < c) : 0 < Xc c ∧ tanhInt (Xc c) = 1 / c := by
  unfold Xc
  rw [dif_pos hc]
  exact Classical.choose_spec (exists_tanhInt_eq c hc)

lemma tanhInt_eq_iff (c : ℝ) (hc : 0 < c) (X : ℝ) : tanhInt X = 1 / c ↔ X = Xc c := by
  constructor
  · intro h
    exact strictMono_tanhInt.injective (h.trans (Xc_spec c hc).2.symm)
  · intro h; rw [h]; exact (Xc_spec c hc).2

theorem gap_Tc_iff (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) (T : ℝ) :
    (0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling) ↔
      T = hbarOmegaD / (2 * kB * Xc coupling) := by
  have hX := (Xc_spec coupling hc).1
  constructor
  · rintro ⟨hT, h⟩
    rw [gapIntegral_zero_eq _ _ _ hkB hT, tanhInt_eq_iff _ hc] at h
    rw [← h]
    field_simp
  · intro h
    have hT : 0 < T := by rw [h]; positivity
    refine ⟨hT, ?_⟩
    rw [gapIntegral_zero_eq _ _ _ hkB hT, tanhInt_eq_iff _ hc, h]
    field_simp

theorem criticalTemperature_existsUnique' (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    ∃! T : ℝ, 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling :=
  ⟨_, (gap_Tc_iff kB hbarOmegaD coupling hkB hω hc _).mpr rfl,
    fun T hT => (gap_Tc_iff kB hbarOmegaD coupling hkB hω hc T).mp hT⟩

theorem criticalTemperature_eq (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    criticalTemperature kB hbarOmegaD coupling = hbarOmegaD / (2 * kB * Xc coupling) := by
  unfold criticalTemperature
  have : {T : ℝ | 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling} =
      {hbarOmegaD / (2 * kB * Xc coupling)} := by
    ext T
    exact gap_Tc_iff kB hbarOmegaD coupling hkB hω hc T
  rw [this, csSup_singleton]

theorem criticalTemperature_pos (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    0 < criticalTemperature kB hbarOmegaD coupling := by
  rw [criticalTemperature_eq kB hbarOmegaD coupling hkB hω hc]
  have := (Xc_spec coupling hc).1
  positivity

theorem tendsto_Xc : Tendsto Xc (𝓝[>] 0) atTop := by
  rw [tendsto_atTop]
  intro M
  have hinv : Tendsto (fun c : ℝ => 1 / c) (𝓝[>] 0) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  filter_upwards [self_mem_nhdsWithin, (tendsto_atTop.mp hinv) (tanhInt M + 1)] with c hc h1
  have hc' : (0:ℝ) < c := hc
  by_contra hlt
  have := strictMono_tanhInt.monotone (not_le.mp hlt).le
  rw [(Xc_spec c hc').2] at this
  linarith

theorem tendsto_Xc_mul_exp :
    Tendsto (fun c : ℝ => Xc c * Real.exp (-1 / c)) (𝓝[>] 0) (𝓝 (Real.exp (-tanhConst))) := by
  have h := ((tendsto_tanhInt_sub_log.comp tendsto_Xc).neg).rexp
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc' : (0:ℝ) < c := hc
  obtain ⟨hX, hXeq⟩ := Xc_spec c hc'
  simp only [Function.comp]
  rw [hXeq, neg_sub, Real.exp_sub, Real.exp_log hX, neg_div, Real.exp_neg, div_eq_mul_inv,
    one_div]

theorem criticalTemperature_weak_coupling' (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        kB * criticalTemperature kB hbarOmegaD coupling /
          (hbarOmegaD * Real.exp (-1 / coupling)))
      (𝓝[>] 0) (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / Real.pi)) := by
  have h := (tendsto_Xc_mul_exp.const_mul 2).inv₀ (by positivity)
  have e : 2 * Real.exp Real.eulerMascheroniConstant / Real.pi =
      (2 * Real.exp (-tanhConst))⁻¹ := by
    unfold tanhConst
    rw [Real.exp_neg, Real.exp_sub, Real.exp_add, Real.exp_log Real.pi_pos,
      show 2 * Real.log 2 = Real.log 4 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    field_simp
    ring
  rw [e]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc' : (0:ℝ) < c := hc
  have hX := (Xc_spec c hc').1
  rw [criticalTemperature_eq kB hbarOmegaD c hkB hω hc']
  have := Real.exp_pos (-1 / c)
  field_simp

end BCSAux
end Dev_Tc

section Dev_Main

open Filter Topology

namespace BCSAux

open BCSTheory

theorem gap_ratio_weak_coupling' (kB hbarOmegaD : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD) :
    Tendsto (fun coupling : ℝ =>
        zeroTemperatureGap hbarOmegaD coupling /
          (kB * criticalTemperature kB hbarOmegaD coupling))
      (𝓝[>] 0) (𝓝 (Real.pi / Real.exp Real.eulerMascheroniConstant)) := by
  have h1 := zeroTemperatureGap_weak_coupling hbarOmegaD hω
  have h2 := (criticalTemperature_weak_coupling' kB hbarOmegaD hkB hω).inv₀ (by positivity)
  have h := (h1.mul (h2.const_mul 2))
  have e : Real.pi / Real.exp Real.eulerMascheroniConstant =
      1 * (2 * (2 * Real.exp Real.eulerMascheroniConstant / Real.pi)⁻¹) := by
    field_simp
  rw [e]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc' : (0:ℝ) < c := hc
  have hT := criticalTemperature_pos kB hbarOmegaD c hkB hω hc'
  have := Real.exp_pos (-1 / c)
  field_simp

theorem criticalTemperature_isotope_effect' (kB C coupling M : ℝ) (hkB : 0 < kB)
    (hC : 0 < C) (hc : 0 < coupling) (hM : 0 < M) :
    criticalTemperature kB (C / Real.sqrt M) coupling =
      criticalTemperature kB C coupling * M ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  rw [criticalTemperature_eq kB _ coupling hkB (by positivity) hc,
    criticalTemperature_eq kB _ coupling hkB hC hc, Real.rpow_neg hM.le,
    ← Real.sqrt_eq_rpow]
  have := (Xc_spec coupling hc).1
  field_simp

lemma one_sub_two_fermiDirac (kB E T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    1 - 2 * fermiDirac kB E T = Real.tanh (E / (2 * kB * T)) := by
  unfold fermiDirac
  set y := E / (2 * kB * T) with hy
  have e : E / (kB * T) = 2 * y := by rw [hy]; field_simp
  rw [e, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [h1, h2]
  have := Real.exp_pos y
  field_simp
  ring

theorem gapIntegral_fermiDirac_form' (kB hbarOmegaD Δ T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    (∫ η in (0 : ℝ)..hbarOmegaD,
        (1 - 2 * fermiDirac kB (quasiparticleEnergy η Δ) T) / quasiparticleEnergy η Δ) =
      gapIntegral kB hbarOmegaD Δ T := by
  unfold gapIntegral
  congr 1
  ext η
  rw [one_sub_two_fermiDirac kB _ T hkB hT]

end BCSAux
end Dev_Main

section Dev_Gap

open Filter Topology

namespace BCSAux

open BCSTheory

lemma summable_tanhSeries_terms (x : ℝ) : Summable (fun k : ℕ => 2 / (bk k ^ 2 + x ^ 2)) :=
  Summable.of_norm_bounded summable_inv_bk_sq (tanhSeries_bound · x)

lemma continuous_tanhSeries : Continuous tanhSeries := by
  apply continuous_tsum (fun k => ?_) summable_inv_bk_sq tanhSeries_bound
  have := bk_pos k
  apply Continuous.div continuous_const (by fun_prop)
  intro x; positivity

lemma tanhSeries_eq (x : ℝ) (hx : x ≠ 0) : tanhSeries x = Real.tanh x / x := by
  rw [← (hasSum_tanh_div x hx).tsum_eq]
  unfold tanhSeries bk
  apply tsum_congr
  intro k; ring

lemma tanhSeries_strictAntiOn : StrictAntiOn tanhSeries (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  unfold tanhSeries
  apply Summable.tsum_lt_tsum (i := 0) _ _ (summable_tanhSeries_terms y)
    (summable_tanhSeries_terms x)
  · intro k
    have := bk_pos k
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  · have := bk_pos 0
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith

lemma tanhSeries_le (x : ℝ) (hx : 0 < x) : tanhSeries x ≤ 1 / x := by
  rw [tanhSeries_eq x hx.ne']
  apply div_le_div_of_nonneg_right _ hx.le
  exact (Real.tanh_lt_one x).le

lemma tanhSeries_pos' (x : ℝ) : 0 < tanhSeries x := tanhSeries_pos x

/-- A continuous version of the gap integral. -/
noncomputable def gapJ (kB hbarOmegaD T Δ : ℝ) : ℝ :=
  ∫ η in (0 : ℝ)..hbarOmegaD,
    1 / (2 * kB * T) * tanhSeries (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T))

lemma integrand_eq (a E : ℝ) (ha : 0 < a) (hE : E ≠ 0) :
    Real.tanh (E / a) / E = 1 / a * tanhSeries (E / a) := by
  rw [tanhSeries_eq _ (div_ne_zero hE ha.ne')]
  field_simp

lemma gapIntegral_eq_gapJ (kB hbarOmegaD Δ T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    gapIntegral kB hbarOmegaD Δ T = gapJ kB hbarOmegaD T Δ := by
  have ha : 0 < 2 * kB * T := by positivity
  unfold gapIntegral gapJ quasiparticleEnergy
  apply intervalIntegral.integral_congr_ae
  have : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (0:ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [this] with η hη _
  apply integrand_eq _ _ ha
  apply (Real.sqrt_pos.mpr _).ne'
  positivity

lemma continuous_gapJ (kB hbarOmegaD T : ℝ) : Continuous (gapJ kB hbarOmegaD T) := by
  unfold gapJ
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.mul continuous_const
  apply continuous_tanhSeries.comp
  apply Continuous.div_const
  fun_prop

lemma gapJ_strictAntiOn (kB hbarOmegaD T : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (hω : 0 < hbarOmegaD) : StrictAntiOn (gapJ kB hbarOmegaD T) (Set.Ici 0) := by
  have ha : 0 < 2 * kB * T := by positivity
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  unfold gapJ
  have hc : ∀ Δ : ℝ, Continuous (fun η : ℝ =>
      1 / (2 * kB * T) * tanhSeries (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T))) := by
    intro Δ
    apply Continuous.mul continuous_const
    apply continuous_tanhSeries.comp
    apply Continuous.div_const
    fun_prop
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hω
    (hc y).continuousOn (hc x).continuousOn
  · intro η _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply tanhSeries_strictAntiOn.antitoneOn (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr (by positivity))
    apply div_le_div_of_nonneg_right _ ha.le
    apply Real.sqrt_le_sqrt
    nlinarith
  · refine ⟨hbarOmegaD / 2, ⟨by linarith, by linarith⟩, ?_⟩
    apply mul_lt_mul_of_pos_left _ (by positivity)
    apply tanhSeries_strictAntiOn (Set.mem_Ici.mpr (by positivity))
      (Set.mem_Ici.mpr (by positivity))
    apply div_lt_div_of_pos_right _ ha
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith

lemma gapJ_le (kB hbarOmegaD T Δ : ℝ) (hkB : 0 < kB) (hT : 0 < T)
    (hω : 0 < hbarOmegaD) (hΔ : 0 < Δ) : gapJ kB hbarOmegaD T Δ ≤ hbarOmegaD / Δ := by
  have ha : 0 < 2 * kB * T := by positivity
  unfold gapJ
  have : ∫ η in (0:ℝ)..hbarOmegaD, (1 / Δ) = hbarOmegaD / Δ := by
    simp [div_eq_mul_inv]
  rw [← this]
  apply intervalIntegral.integral_mono_on hω.le
  · apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply continuous_tanhSeries.comp
    apply Continuous.div_const
    fun_prop
  · simp
  · intro η _
    have hE : Δ ≤ Real.sqrt (η ^ 2 + Δ ^ 2) := by
      have := Real.sqrt_le_sqrt (show Δ ^ 2 ≤ η ^ 2 + Δ ^ 2 by nlinarith)
      rwa [Real.sqrt_sq hΔ.le] at this
    have hEpos : 0 < Real.sqrt (η ^ 2 + Δ ^ 2) := lt_of_lt_of_le hΔ hE
    have h1 := tanhSeries_le (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T)) (by positivity)
    calc 1 / (2 * kB * T) * tanhSeries (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T))
        ≤ 1 / (2 * kB * T) * (1 / (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / Real.sqrt (η ^ 2 + Δ ^ 2) := by field_simp
      _ ≤ 1 / Δ := one_div_le_one_div_of_le hΔ hE

lemma gapJ_zero (kB hbarOmegaD T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    gapJ kB hbarOmegaD T 0 = tanhInt (hbarOmegaD / (2 * kB * T)) := by
  rw [← gapIntegral_eq_gapJ _ _ _ _ hkB hT, gapIntegral_zero_eq _ _ _ hkB hT]

theorem gap_existsUnique_below_Tc' (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    (∀ T : ℝ, 0 < T → T < criticalTemperature kB hbarOmegaD coupling →
      ∃! Δ : ℝ, 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling) ∧
    (∀ T : ℝ, criticalTemperature kB hbarOmegaD coupling ≤ T →
      ¬ ∃ Δ : ℝ, 0 < Δ ∧ gapIntegral kB hbarOmegaD Δ T = 1 / coupling) := by
  have hTc := criticalTemperature_eq kB hbarOmegaD coupling hkB hω hc
  have hTcpos := criticalTemperature_pos kB hbarOmegaD coupling hkB hω hc
  obtain ⟨hX, hXeq⟩ := Xc_spec coupling hc
  have hXc : hbarOmegaD / (2 * kB * criticalTemperature kB hbarOmegaD coupling) = Xc coupling := by
    rw [hTc]; field_simp
  constructor
  · intro T hT hTlt
    have h0 : 1 / coupling < gapJ kB hbarOmegaD T 0 := by
      rw [gapJ_zero _ _ _ hkB hT, ← hXeq, ← hXc]
      apply strictMono_tanhInt
      apply div_lt_div_of_pos_left hω (by positivity)
      nlinarith
    set D : ℝ := hbarOmegaD * coupling + 1 with hD
    have hDpos : 0 < D := by positivity
    have h1 : gapJ kB hbarOmegaD T D < 1 / coupling := by
      refine lt_of_le_of_lt (gapJ_le _ _ _ _ hkB hT hω hDpos) ?_
      rw [div_lt_div_iff₀ hDpos hc]
      nlinarith
    obtain ⟨Δ, hΔmem, hΔeq⟩ := intermediate_value_Icc' hDpos.le
      (continuous_gapJ kB hbarOmegaD T).continuousOn ⟨h1.le, h0.le⟩
    have hΔpos : 0 < Δ := by
      rcases hΔmem.1.eq_or_lt with h | h
      · rw [← h] at hΔeq; linarith
      · exact h
    refine ⟨Δ, ⟨hΔpos, by rw [gapIntegral_eq_gapJ _ _ _ _ hkB hT, hΔeq]⟩, ?_⟩
    rintro Δ' ⟨hΔ'pos, hΔ'eq⟩
    rw [gapIntegral_eq_gapJ _ _ _ _ hkB hT] at hΔ'eq
    exact (gapJ_strictAntiOn kB hbarOmegaD T hkB hT hω).injOn (Set.mem_Ici.mpr hΔ'pos.le)
      (Set.mem_Ici.mpr hΔpos.le) (hΔ'eq.trans hΔeq.symm)
  · intro T hTge ⟨Δ, hΔpos, hΔeq⟩
    have hT : 0 < T := lt_of_lt_of_le hTcpos hTge
    rw [gapIntegral_eq_gapJ _ _ _ _ hkB hT] at hΔeq
    have h1 := gapJ_strictAntiOn kB hbarOmegaD T hkB hT hω (Set.mem_Ici.mpr le_rfl)
      (Set.mem_Ici.mpr hΔpos.le) hΔpos
    have h2 : gapJ kB hbarOmegaD T 0 ≤ 1 / coupling := by
      rw [gapJ_zero _ _ _ hkB hT, ← hXeq, ← hXc]
      apply strictMono_tanhInt.monotone
      apply div_le_div_of_nonneg_left hω.le (by positivity)
      nlinarith
    linarith

end BCSAux
end Dev_Gap

section Dev_NearTc

open Filter Topology

namespace BCSAux

open BCSTheory

/-- `R(w) = ∑ 2 / (b_k² + w)`, so that `tanhSeries x = R(x²)`. -/
noncomputable def Rs (w : ℝ) : ℝ := ∑' k : ℕ, 2 / (bk k ^ 2 + w)

lemma tanhSeries_eq_Rs (x : ℝ) : tanhSeries x = Rs (x ^ 2) := rfl

lemma one_lt_bk (k : ℕ) : 1 < bk k := by
  unfold bk
  have := Real.pi_gt_three
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma summable_Rs_terms (w : ℝ) (hw : 0 ≤ w) : Summable (fun k : ℕ => 2 / (bk k ^ 2 + w)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_inv_bk_sq
  · have := bk_pos k; positivity
  · have := bk_pos k
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- Clamped difference-quotient kernel `Q(w₁,w₂) = ∑ 2 / ((b_k² + w₁)(b_k² + w₂))`. -/
noncomputable def Qc (w1 w2 : ℝ) : ℝ :=
  ∑' k : ℕ, 2 / ((bk k ^ 2 + max w1 0) * (bk k ^ 2 + max w2 0))

lemma Qc_term_bound (k : ℕ) (w1 w2 : ℝ) :
    ‖2 / ((bk k ^ 2 + max w1 0) * (bk k ^ 2 + max w2 0))‖ ≤ 2 / bk k ^ 2 := by
  have hb := bk_pos k
  have hb1 := one_lt_bk k
  have h1 : 0 ≤ max w1 0 := le_max_right _ _
  have h2 : 0 ≤ max w2 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have : bk k ^ 2 ≥ 1 := by nlinarith
  nlinarith [mul_le_mul this this (by norm_num) (by positivity)]

lemma summable_Qc_terms (w1 w2 : ℝ) :
    Summable (fun k : ℕ => 2 / ((bk k ^ 2 + max w1 0) * (bk k ^ 2 + max w2 0))) :=
  Summable.of_norm_bounded summable_inv_bk_sq (Qc_term_bound · w1 w2)

lemma continuous_Qc : Continuous (fun p : ℝ × ℝ => Qc p.1 p.2) := by
  unfold Qc
  refine continuous_tsum
    (f := fun k (p : ℝ × ℝ) => 2 / ((bk k ^ 2 + max p.1 0) * (bk k ^ 2 + max p.2 0)))
    (fun k => ?_) summable_inv_bk_sq (fun k p => Qc_term_bound k p.1 p.2)
  have hb := bk_pos k
  apply Continuous.div continuous_const (by fun_prop)
  intro p
  have h1 : 0 ≤ max p.1 0 := le_max_right _ _
  have h2 : 0 ≤ max p.2 0 := le_max_right _ _
  positivity

lemma Qc_pos (w1 w2 : ℝ) : 0 < Qc w1 w2 := by
  unfold Qc
  apply (summable_Qc_terms w1 w2).tsum_pos (fun k => ?_) 0
  · have hb := bk_pos 0
    have h1 : 0 ≤ max w1 0 := le_max_right _ _
    have h2 : 0 ≤ max w2 0 := le_max_right _ _
    positivity
  · have hb := bk_pos k
    have h1 : 0 ≤ max w1 0 := le_max_right _ _
    have h2 : 0 ≤ max w2 0 := le_max_right _ _
    positivity

lemma Rs_sub (w1 w2 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    Rs w1 - Rs w2 = (w2 - w1) * Qc w1 w2 := by
  unfold Rs Qc
  rw [← (summable_Rs_terms w1 h1).tsum_sub (summable_Rs_terms w2 h2),
    ← (summable_Qc_terms w1 w2).tsum_mul_left]
  apply tsum_congr
  intro k
  have hb := bk_pos k
  rw [max_eq_left h1, max_eq_left h2]
  field_simp
  ring

/-- The gap integral as a function of `v = Δ²`, written with `Rs`. -/
lemma gapJ_sqrt_eq (kB hbarOmegaD T v : ℝ) (hv : 0 ≤ v) :
    gapJ kB hbarOmegaD T (Real.sqrt v) =
      ∫ η in (0:ℝ)..hbarOmegaD, 1 / (2 * kB * T) * Rs ((η ^ 2 + v) / (2 * kB * T) ^ 2) := by
  unfold gapJ
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [tanhSeries_eq_Rs, Real.sq_sqrt hv, div_pow, Real.sq_sqrt (by positivity)]

/-- Clamped kernel integral `P(v,T)`. -/
noncomputable def Pc (kB hbarOmegaD T0 v T : ℝ) : ℝ :=
  ∫ η in (0:ℝ)..hbarOmegaD,
    1 / (2 * kB * max T T0) ^ 3 *
      Qc ((η ^ 2 + v) / (2 * kB * max T T0) ^ 2) (η ^ 2 / (2 * kB * max T T0) ^ 2)

lemma continuous_Pc (kB hbarOmegaD T0 : ℝ) (hkB : 0 < kB) (hT0 : 0 < T0) :
    Continuous (fun p : ℝ × ℝ => Pc kB hbarOmegaD T0 p.1 p.2) := by
  unfold Pc
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hpos : ∀ T : ℝ, 0 < 2 * kB * max T T0 := fun T => by
    have : T0 ≤ max T T0 := le_max_right _ _
    have : 0 < max T T0 := lt_of_lt_of_le hT0 this
    positivity
  apply Continuous.mul
  · apply Continuous.div continuous_const (by fun_prop)
    intro p; exact (pow_pos (hpos _) 3).ne'
  · have hc := continuous_Qc
    refine hc.comp (Continuous.prodMk ?_ ?_)
    · apply Continuous.div (by fun_prop) (by fun_prop)
      intro p; exact (pow_pos (hpos _) 2).ne'
    · apply Continuous.div (by fun_prop) (by fun_prop)
      intro p; exact (pow_pos (hpos _) 2).ne'

lemma Pc_pos (kB hbarOmegaD T0 v T : ℝ) (hkB : 0 < kB) (hT0 : 0 < T0) (hω : 0 < hbarOmegaD) :
    0 < Pc kB hbarOmegaD T0 v T := by
  have hpos : 0 < 2 * kB * max T T0 := by
    have : 0 < max T T0 := lt_of_lt_of_le hT0 (le_max_right _ _)
    positivity
  unfold Pc
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hω
  · apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    refine continuous_Qc.comp (Continuous.prodMk ?_ ?_) <;> fun_prop
  · intro η _
    have := Qc_pos ((η ^ 2 + v) / (2 * kB * max T T0) ^ 2) (η ^ 2 / (2 * kB * max T T0) ^ 2)
    positivity

lemma continuous_gapJ_integrand (kB T Δ : ℝ) : Continuous (fun η : ℝ =>
    1 / (2 * kB * T) * tanhSeries (Real.sqrt (η ^ 2 + Δ ^ 2) / (2 * kB * T))) := by
  apply Continuous.mul continuous_const
  apply continuous_tanhSeries.comp
  apply Continuous.div_const
  fun_prop

lemma gapJ_sub (kB hbarOmegaD T0 v T : ℝ) (hkB : 0 < kB) (hT0 : 0 < T0) (hT : T0 ≤ T)
    (hv : 0 ≤ v) :
    gapJ kB hbarOmegaD T (Real.sqrt v) - gapJ kB hbarOmegaD T 0 =
      -v * Pc kB hbarOmegaD T0 v T := by
  have hTpos : 0 < T := lt_of_lt_of_le hT0 hT
  have hmax : max T T0 = T := max_eq_left hT
  have ha : 0 < 2 * kB * T := by positivity
  unfold gapJ
  rw [← intervalIntegral.integral_sub ((continuous_gapJ_integrand _ _ _).intervalIntegrable _ _)
    ((continuous_gapJ_integrand _ _ _).intervalIntegrable _ _)]
  unfold Pc
  rw [hmax, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  have e1 : Real.sqrt (η ^ 2 + Real.sqrt v ^ 2) ^ 2 = η ^ 2 + v := by
    rw [Real.sq_sqrt hv, Real.sq_sqrt (by positivity)]
  have e2 : Real.sqrt (η ^ 2 + 0 ^ 2) ^ 2 = η ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]; ring
  rw [tanhSeries_eq_Rs, tanhSeries_eq_Rs, ← mul_sub, div_pow, div_pow, e1, e2,
    Rs_sub _ _ (by positivity) (by positivity)]
  field_simp
  ring

end BCSAux

namespace BCSAux

open BCSTheory

lemma gap_spec_below (kB hbarOmegaD coupling T : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) (hT : 0 < T) (hTlt : T < criticalTemperature kB hbarOmegaD coupling) :
    0 < gap kB hbarOmegaD coupling T ∧
      gapIntegral kB hbarOmegaD (gap kB hbarOmegaD coupling T) T = 1 / coupling := by
  obtain ⟨Δ, ⟨hpos, heq⟩, huniq⟩ :=
    (gap_existsUnique_below_Tc' kB hbarOmegaD coupling hkB hω hc).1 T hT hTlt
  have : {Δ' : ℝ | 0 < Δ' ∧ gapIntegral kB hbarOmegaD Δ' T = 1 / coupling} = {Δ} := by
    ext Δ'
    simp only [Set.mem_singleton_iff]
    exact ⟨fun h => huniq Δ' h, fun h => h ▸ ⟨hpos, heq⟩⟩
  unfold gap
  rw [this, csSup_singleton]
  exact ⟨hpos, heq⟩

lemma gap_at_Tc (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    gap kB hbarOmegaD coupling (criticalTemperature kB hbarOmegaD coupling) = 0 := by
  have h := (gap_existsUnique_below_Tc' kB hbarOmegaD coupling hkB hω hc).2 _ le_rfl
  have : {Δ' : ℝ | 0 < Δ' ∧ gapIntegral kB hbarOmegaD Δ'
      (criticalTemperature kB hbarOmegaD coupling) = 1 / coupling} = ∅ := by
    ext Δ'
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun h' => h ⟨Δ', h'⟩
  unfold gap
  rw [this, Real.sSup_empty]

lemma near_Tc_alg (u P d T Tc : ℝ) (hP : P ≠ 0) (hne : T - Tc ≠ 0) (hTc : Tc ≠ 0)
    (hk : u * P = d) : -Tc * (d / (T - Tc)) / P = u / (1 - T / Tc) := by
  subst hk
  have : 1 - T / Tc = -(T - Tc) / Tc := by field_simp; ring
  rw [this]
  field_simp

/-- The coefficient `L(λ)` of `Δ(T)² ≈ L(λ) (1 - T/T_c)`. -/
noncomputable def Lcoef (kB hbarOmegaD coupling : ℝ) : ℝ :=
  tanhSeries (Xc coupling) * Xc coupling /
    Pc kB hbarOmegaD (criticalTemperature kB hbarOmegaD coupling / 2) 0
      (criticalTemperature kB hbarOmegaD coupling)

theorem gap_sq_near_Tc (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    Tendsto (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2 /
        (1 - T / criticalTemperature kB hbarOmegaD coupling))
      (𝓝[<] (criticalTemperature kB hbarOmegaD coupling)) (𝓝 (Lcoef kB hbarOmegaD coupling)) := by
  have hTc := criticalTemperature_pos kB hbarOmegaD coupling hkB hω hc
  have hTceq := criticalTemperature_eq kB hbarOmegaD coupling hkB hω hc
  obtain ⟨hX, hXeq⟩ := Xc_spec coupling hc
  unfold Lcoef
  set Tc := criticalTemperature kB hbarOmegaD coupling with hTc_def
  set X := Xc coupling with hX_def
  set T0 := Tc / 2 with hT0
  have hT0pos : 0 < T0 := by positivity
  have hT0lt : T0 < Tc := by rw [hT0]; linarith
  have hXdef : hbarOmegaD / (2 * kB * Tc) = X := by rw [hTceq]; field_simp
  set H0 : ℝ → ℝ := fun T => tanhInt (hbarOmegaD / (2 * kB * T)) with hH0
  set u : ℝ → ℝ := fun T => gap kB hbarOmegaD coupling T ^ 2 with hu
  have hH0Tc : H0 Tc = 1 / coupling := by simp only [hH0]; rw [hXdef, hXeq]
  have key : ∀ T, T0 ≤ T → T < Tc → u T * Pc kB hbarOmegaD T0 (u T) T = H0 T - H0 Tc := by
    intro T hT1 hT2
    have hT : 0 < T := lt_of_lt_of_le hT0pos hT1
    obtain ⟨hg, hgeq⟩ := gap_spec_below kB hbarOmegaD coupling T hkB hω hc hT hT2
    have h := gapJ_sub kB hbarOmegaD T0 (u T) T hkB hT0pos hT1 (by positivity)
    simp only [hu] at h
    rw [Real.sqrt_sq hg.le, ← gapIntegral_eq_gapJ _ _ _ _ hkB hT, hgeq,
      gapJ_zero _ _ _ hkB hT] at h
    rw [hH0Tc]
    simp only [hH0, hu]
    linarith
  have hderiv : HasDerivAt H0 (tanhSeries X * (hbarOmegaD / (2 * kB) * (-(Tc ^ 2)⁻¹))) Tc := by
    have h1 : HasDerivAt (fun T => hbarOmegaD / (2 * kB) * T⁻¹)
        (hbarOmegaD / (2 * kB) * (-(Tc ^ 2)⁻¹)) Tc :=
      (hasDerivAt_inv hTc.ne').const_mul _
    have e2 : hbarOmegaD / (2 * kB) * Tc⁻¹ = X := by rw [← hXdef]; ring
    have h2 := (hasDerivAt_tanhInt (hbarOmegaD / (2 * kB) * Tc⁻¹)).comp Tc h1
    rw [e2] at h2
    refine h2.congr_of_eventuallyEq (Eventually.of_forall (fun T => ?_))
    show tanhInt _ = tanhInt _
    congr 1
    ring
  have hslope : Tendsto (fun T => (H0 T - H0 Tc) / (T - Tc)) (𝓝[<] Tc)
      (𝓝 (tanhSeries X * (hbarOmegaD / (2 * kB) * (-(Tc ^ 2)⁻¹)))) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
      (nhdsWithin_mono _ (fun y (hy : y < Tc) => ne_of_lt hy))
    refine h.congr (fun T => ?_)
    rw [slope_def_field]
  have hH0c : Tendsto H0 (𝓝[<] Tc) (𝓝 (H0 Tc)) :=
    hderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu0 : Tendsto u (𝓝[<] Tc) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hPε := Pc_pos kB hbarOmegaD T0 ε Tc hkB hT0pos hω
    have hcontP : Tendsto (fun T => Pc kB hbarOmegaD T0 ε T) (𝓝[<] Tc)
        (𝓝 (Pc kB hbarOmegaD T0 ε Tc)) :=
      (((continuous_Pc kB hbarOmegaD T0 hkB hT0pos).comp
        (Continuous.prodMk continuous_const continuous_id)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have e1 := hcontP.eventually (lt_mem_nhds (half_lt_self hPε))
    have e2 : ∀ᶠ T in 𝓝[<] Tc, H0 T - H0 Tc < ε * (Pc kB hbarOmegaD T0 ε Tc / 2) := by
      have h := hH0c.sub_const (H0 Tc)
      rw [sub_self] at h
      exact (tendsto_order.1 h).2 _ (by positivity)
    filter_upwards [e1, e2, Ioo_mem_nhdsLT hT0lt] with T h1 h2 h3
    have hT : 0 < T := lt_trans hT0pos h3.1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by simp only [hu]; positivity)]
    by_contra hge
    have hge' : ε ≤ u T := not_lt.mp hge
    have hk := key T h3.1.le h3.2
    have hmono : gapJ kB hbarOmegaD T (Real.sqrt (u T)) ≤ gapJ kB hbarOmegaD T (Real.sqrt ε) :=
      (gapJ_strictAntiOn kB hbarOmegaD T hkB hT hω).antitoneOn
        (Set.mem_Ici.mpr (Real.sqrt_nonneg _)) (Set.mem_Ici.mpr (Real.sqrt_nonneg _))
        (Real.sqrt_le_sqrt hge')
    have hsub1 := gapJ_sub kB hbarOmegaD T0 (u T) T hkB hT0pos h3.1.le (by simp only [hu]; positivity)
    have hsub2 := gapJ_sub kB hbarOmegaD T0 ε T hkB hT0pos h3.1.le hε.le
    have : ε * Pc kB hbarOmegaD T0 ε T > ε * (Pc kB hbarOmegaD T0 ε Tc / 2) :=
      mul_lt_mul_of_pos_left h1 hε
    linarith
  have hP : Tendsto (fun T => Pc kB hbarOmegaD T0 (u T) T) (𝓝[<] Tc)
      (𝓝 (Pc kB hbarOmegaD T0 0 Tc)) := by
    have hc2 : Tendsto (fun p : ℝ × ℝ => Pc kB hbarOmegaD T0 p.1 p.2) (𝓝 ((0:ℝ), Tc))
        (𝓝 (Pc kB hbarOmegaD T0 0 Tc)) :=
      (continuous_Pc kB hbarOmegaD T0 hkB hT0pos).tendsto ((0:ℝ), Tc)
    have hpair : Tendsto (fun T => (u T, T)) (𝓝[<] Tc) (𝓝 ((0:ℝ), Tc)) :=
      hu0.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
    have h3 := hc2.comp hpair
    simp only [Function.comp_def] at h3
    exact h3
  have hPpos := Pc_pos kB hbarOmegaD T0 0 Tc hkB hT0pos hω
  have hlim := (hslope.const_mul (-Tc)).div hP hPpos.ne'
  have hval : -Tc * (tanhSeries X * (hbarOmegaD / (2 * kB) * (-(Tc ^ 2)⁻¹))) /
      Pc kB hbarOmegaD T0 0 Tc = tanhSeries X * X / Pc kB hbarOmegaD T0 0 Tc := by
    congr 1
    rw [← hXdef]
    field_simp
  rw [← hval]
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hT0lt] with T hT
  have hk := key T hT.1.le hT.2
  have hP' := Pc_pos kB hbarOmegaD T0 (u T) T hkB hT0pos hω
  have hne : T - Tc ≠ 0 := sub_ne_zero.mpr (ne_of_lt hT.2)
  exact near_Tc_alg _ _ _ _ _ hP'.ne' hne hTc.ne' hk

end BCSAux
end Dev_NearTc

section Dev_NearTc2

open Filter Topology

namespace BCSAux

open BCSTheory

/-- `K(X) = ∫₀^X ∑ 2/(x² + b_k²)² dx`. -/
noncomputable def Kint (X : ℝ) : ℝ := ∫ x in (0:ℝ)..X, Qc (x ^ 2) (x ^ 2)

lemma Pc_zero_eq (kB hbarOmegaD Tc : ℝ) (hkB : 0 < kB) (hTc : 0 < Tc) :
    Pc kB hbarOmegaD (Tc / 2) 0 Tc =
      Kint (hbarOmegaD / (2 * kB * Tc)) / (2 * kB * Tc) ^ 2 := by
  have hmax : max Tc (Tc / 2) = Tc := max_eq_left (by linarith)
  have ha : 0 < 2 * kB * Tc := by positivity
  unfold Pc Kint
  rw [hmax]
  have h := intervalIntegral.integral_comp_div (fun y => Qc (y ^ 2) (y ^ 2)) ha.ne'
    (a := 0) (b := hbarOmegaD)
  simp only [zero_div, smul_eq_mul, div_pow] at h
  simp only [add_zero]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

/-- The antiderivative of `2/(x²+b²)²`. -/
noncomputable def kterm (b X : ℝ) : ℝ := X / (b ^ 2 * (X ^ 2 + b ^ 2)) + Real.arctan (X / b) / b ^ 3

lemma hasDerivAt_kterm (b : ℝ) (hb : 0 < b) (x : ℝ) :
    HasDerivAt (kterm b) (2 / ((b ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))) x := by
  have h1 : HasDerivAt (fun X => X / (b ^ 2 * (X ^ 2 + b ^ 2)))
      ((1 * (b ^ 2 * (x ^ 2 + b ^ 2)) - x * (b ^ 2 * (2 * x))) / (b ^ 2 * (x ^ 2 + b ^ 2)) ^ 2) x := by
    have hd : HasDerivAt (fun X => b ^ 2 * (X ^ 2 + b ^ 2)) (b ^ 2 * (2 * x)) x := by
      have := ((hasDerivAt_pow 2 x).add_const (b ^ 2)).const_mul (b ^ 2)
      exact this.congr_deriv (by norm_num)
    exact (hasDerivAt_id x).div hd (by positivity)
  have h2 : HasDerivAt (fun X => Real.arctan (X / b) / b ^ 3)
      (1 / (1 + (x / b) ^ 2) * (1 / b) / b ^ 3) x :=
    (((hasDerivAt_id x).div_const b).arctan).div_const (b ^ 3)
  refine (h1.add h2).congr_deriv ?_
  field_simp
  ring

lemma kterm_bound (b X : ℝ) (hb : 1 < b) (hX : 0 ≤ X) : ‖kterm b X‖ ≤ 3 / b ^ 2 := by
  have hb0 : 0 < b := by linarith
  have h1 : 0 ≤ X / (b ^ 2 * (X ^ 2 + b ^ 2)) := by positivity
  have h2 : 0 ≤ Real.arctan (X / b) := Real.arctan_nonneg.mpr (by positivity)
  have h3 : Real.arctan (X / b) ≤ 2 := le_trans (Real.arctan_lt_pi_div_two _).le
    (by linarith [Real.pi_lt_four])
  have h4 : X / (b ^ 2 * (X ^ 2 + b ^ 2)) ≤ 1 / b ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (X - b), mul_pos hb0 hb0]
  unfold kterm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h5 : Real.arctan (X / b) / b ^ 3 ≤ 2 / b ^ 3 := div_le_div_of_nonneg_right h3 (by positivity)
  have h6 : 3 / b ^ 3 ≤ 3 / b ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_pos hb0 hb0]
  have : 1 / b ^ 3 + 2 / b ^ 3 = 3 / b ^ 3 := by ring
  linarith

lemma summable_three_div_bk_sq : Summable (fun k : ℕ => 3 / bk k ^ 2) := by
  have := summable_inv_bk_sq.mul_left (3 / 2)
  refine this.congr (fun k => ?_)
  ring

theorem Kint_eq_tsum (X : ℝ) : Kint X = ∑' k : ℕ, kterm (bk k) X := by
  have hderiv : ∀ x, HasDerivAt (fun X => ∑' k : ℕ, kterm (bk k) X)
      (∑' k : ℕ, 2 / ((bk k ^ 2 + x ^ 2) * (bk k ^ 2 + x ^ 2))) x := by
    intro x
    apply hasDerivAt_tsum summable_inv_bk_sq
      (fun k y => hasDerivAt_kterm (bk k) (bk_pos k) y) (fun k y => ?_) (y₀ := 0)
    · simp [kterm]
    · have := Qc_term_bound k (y ^ 2) (y ^ 2)
      rwa [max_eq_left (sq_nonneg y)] at this
  have hcont : Continuous (fun x : ℝ => Qc (x ^ 2) (x ^ 2)) :=
    continuous_Qc.comp ((continuous_pow 2).prodMk (continuous_pow 2))
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := X)
    (fun x _ => hderiv x) (f' := fun x => ∑' k : ℕ, 2 / ((bk k ^ 2 + x ^ 2) * (bk k ^ 2 + x ^ 2)))
    (by
      apply (hcont.intervalIntegrable 0 X).congr
      intro x _
      simp only [Qc, max_eq_left (sq_nonneg x)])
  have h0 : ∑' k : ℕ, kterm (bk k) 0 = 0 := by simp [kterm]
  rw [h0, sub_zero] at h1
  rw [← h1]
  unfold Kint
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Qc, max_eq_left (sq_nonneg x)]

/-- `∑ π / (2 b_k³)`. -/
noncomputable def kappaInf : ℝ := ∑' k : ℕ, Real.pi / 2 / bk k ^ 3

theorem tendsto_Kint : Tendsto Kint atTop (𝓝 kappaInf) := by
  have h : Tendsto (fun X => ∑' k : ℕ, kterm (bk k) X) atTop (𝓝 kappaInf) := by
    unfold kappaInf
    apply tendsto_tsum_of_dominated_convergence summable_three_div_bk_sq
    · intro k
      have hb := bk_pos k
      have h1 : Tendsto (fun X => X / (bk k ^ 2 * (X ^ 2 + bk k ^ 2))) atTop (𝓝 0) := by
        have : Tendsto (fun X : ℝ => (bk k ^ 2)⁻¹ * (X / (X ^ 2 + bk k ^ 2))) atTop (𝓝 ((bk k ^ 2)⁻¹ * 0)) := by
          apply Tendsto.const_mul
          have h2 : Tendsto (fun X : ℝ => X⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
          apply squeeze_zero' ?_ ?_ h2
          · filter_upwards [eventually_gt_atTop 0] with X hX
            positivity
          · filter_upwards [eventually_gt_atTop 0] with X hX
            rw [div_le_iff₀ (by positivity)]
            rw [inv_mul_eq_div, le_div_iff₀ hX]
            nlinarith
        rw [mul_zero] at this
        refine this.congr (fun X => ?_)
        field_simp
      have h2 : Tendsto (fun X => Real.arctan (X / bk k) / bk k ^ 3) atTop
          (𝓝 (Real.pi / 2 / bk k ^ 3)) := by
        apply Tendsto.div_const
        exact Real.tendsto_arctan_atTop.comp (tendsto_id.atTop_div_const hb) |>.mono_right
          nhdsWithin_le_nhds
      have := h1.add h2
      rw [zero_add] at this
      exact this
    · filter_upwards [eventually_ge_atTop 0] with X hX k
      exact kterm_bound (bk k) X (one_lt_bk k) hX
  refine h.congr (fun X => ?_)
  rw [Kint_eq_tsum]


lemma zeta_three_re_eq : (riemannZeta 3).re = ∑' n : ℕ, 1 / (n:ℝ) ^ 3 := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  push_cast at h
  rw [h]
  have : (∑' n : ℕ, 1 / (n:ℂ) ^ 3) = ((∑' n : ℕ, 1 / (n:ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  rw [this, Complex.ofReal_re]

lemma tsum_odd_cube : ∑' k : ℕ, 1 / (2 * (k:ℝ) + 1) ^ 3 = 7 / 8 * ∑' n : ℕ, 1 / (n:ℝ) ^ 3 := by
  set f : ℕ → ℝ := fun n => 1 / (n:ℝ) ^ 3 with hf
  have hs : Summable f := by
    simpa [hf] using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
  have i1 : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have i2 : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by simpa using h
  have he : Summable (fun k : ℕ => f (2 * k)) := hs.comp_injective i1
  have ho : Summable (fun k : ℕ => f (2 * k + 1)) := hs.comp_injective i2
  have h := tsum_even_add_odd he ho
  have h2 : ∑' k : ℕ, f (2 * k) = 1 / 8 * ∑' n : ℕ, f n := by
    rw [← tsum_mul_left]; congr 1; ext k; simp only [hf]; push_cast; field_simp; ring
  have h3 : ∑' k : ℕ, 1 / (2 * (k:ℝ) + 1) ^ 3 = ∑' k : ℕ, f (2 * k + 1) := by
    simp only [hf]; push_cast; rfl
  rw [h3]; linarith

theorem kappaInf_eq : kappaInf = 7 * (riemannZeta 3).re / (2 * Real.pi ^ 2) := by
  have hp := Real.pi_pos
  have e : (fun k : ℕ => Real.pi / 2 / bk k ^ 3) =
      fun k : ℕ => 4 / Real.pi ^ 2 * (1 / (2 * (k:ℝ) + 1) ^ 3) := by
    ext k; unfold bk; field_simp; ring
  unfold kappaInf
  rw [e, tsum_mul_left, tsum_odd_cube, zeta_three_re_eq]
  field_simp; ring

lemma tanh_eq_one_sub (x : ℝ) : Real.tanh x = 1 - 2 * (1 / (Real.exp (2 * x) + 1)) := by
  have h := one_sub_two_fermiDirac 1 (2 * x) 1 one_pos one_pos
  unfold BCSTheory.fermiDirac at h
  simp only [mul_one, div_one] at h
  rw [h]; congr 1; ring

lemma tendsto_tanh_atTop' : Tendsto Real.tanh atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => Real.exp (2 * x) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2)))
  have h2 := (h1.inv_tendsto_atTop).const_mul 2
  have h3 := h2.const_sub 1
  simp only [mul_zero, sub_zero] at h3
  refine h3.congr (fun x => ?_)
  rw [tanh_eq_one_sub]; simp [one_div]

lemma Lcoef_eq (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB) (hω : 0 < hbarOmegaD)
    (hc : 0 < coupling) :
    Lcoef kB hbarOmegaD coupling = Real.tanh (Xc coupling) *
      (2 * kB * criticalTemperature kB hbarOmegaD coupling) ^ 2 / Kint (Xc coupling) := by
  have hT := criticalTemperature_pos kB hbarOmegaD coupling hkB hω hc
  have hX := (Xc_spec coupling hc).1
  have hTe := criticalTemperature_eq kB hbarOmegaD coupling hkB hω hc
  have hXe : hbarOmegaD / (2 * kB * criticalTemperature kB hbarOmegaD coupling) = Xc coupling := by
    rw [hTe]; field_simp
  unfold Lcoef
  rw [Pc_zero_eq kB hbarOmegaD _ hkB hT, hXe, tanhSeries_eq _ hX.ne']
  have ha : 0 < 2 * kB * criticalTemperature kB hbarOmegaD coupling := by positivity
  rw [div_mul_cancel₀ _ hX.ne', div_div_eq_mul_div]

theorem gap_near_Tc_weak_coupling' (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    ∃ L : ℝ → ℝ,
      (∀ coupling : ℝ, 0 < coupling →
        Tendsto (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2 /
            (1 - T / criticalTemperature kB hbarOmegaD coupling))
          (𝓝[<] (criticalTemperature kB hbarOmegaD coupling)) (𝓝 (L coupling))) ∧
      Tendsto (fun coupling : ℝ => L coupling / zeroTemperatureGap hbarOmegaD coupling ^ 2)
        (𝓝[>] 0)
        (𝓝 (8 * Real.exp (2 * Real.eulerMascheroniConstant) / (7 * (riemannZeta 3).re))) := by
  refine ⟨Lcoef kB hbarOmegaD, fun c hc => gap_sq_near_Tc kB hbarOmegaD c hkB hω hc, ?_⟩
  have hr := gap_ratio_weak_coupling' kB hbarOmegaD hkB hω
  have hp := Real.pi_pos
  have he := Real.exp_pos Real.eulerMascheroniConstant
  have hr' := (hr.inv₀ (by positivity)).pow 2
  have ht := tendsto_tanh_atTop'.comp tendsto_Xc
  have hk := tendsto_Kint.comp tendsto_Xc
  have hz : 0 < (riemannZeta 3).re := by
    rw [zeta_three_re_eq]
    have hs : Summable (fun n : ℕ => 1 / (n:ℝ) ^ 3) := by
      simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have := hs.le_tsum 1 (fun j _ => by positivity)
    norm_num at this
    simp only [one_div]
    linarith
  have hkap : kappaInf ≠ 0 := by rw [kappaInf_eq]; positivity
  have hlim := ((ht.mul_const 4).mul hr').div hk hkap
  have htarget : 1 * 4 * (Real.pi / Real.exp Real.eulerMascheroniConstant)⁻¹ ^ 2 / kappaInf =
      8 * Real.exp (2 * Real.eulerMascheroniConstant) / (7 * (riemannZeta 3).re) := by
    rw [kappaInf_eq, show 2 * Real.eulerMascheroniConstant = Real.eulerMascheroniConstant +
      Real.eulerMascheroniConstant by ring, Real.exp_add]
    field_simp; ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc' : (0:ℝ) < c := hc
  simp only [Function.comp_apply, Pi.div_apply, inv_div]
  rw [Lcoef_eq kB hbarOmegaD c hkB hω hc']
  ring


theorem specific_heat_jump_weak_coupling' (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    ∃ D : ℝ → ℝ,
      (∀ coupling : ℝ, 0 < coupling →
        HasDerivWithinAt (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2) (D coupling)
          (Set.Iic (criticalTemperature kB hbarOmegaD coupling))
          (criticalTemperature kB hbarOmegaD coupling)) ∧
      Tendsto (fun coupling : ℝ => -D coupling /
          (2 * Real.pi ^ 2 / 3 * kB ^ 2 * criticalTemperature kB hbarOmegaD coupling))
        (𝓝[>] 0) (𝓝 (12 / (7 * (riemannZeta 3).re))) := by
  refine ⟨fun c => -Lcoef kB hbarOmegaD c / criticalTemperature kB hbarOmegaD c, ?_, ?_⟩
  · intro c hc
    have hT0 := criticalTemperature_pos kB hbarOmegaD c hkB hω hc
    have h0 := gap_at_Tc kB hbarOmegaD c hkB hω hc
    have h := (gap_sq_near_Tc kB hbarOmegaD c hkB hω hc).mul_const
      (-1 / criticalTemperature kB hbarOmegaD c)
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_diff_right]
    beta_reduce
    obtain ⟨Tc, hTc⟩ : ∃ Tc, Tc = criticalTemperature kB hbarOmegaD c := ⟨_, rfl⟩
    rw [← hTc] at h h0 hT0 ⊢
    have e : Lcoef kB hbarOmegaD c * (-1 / Tc) = -Lcoef kB hbarOmegaD c / Tc := by ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with T hT'
    have hlt : T < Tc := hT'
    rw [slope_def_field, h0, one_sub_div hT0.ne']
    have h1 : T - Tc ≠ 0 := by linarith
    have h2 : Tc - T ≠ 0 := by linarith
    field_simp
    ring
  · have hp := Real.pi_pos
    have hz : 0 < (riemannZeta 3).re := by
      rw [zeta_three_re_eq]
      have hs : Summable (fun n : ℕ => 1 / (n:ℝ) ^ 3) := by
        simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have := hs.le_tsum 1 (fun j _ => by positivity)
      norm_num at this
      simp only [one_div]
      linarith
    have hkap : kappaInf ≠ 0 := by rw [kappaInf_eq]; positivity
    have ht := tendsto_tanh_atTop'.comp tendsto_Xc
    have hk := tendsto_Kint.comp tendsto_Xc
    have hlim := (ht.mul_const (6 / Real.pi ^ 2)).div hk hkap
    have htarget : 1 * (6 / Real.pi ^ 2) / kappaInf = 12 / (7 * (riemannZeta 3).re) := by
      rw [kappaInf_eq]; field_simp; ring
    rw [htarget] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hc' : (0:ℝ) < c := hc
    have hT := criticalTemperature_pos kB hbarOmegaD c hkB hω hc'
    simp only [Function.comp_apply, Pi.div_apply]
    rw [Lcoef_eq kB hbarOmegaD c hkB hω hc']
    field_simp
    ring

end BCSAux
end Dev_NearTc2

open Filter Topology BCSTheory

theorem solution (kB hbarOmegaD : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) :
    ∃ L : ℝ → ℝ,
      (∀ coupling : ℝ, 0 < coupling →
        Tendsto (fun T : ℝ => gap kB hbarOmegaD coupling T ^ 2 /
            (1 - T / criticalTemperature kB hbarOmegaD coupling))
          (𝓝[<] (criticalTemperature kB hbarOmegaD coupling)) (𝓝 (L coupling))) ∧
      Tendsto (fun coupling : ℝ => L coupling / zeroTemperatureGap hbarOmegaD coupling ^ 2)
        (𝓝[>] 0)
        (𝓝 (8 * Real.exp (2 * Real.eulerMascheroniConstant) / (7 * (riemannZeta 3).re))) :=
  BCSAux.gap_near_Tc_weak_coupling' kB hbarOmegaD hkB hω
