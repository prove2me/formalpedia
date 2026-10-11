-- Prove2me | solution 1 for BCSTheory.criticalTemperature_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-11T07:00:39.113358+00:00
-- url     : https://prove2.me/submissions/ad7503be-6cf4-4512-bee2-3e07677c580d

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

open Filter Topology BCSTheory

theorem solution (kB hbarOmegaD coupling : ℝ) (hkB : 0 < kB)
    (hω : 0 < hbarOmegaD) (hc : 0 < coupling) :
    ∃! T : ℝ, 0 < T ∧ gapIntegral kB hbarOmegaD 0 T = 1 / coupling :=
  BCSAux.criticalTemperature_existsUnique' kB hbarOmegaD coupling hkB hω hc
