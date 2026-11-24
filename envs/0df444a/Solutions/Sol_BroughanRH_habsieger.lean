-- Prove2me | solution 1 for BroughanRH.habsieger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:09:54.94151+00:00
-- url     : https://prove2.me/submissions/6c588d7e-f91c-4620-a914-6c6525c80196
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_FourierSeries_tendsto_symmetric_partial_sums_of_piecewise_C1
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneSincSquaredIntegralValue
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEqualsSincSquare
import Theorems.Thm_NymanBeurling_damped_spectral_vanishing_of_ratio_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_NymanAux_moebiusPolynomialBoundaryBound_of_riemannHypothesis
import Theorems.Thm_NymanAux_shiftedZetaRatioBound_of_riemannHypothesis

section BagchiPart
open MeasureTheory
open scoped BigOperators

theorem bagchiConst_of_bounds (hA : NymanBeurling.MoebiusPolynomialBoundaryBound)
    (hB : NymanBeurling.ShiftedZetaRatioBound) :
    let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
      ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
        ((n : ℝ)*(n+1))
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
      Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
      (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε := by
  intro err ε hε
  obtain ⟨e₀, he₀, he₀h, hvan⟩ :=
    NymanBeurling.damped_spectral_vanishing_of_ratio_bound hB (ε / 8) (by linarith)
  set e : ℝ := e₀ / 2 with he
  have he0 : 0 < e := by positivity
  have hee : e < e₀ := by linarith
  have heh : e < 1/2 := by linarith
  obtain ⟨hint, hsmall⟩ := hvan e he0 hee
  obtain ⟨hcompl, hprof⟩ := NymanBeurling.damped_mellin_completion_of_polynomial_bound hA
  obtain ⟨N₀, hN₀⟩ := hcompl e he0 heh (ε / 8) (by linarith)
  obtain ⟨hsum, -, hpl⟩ := hprof e he0 heh
  set P := fun n : ℕ => (NymanBeurling.dampedResidualProfile e (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ)) with hP
  have hPt : (∑' n, P n) < ε / 8 := by
    have h2 : (2 * Real.pi) * (∑' n, P n) < ε / 8 := by rw [← hpl]; exact hsmall
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hP0 : 0 ≤ ∑' n, P n := tsum_nonneg (fun n => by positivity)
    nlinarith
  refine ⟨N₀ + 1, fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ), ?_⟩
  -- identify the error terms
  have key : ∀ m : ℕ, err (fun _ => 1) (N₀+1) (fun j => if j.val = 0 then 0 else
      -(((ArithmeticFunction.moebius (j.val+1) : ℝ) / ((j.val+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) (m+1) =
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) := by
    intro m
    simp only [err]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, if_pos, zero_mul, zero_add, Fin.val_succ]
    have : ∀ i : Fin N₀, (if (i.val + 1 = 0) then (0:ℂ) else
        -(((ArithmeticFunction.moebius (i.val+1+1) : ℝ) / ((i.val+1+1 : ℕ) : ℝ)^e : ℝ) : ℂ)) *
        ((Int.fract (((m+1 : ℕ) : ℝ)/(i.val+1+1 : ℕ)) : ℝ) : ℂ) =
        -((((ArithmeticFunction.moebius (i.val+2) : ℝ) / (i.val+2 : ℝ)^e) *
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) : ℝ) : ℂ) := by
      intro i
      rw [if_neg (by omega)]
      have h1 : (Int.fract (((m+1 : ℕ) : ℝ)/((i.val+1+1 : ℕ) : ℝ))) =
          (((m+1) % (i.val+2) : ℕ) : ℝ) / (i.val+2 : ℝ) := by
        rw [Int.fract_div_natCast_eq_div_natCast_mod]; push_cast; ring_nf
      rw [h1]; push_cast; ring_nf
    have hc : ((m+1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [show ((↑(m+1) : ℝ)) = ((m+1 : ℕ) : ℝ) from rfl] at *
    simp_rw [this]
    rw [Finset.sum_neg_distrib, sub_neg_eq_add]
    unfold NymanBeurling.dampedResidualFinite
    rw [show ((m+1 : ℕ) : ℝ) * (((m+1 : ℕ) : ℝ) + 1) = ((m+1 : ℝ)*(m+2 : ℝ)) by push_cast; ring]
    congr 1
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hle : ∀ H : ℕ, ∑ m ∈ Finset.range H,
      (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ)) ≤ ε / 2 := by
    intro H
    have hw : ∀ m : ℕ, 0 < ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
    have h1 := hN₀ N₀ le_rfl H
    have h2 : ∑ m ∈ Finset.range H, P m ≤ ∑' n, P n :=
      hsum.sum_le_tsum _ (fun n _ => by positivity)
    calc ∑ m ∈ Finset.range H,
          (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))
        ≤ ∑ m ∈ Finset.range H, (2 * ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) + 2 * P m) := by
          apply Finset.sum_le_sum; intro m _
          rw [hP]; dsimp only
          rw [mul_div_assoc', mul_div_assoc', ← add_div]
          apply div_le_div_of_nonneg_right _ (hw m).le
          nlinarith [sq_nonneg (NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            2 * NymanBeurling.dampedResidualProfile e (m+1))]
      _ = 2 * ∑ m ∈ Finset.range H, ((NymanBeurling.dampedResidualFinite N₀ e (m+1) -
            NymanBeurling.dampedResidualProfile e (m+1))^2 / ((m+1 : ℝ)*(m+2 : ℝ))) +
            2 * ∑ m ∈ Finset.range H, P m := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ε / 2 := by linarith
  have hnn : ∀ m : ℕ, 0 ≤ (NymanBeurling.dampedResidualFinite N₀ e (m+1))^2 /
      ((m+1 : ℝ)*(m+2 : ℝ)) := fun m => by positivity
  simp_rw [key]
  refine ⟨summable_of_sum_range_le hnn hle, ?_⟩
  have := Real.tsum_le_of_sum_range_le hnn hle
  linarith


end BagchiPart

section SawPart

open Filter Topology Set MeasureTheory
open scoped Real

namespace MellinSaw

noncomputable def sf (t : ℝ) : ℂ := ((Int.fract t - 1/2 : ℝ) : ℂ)

lemma floor_of_mem_left {x t : ℝ} (ht : t ∈ Ioo ((⌈x⌉ : ℝ) - 1) x) : ⌊t⌋ = ⌈x⌉ - 1 := by
  rw [Int.floor_eq_iff]; push_cast
  refine ⟨ht.1.le, ?_⟩
  have := Int.le_ceil x; linarith [ht.2]

lemma floor_of_mem_right {x t : ℝ} (ht : t ∈ Ioo x ((⌊x⌋ : ℝ) + 1)) : ⌊t⌋ = ⌊x⌋ := by
  rw [Int.floor_eq_iff]
  refine ⟨?_, ht.2⟩
  have := Int.floor_le x; linarith [ht.1]

lemma left_mem (x : ℝ) : Ioo ((⌈x⌉ : ℝ) - 1) x ∈ 𝓝[<] x := by
  apply Ioo_mem_nhdsLT
  have := Int.ceil_lt_add_one x; linarith

lemma right_mem (x : ℝ) : Ioo x ((⌊x⌋ : ℝ) + 1) ∈ 𝓝[>] x := by
  apply Ioo_mem_nhdsGT
  exact Int.lt_floor_add_one x

lemma notint_eventually (x : ℝ) : ∀ᶠ t : ℝ in 𝓝[≠] x, ∀ n : ℤ, t ≠ (n : ℝ) := by
  have hmem : Ioo ((⌈x⌉ : ℝ) - 1) ((⌊x⌋ : ℝ) + 1) ∈ 𝓝 x := by
    apply Ioo_mem_nhds
    · have := Int.ceil_lt_add_one x; linarith
    · exact Int.lt_floor_add_one x
  have := nhdsWithin_le_nhds (s := {x}ᶜ) hmem
  filter_upwards [this, self_mem_nhdsWithin] with t ht htx n hn
  subst hn
  have h1 : (⌈x⌉ : ℤ) - 1 < n := by exact_mod_cast ht.1
  have h2 : n < ⌊x⌋ + 1 := by exact_mod_cast ht.2
  have h3 : x ≤ (n : ℝ) := by
    have : ⌈x⌉ ≤ n := by omega
    have h := Int.le_ceil x
    have : ((⌈x⌉ : ℤ) : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have h4 : (n : ℝ) ≤ x := by
    have : n ≤ ⌊x⌋ := by omega
    have h := Int.floor_le x
    have : (n : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  exact htx (le_antisymm h4 h3)

lemma eq_affine_near {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) :
    sf =ᶠ[𝓝 x] fun t => (((t - ⌊x⌋ - 1/2 : ℝ)) : ℂ) := by
  have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun h => hx _ h.symm)
  have hmem : Ioo (⌊x⌋ : ℝ) ((⌊x⌋ : ℝ) + 1) ∈ 𝓝 x := Ioo_mem_nhds hlt (Int.lt_floor_add_one x)
  filter_upwards [hmem] with t ht
  have : ⌊t⌋ = ⌊x⌋ := by
    rw [Int.floor_eq_iff]; exact ⟨ht.1.le, ht.2⟩
  simp only [sf, Int.fract, this]

lemma hasDerivAt_sf {x : ℝ} (hx : ∀ n : ℤ, x ≠ n) : HasDerivAt sf 1 x := by
  have h : HasDerivAt (fun t : ℝ => (((t - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) 1 x := by
    have := ((hasDerivAt_id x).sub_const ((⌊x⌋ : ℝ) + 1/2)).ofReal_comp
    simp only [id, Complex.ofReal_one] at this
    convert this using 2
    push_cast; ring
  exact h.congr_of_eventuallyEq (eq_affine_near hx)

lemma deriv_sf_eventually (x : ℝ) : ∀ᶠ t in 𝓝[≠] x, deriv sf t = 1 := by
  filter_upwards [notint_eventually x] with t ht
  exact (hasDerivAt_sf ht).deriv

lemma tendsto_left (x : ℝ) :
    Tendsto sf (𝓝[<] x) (𝓝 (((x - (⌈x⌉ - 1) - 1/2 : ℝ)) : ℂ)) := by
  have hc : Tendsto (fun t : ℝ => (((t - (⌈x⌉ - 1) - 1/2 : ℝ)) : ℂ)) (𝓝[<] x)
      (𝓝 (((x - (⌈x⌉ - 1) - 1/2 : ℝ)) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Continuous.tendsto
    fun_prop
  apply hc.congr'
  filter_upwards [left_mem x] with t ht
  simp only [sf, Int.fract, floor_of_mem_left ht]
  push_cast; ring_nf

lemma tendsto_right (x : ℝ) :
    Tendsto sf (𝓝[>] x) (𝓝 (((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) := by
  have hc : Tendsto (fun t : ℝ => (((t - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) (𝓝[>] x)
      (𝓝 (((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Continuous.tendsto
    fun_prop
  apply hc.congr'
  filter_upwards [right_mem x] with t ht
  simp only [sf, Int.fract, floor_of_mem_right ht]

lemma coeff_eq (n : ℤ) :
    (((1 / (1:ℝ) : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..1, sf t * Complex.exp (-(2 * π * Complex.I * n * t / 1))) =
      if n = 0 then 0 else -1 / (2 * π * Complex.I * n) := by
  have hcongr : ∫ t in (0 : ℝ)..1, sf t * Complex.exp (-(2 * π * Complex.I * n * t / 1)) =
      ∫ t in (0 : ℝ)..1, (((t - 1/2 : ℝ)) : ℂ) * Complex.exp (-(2 * π * Complex.I * n * t)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩
    simp only [sf, this, div_one]
  rw [hcongr]
  simp only [div_one, Complex.ofReal_one, one_mul]
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_eq_zero]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const]
    simp
  · set c : ℂ := 2 * π * Complex.I * n with hc
    have hc0 : c ≠ 0 := by
      simp [hc, Complex.I_ne_zero, Real.pi_ne_zero, hn]
    have hexp : Complex.exp (-c) = 1 := by
      rw [hc, show -(2 * (π:ℂ) * Complex.I * (n:ℂ)) = ((-n : ℤ) : ℂ) * (2 * π * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-n)
    let F : ℝ → ℂ := fun t => Complex.exp (-(c * t)) * (-(((t - 1/2 : ℝ)) : ℂ) / c - 1 / c ^ 2)
    have hF : ∀ t : ℝ, HasDerivAt F ((((t - 1/2 : ℝ)) : ℂ) * Complex.exp (-(c * t))) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
        have := ((hasDerivAt_id (t : ℂ)).const_mul c).neg.cexp
        have h2 := this.comp_ofReal (z := t)
        simpa using h2
      have h3 : HasDerivAt (fun t : ℝ => (-(((t - 1/2 : ℝ)) : ℂ) / c - 1 / c ^ 2)) (-1 / c) t := by
        have := (((hasDerivAt_id t).sub_const (1/2 : ℝ)).ofReal_comp).neg.div_const c
        have := this.sub_const (1 / c ^ 2)
        simpa using this
      refine (h1.mul h3).congr_deriv ?_
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)]
    · simp only [F, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.exp_zero, one_mul, hexp]
      field_simp
      push_cast
      ring
    · apply Continuous.intervalIntegrable
      fun_prop

lemma sym_sum (φ : ℤ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ n =
      φ 0 + ∑ m ∈ Finset.Icc 1 N, (φ m + φ (-m)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N+1 : ℕ) : ℤ)) ((N+1 : ℕ) : ℤ) =
        insert (((N+1 : ℕ) : ℤ)) (insert (-((N+1 : ℕ) : ℤ)) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext z; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hset, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_Icc_succ_top (by omega)]
    · push_cast; ring
    · simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; omega

lemma pair_eq (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (-1 / (2 * π * Complex.I * (m : ℤ))) * Complex.exp (2 * π * Complex.I * (m : ℤ) * x / 1) +
      (-1 / (2 * π * Complex.I * ((-(m:ℤ) : ℤ) : ℂ))) *
        Complex.exp (2 * π * Complex.I * ((-(m:ℤ) : ℤ) : ℂ) * x / 1) =
      -((Real.sin (2 * π * m * x) / m : ℝ) : ℂ) / π := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [Complex.sin]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

theorem sin_sum_tendsto (x : ℝ) (hx : ∀ n : ℤ, x ≠ n) :
    Tendsto (fun M : ℕ => ∑ m ∈ Finset.Icc 1 M, Real.sin (2 * π * m * x) / m) atTop
      (𝓝 (π * (1/2 - Int.fract x))) := by
  have hper : Function.Periodic sf 1 := by
    intro t; simp [sf, Int.fract_add_one]
  have hC1 : ∀ y : ℝ, (∀ n : ℤ, y + n * 1 ∉ ({0} : Finset ℝ)) →
      DifferentiableAt ℝ sf y ∧ ContinuousAt (deriv sf) y := by
    intro y hy
    have hy' : ∀ n : ℤ, y ≠ n := by
      intro n h; apply hy (-n); simp [h]
    refine ⟨(hasDerivAt_sf hy').differentiableAt, ?_⟩
    have hev : ∀ᶠ t in 𝓝 y, deriv sf t = 1 := by
      have := deriv_sf_eventually y
      rw [eventually_nhdsWithin_iff] at this
      filter_upwards [this] with t ht
      by_cases h : t = y
      · subst h; exact (hasDerivAt_sf hy').deriv
      · exact ht h
    exact (continuousAt_const (y := (1:ℂ))).congr (by
      filter_upwards [hev] with t ht; exact ht.symm)
  have hlim : ∀ y : ℝ, ∃ l r : ℂ, Tendsto sf (𝓝[<] y) (𝓝 l) ∧ Tendsto sf (𝓝[>] y) (𝓝 r) :=
    fun y => ⟨_, _, tendsto_left y, tendsto_right y⟩
  have hlim' : ∀ y : ℝ, ∃ l r : ℂ,
      Tendsto (deriv sf) (𝓝[<] y) (𝓝 l) ∧ Tendsto (deriv sf) (𝓝[>] y) (𝓝 r) := by
    intro y
    refine ⟨1, 1, ?_, ?_⟩
    · apply tendsto_const_nhds.congr'
      have := deriv_sf_eventually y
      have h2 : 𝓝[<] y ≤ 𝓝[≠] y := nhdsWithin_mono _ (fun t ht => ne_of_lt ht)
      filter_upwards [h2 this] with t ht; exact ht.symm
    · apply tendsto_const_nhds.congr'
      have := deriv_sf_eventually y
      have h2 : 𝓝[>] y ≤ 𝓝[≠] y := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
      filter_upwards [h2 this] with t ht; exact ht.symm
  have hceil : (⌈x⌉ : ℝ) - 1 = ⌊x⌋ := by
    have : ⌈x⌉ = ⌊x⌋ + 1 := by
      rw [Int.ceil_eq_iff]; push_cast
      refine ⟨?_, (Int.lt_floor_add_one x).le⟩
      have := lt_of_le_of_ne (Int.floor_le x) (fun h => hx _ h.symm); linarith
    rw [this]; push_cast; ring
  have hl := tendsto_left x
  rw [hceil] at hl
  have hmain := FourierSeries.tendsto_symmetric_partial_sums_of_piecewise_C1 1 one_pos sf hper
    {0} hC1 hlim hlim' x _ _ hl (tendsto_right x)
  have heq : ∀ N : ℕ, (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (if n = 0 then (0:ℂ) else -1 / (2 * π * Complex.I * n)) *
        Complex.exp (2 * π * Complex.I * n * x / 1)) =
      -(((∑ m ∈ Finset.Icc 1 N, Real.sin (2 * π * m * x) / m : ℝ)) : ℂ) / π := by
    intro N
    rw [sym_sum]
    rw [if_pos rfl, zero_mul, zero_add]
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [if_neg (by omega), if_neg (by omega)]
    convert pair_eq x m hm1 using 3 <;> push_cast <;> ring
  replace hmain : Tendsto (fun N : ℕ =>
      -(((∑ m ∈ Finset.Icc 1 N, Real.sin (2 * π * m * x) / m : ℝ)) : ℂ) / π) atTop
      (𝓝 (((((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ) + (((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) / 2)) := by
    refine hmain.congr (fun N => ?_)
    rw [← heq N]
    apply Finset.sum_congr rfl
    intro n _
    exact congrArg (· * _) (coeff_eq n)
  have hcont : Continuous (fun z : ℂ => -(π * z).re) := by fun_prop
  have := (hcont.tendsto _).comp hmain
  have hpi : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : -((π:ℂ) * (((((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ) + (((x - ⌊x⌋ - 1/2 : ℝ)) : ℂ)) / 2)).re =
      π * (1/2 - Int.fract x) := by
    rw [Complex.mul_re, Int.fract]; simp; ring
  rw [hval] at this
  refine this.congr (fun N => ?_)
  simp only [Function.comp]
  rw [mul_div_assoc', mul_neg, neg_div, mul_div_cancel_left₀ _ hpi]
  simp only [Complex.neg_re, neg_neg, Complex.ofReal_re]
end MellinSaw

end SawPart

section KernPart

open MeasureTheory Set Real

namespace MellinKern

lemma base : IntegrableOn (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), (1 - Real.cos x) / x ^ 2 = π / 2 := by
  have hv : ∫ x in Ioi (0:ℝ), (1 - Real.cos x) / x ^ 2 = π / 2 := by
    rw [Kyprianou.Ch01.stableAlphaOneCosineEqualsSincSquare,
      Kyprianou.Ch01.stableAlphaOneSincSquaredIntegralValue]
  refine ⟨?_, hv⟩
  by_contra h
  rw [integral_undef h] at hv
  linarith [Real.pi_pos]

lemma one_sub_cos_pos (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (c * x)) / x ^ 2) (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), (1 - Real.cos (c * x)) / x ^ 2 = c * π / 2 := by
  set g : ℝ → ℝ := fun x => (1 - Real.cos x) / x ^ 2 with hg
  have hfeq : (fun x : ℝ => (1 - Real.cos (c * x)) / x ^ 2) = fun x => c ^ 2 * g (c * x) := by
    funext x
    by_cases hx : x = 0
    · subst hx; simp [hg]
    · simp only [hg]; field_simp
  rw [hfeq]
  have hi : IntegrableOn (fun x => g (c * x)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff g 0 hc, mul_zero]; exact base.1
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_mul_left_Ioi g 0 hc, mul_zero, smul_eq_mul, base.2]
  field_simp

lemma one_sub_cos (c : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (c * x)) / x ^ 2) (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), (1 - Real.cos (c * x)) / x ^ 2 = |c| * π / 2 := by
  rcases lt_trichotomy c 0 with h | h | h
  · have := one_sub_cos_pos (-c) (by linarith)
    simp only [neg_mul, Real.cos_neg] at this
    rw [abs_of_neg h]; refine ⟨this.1, ?_⟩; rw [this.2]; ring
  · subst h; simp
  · rw [abs_of_pos h]; exact one_sub_cos_pos c h

lemma sin_mul_sin (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.sin (a * x) * Real.sin (b * x) / x ^ 2) (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), Real.sin (a * x) * Real.sin (b * x) / x ^ 2 = min a b * π / 2 := by
  have heq : (fun x : ℝ => Real.sin (a * x) * Real.sin (b * x) / x ^ 2) =
      fun x => (1/2 : ℝ) * ((1 - Real.cos ((a + b) * x)) / x ^ 2 -
        (1 - Real.cos ((a - b) * x)) / x ^ 2) := by
    funext x
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  rw [heq]
  obtain ⟨i1, v1⟩ := one_sub_cos (a + b)
  obtain ⟨i2, v2⟩ := one_sub_cos (a - b)
  refine ⟨(i1.sub i2).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i1 i2, v1, v2, abs_of_pos (by linarith)]
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

theorem trig_quad (h : ℕ → ℝ) (N : ℕ) :
    IntegrableOn (fun x : ℝ => (∑ n ∈ Finset.Icc 1 N, h n * Real.sin (2 * π * n * x)) ^ 2 / x ^ 2)
      (Ioi 0) ∧
    ∫ x in Ioi (0:ℝ), (∑ n ∈ Finset.Icc 1 N, h n * Real.sin (2 * π * n * x)) ^ 2 / x ^ 2 =
      π ^ 2 * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, h m * h n * (min m n : ℕ) := by
  have heq : (fun x : ℝ => (∑ n ∈ Finset.Icc 1 N, h n * Real.sin (2 * π * n * x)) ^ 2 / x ^ 2) =
      fun x => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, h m * h n *
        (Real.sin ((2 * π * m) * x) * Real.sin ((2 * π * n) * x) / x ^ 2) := by
    funext x
    rw [sq, Finset.sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro n _
    ring
  have hterm : ∀ m ∈ Finset.Icc 1 N, ∀ n ∈ Finset.Icc 1 N,
      IntegrableOn (fun x : ℝ => h m * h n *
        (Real.sin ((2 * π * m) * x) * Real.sin ((2 * π * n) * x) / x ^ 2)) (Ioi 0) ∧
      ∫ x in Ioi (0:ℝ), h m * h n *
        (Real.sin ((2 * π * m) * x) * Real.sin ((2 * π * n) * x) / x ^ 2) =
        π ^ 2 * (h m * h n * (min m n : ℕ)) := by
    intro m hm n hn
    have hm1 : (0:ℝ) < m := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast this
    have hn1 : (0:ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1; exact_mod_cast this
    obtain ⟨i, v⟩ := sin_mul_sin (2 * π * m) (2 * π * n) (by positivity) (by positivity)
    refine ⟨i.const_mul _, ?_⟩
    rw [integral_const_mul, v]
    have : min (2 * π * m) (2 * π * n) = 2 * π * ((min m n : ℕ) : ℝ) := by
      rw [Nat.cast_min, mul_min_of_nonneg _ _ (by positivity)]
    rw [this]; ring
  rw [heq]
  refine ⟨?_, ?_⟩
  · apply integrable_finsetSum _ (fun m hm => ?_)
    apply integrable_finsetSum _ (fun n hn => (hterm m hm n hn).1)
  · rw [integral_finsetSum _ (fun m hm => integrable_finsetSum _ (fun n hn => (hterm m hm n hn).1)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [integral_finsetSum _ (fun n hn => (hterm m hm n hn).1), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n hn
    exact (hterm m hm n hn).2

end MellinKern

end KernPart

namespace MellinHabs

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

/-- quadratic form identity -/
theorem quad_identity (h : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, h m * h n * ((min m n : ℕ) : ℝ) =
      ∑ n ∈ Finset.Ico 1 N, (∑ m ∈ Finset.Icc 1 n, h m * m) ^ 2 / ((n:ℝ) * (n + 1)) +
        (∑ m ∈ Finset.Icc 1 N, h m * m) ^ 2 / N := by
  induction N, hN using Nat.le_induction with
  | base => simp; ring
  | succ N hN ih =>
    set P := ∑ m ∈ Finset.Icc 1 N, h m * m with hP
    have hrow : ∀ m ∈ Finset.Icc 1 (N+1), ∑ n ∈ Finset.Icc 1 (N+1), h m * h n * ((min m n : ℕ) : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, h m * h n * ((min m n : ℕ) : ℝ) + h m * h (N+1) * m := by
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      rw [Finset.sum_Icc_succ_top (by omega), min_eq_left hm'.2]
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
    have hA : ∑ m ∈ Finset.Icc 1 (N+1), ∑ n ∈ Finset.Icc 1 N, h m * h n * ((min m n : ℕ) : ℝ) =
        ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, h m * h n * ((min m n : ℕ) : ℝ) +
        ∑ n ∈ Finset.Icc 1 N, h (N+1) * h n * ((min (N+1) n : ℕ) : ℝ) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hcol : ∑ n ∈ Finset.Icc 1 N, h (N+1) * h n * ((min (N+1) n : ℕ) : ℝ) = h (N+1) * P := by
      rw [hP, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      rw [min_eq_right (by omega)]; ring
    have hB : ∑ m ∈ Finset.Icc 1 (N+1), h m * h (N+1) * (m : ℝ) =
        h (N+1) * P + h (N+1)^2 * ((N:ℝ)+1) := by
      rw [Finset.sum_Icc_succ_top (by omega), hP, Finset.mul_sum]
      push_cast
      congr 1
      · apply Finset.sum_congr rfl; intro m _; ring
      · ring
    have hC : ∑ n ∈ Finset.Ico 1 (N+1), (∑ m ∈ Finset.Icc 1 n, h m * m) ^ 2 / ((n:ℝ) * (n + 1)) =
        ∑ n ∈ Finset.Ico 1 N, (∑ m ∈ Finset.Icc 1 n, h m * m) ^ 2 / ((n:ℝ) * (n + 1)) +
          P ^ 2 / ((N:ℝ) * (N + 1)) := by
      rw [Finset.sum_Ico_succ_top hN]
    have hD : ∑ m ∈ Finset.Icc 1 (N+1), h m * (m:ℝ) = P + h (N+1) * ((N:ℝ)+1) := by
      rw [Finset.sum_Icc_succ_top (by omega), hP]; push_cast; ring
    rw [hA, hB, hC, hD, ih, hcol]
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    push_cast
    field_simp
    ring

lemma sum_dvd_ind (k M : ℕ) : (∑ m ∈ Finset.Icc 1 M, (if k ∣ m then (1:ℝ) else 0)) = ((M / k : ℕ) : ℝ) := by
  rw [Finset.sum_boole]
  have : Finset.Icc 1 M = Finset.Ioc 0 M := by ext x; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma sum_dvd_regroup (k M : ℕ) (hk : 0 < k) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M, (if k ∣ n then f n else 0)) = ∑ m ∈ Finset.Icc 1 (M / k), f (k * m) := by
  rw [← Finset.sum_filter]
  have himg : (Finset.Icc 1 M).filter (fun n => k ∣ n) = (Finset.Icc 1 (M / k)).image (fun m => k * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at h1
        · exact h
      · rw [Nat.le_div_iff_mul_le hk]; linarith [mul_comm k m]
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right k m⟩
      · exact Nat.mul_pos hk h1 |>.le |> le_trans (le_refl _) |> fun _ => Nat.one_le_iff_ne_zero.mpr (by positivity)
      · rw [Nat.le_div_iff_mul_le hk] at h2; linarith [mul_comm k m]
  rw [himg, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hk hab

lemma nat_div_tendsto (k : ℕ) (hk : 0 < k) : Tendsto (fun M : ℕ => M / k) atTop atTop :=
  tendsto_atTop_atTop.mpr (fun b => ⟨b * k, fun a ha => (Nat.le_div_iff_mul_le hk).mpr ha⟩)


noncomputable def hcoef {K : ℕ} (b : Fin K → ℝ) (n : ℕ) : ℝ :=
  ((if n = 1 then (1:ℝ) else 0) + ∑ j : Fin K, (if (j.val+1) ∣ n then b j else 0)) / n

noncomputable def Rres {K : ℕ} (b : Fin K → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ j : Fin K, b j * Int.fract ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))

lemma partial_eq {K : ℕ} (b : Fin K → ℝ) (hcon : ∑ j, b j / ((j.val+1:ℕ):ℝ) = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n, hcoef b m * m = Rres b n := by
  have h1 : ∀ m ∈ Finset.Icc 1 n, hcoef b m * m =
      (if m = 1 then (1:ℝ) else 0) + ∑ j : Fin K, (if (j.val+1) ∣ m then b j else 0) := by
    intro m hm
    have hm1 : (m:ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hm).1
      exact_mod_cast (show m ≠ 0 by omega)
    unfold hcoef; field_simp
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_comm]
  have hone : ∑ m ∈ Finset.Icc 1 n, (if m = 1 then (1:ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq']; rw [if_pos (Finset.mem_Icc.mpr ⟨le_refl _, hn⟩)]
  have hj : ∀ j : Fin K, ∑ m ∈ Finset.Icc 1 n, (if (j.val+1) ∣ m then b j else 0) =
      b j * ((n / (j.val+1) : ℕ) : ℝ) := by
    intro j
    rw [← sum_dvd_ind, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _; split_ifs <;> simp
  rw [hone, Finset.sum_congr rfl (fun j _ => hj j)]
  unfold Rres
  have hfr : ∀ j : Fin K, Int.fract ((n:ℝ) / ((j.val+1:ℕ):ℝ)) =
      (n:ℝ) / ((j.val+1:ℕ):ℝ) - ((n / (j.val+1) : ℕ) : ℝ) := by
    intro j
    rw [Int.fract_div_natCast_eq_div_natCast_mod]
    have hk : ((j.val+1 : ℕ):ℝ) ≠ 0 := by positivity
    have hdm : (n:ℝ) = ((j.val+1:ℕ):ℝ) * ((n/(j.val+1) : ℕ):ℝ) + ((n % (j.val+1) : ℕ):ℝ) := by
      exact_mod_cast (Nat.div_add_mod n (j.val+1)).symm
    rw [hdm]; field_simp; ring
  simp_rw [hfr, mul_sub, Finset.sum_sub_distrib]
  have : ∑ j : Fin K, b j * ((n:ℝ) / ((j.val+1:ℕ):ℝ)) = n * ∑ j, b j / ((j.val+1:ℕ):ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [this, hcon]; ring

lemma Rres_bound {K : ℕ} (b : Fin K → ℝ) (n : ℕ) : |Rres b n| ≤ 1 + ∑ j, |b j| := by
  unfold Rres
  have h1 : |∑ j : Fin K, b j * Int.fract ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))| ≤ ∑ j, |b j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul]
    have h0 := Int.fract_nonneg ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))
    have h1 := Int.fract_lt_one ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))
    rw [abs_of_nonneg h0]
    nlinarith [abs_nonneg (b j)]
  calc |1 - ∑ j : Fin K, b j * Int.fract ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))|
      ≤ |(1:ℝ)| + |∑ j : Fin K, b j * Int.fract ((n:ℝ) / ((j.val+1 : ℕ) : ℝ))| := abs_sub _ _
    _ ≤ 1 + ∑ j, |b j| := by rw [abs_one]; linarith

lemma sum_regroup {K : ℕ} (b : Fin K → ℝ) (x : ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, hcoef b n * Real.sin (2*π*n*x) =
      Real.sin (2*π*x) + ∑ j : Fin K, b j / ((j.val+1:ℕ):ℝ) *
        ∑ m ∈ Finset.Icc 1 (M/(j.val+1)), Real.sin (2*π*m*(((j.val+1:ℕ):ℝ)*x)) / m := by
  unfold hcoef
  simp_rw [add_div, Finset.sum_div, add_mul, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro n _ hn; simp [hn]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_refl _, hM⟩) h
  · apply Finset.sum_congr rfl; intro j _
    have : ∀ n ∈ Finset.Icc 1 M, (if (j.val+1) ∣ n then b j else 0) / (n:ℝ) * Real.sin (2*π*n*x) =
        if (j.val+1) ∣ n then b j / n * Real.sin (2*π*n*x) else 0 := by
      intro n _; split_ifs <;> simp
    rw [Finset.sum_congr rfl this, sum_dvd_regroup _ _ (Nat.succ_pos _), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    push_cast
    have hk : ((j.val:ℝ) + 1) ≠ 0 := by positivity
    by_cases hm : (m:ℝ) = 0
    · simp [hm]
    · field_simp

lemma pointwise {K : ℕ} (b : Fin K → ℝ) (x : ℝ)
    (hx : ∀ j : Fin K, ∀ n : ℤ, ((j.val+1:ℕ):ℝ) * x ≠ n) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, hcoef b n * Real.sin (2*π*n*x)) atTop
      (𝓝 (Real.sin (2*π*x) + ∑ j : Fin K, b j / ((j.val+1:ℕ):ℝ) *
        (π * (1/2 - Int.fract (((j.val+1:ℕ):ℝ)*x))))) := by
  have hev : ∀ᶠ M : ℕ in atTop, Real.sin (2*π*x) + ∑ j : Fin K, b j / ((j.val+1:ℕ):ℝ) *
        ∑ m ∈ Finset.Icc 1 (M/(j.val+1)), Real.sin (2*π*m*(((j.val+1:ℕ):ℝ)*x)) / m =
      ∑ n ∈ Finset.Icc 1 M, hcoef b n * Real.sin (2*π*n*x) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact (sum_regroup b x M hM).symm
  refine Tendsto.congr' hev ?_
  refine tendsto_const_nhds.add (tendsto_finsetSum _ (fun j _ => ?_))
  refine Tendsto.const_mul _ ?_
  exact (MellinSaw.sin_sum_tendsto _ (hx j)).comp (nat_div_tendsto _ (Nat.succ_pos _))


theorem habs_of_real
    (hR : ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∃ b : Fin K → ℝ,
      (∑ j, b j / ((j.val+1:ℕ):ℝ) = 0) ∧
      Summable (fun m : ℕ => Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) ∧
      (∑' m : ℕ, Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) < δ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      let error (x : ℝ) := ((Real.sin (2*Real.pi*x)/Real.pi -
        ∑ j, a j * (Int.fract (((j.val+1 : ℕ):ℝ)*x) - Int.fract x))/x)^2
      MeasureTheory.IntegrableOn error (Set.Ioi 0) ∧
        (∫ x in Set.Ioi (0 : ℝ), error x) < ε := by
  intro ε hε
  obtain ⟨K, b, hcon, hsum, hlt⟩ := hR ε hε
  set S := ∑' m : ℕ, Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  set B := 1 + ∑ j, |b j| with hB
  refine ⟨K, fun j => b j / ((j.val+1 : ℕ):ℝ), ?_⟩
  intro error
  set Q : ℕ → ℝ := fun M => ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
    hcoef b m * hcoef b n * ((min m n : ℕ) : ℝ) with hQ
  set F : ℕ → ℝ → ℝ := fun M x =>
    (∑ n ∈ Finset.Icc 1 M, hcoef b n * Real.sin (2 * π * n * x)) ^ 2 / x ^ 2 / π ^ 2 with hF
  -- integral of F
  have hFint : ∀ M, ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (F M x) = ENNReal.ofReal (Q M) := by
    intro M
    obtain ⟨hi, hv⟩ := MellinKern.trig_quad (hcoef b) M
    have hi' : IntegrableOn (F M) (Ioi 0) := hi.div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (fun x => by
      simp only [hF]; positivity))]
    congr 1
    simp only [hF]
    rw [integral_div, hv]
    have : (π:ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    rfl
  -- bound on Q
  have hQb : ∀ M, 1 ≤ M → Q M ≤ S + B ^ 2 / M := by
    intro M hM
    simp only [hQ]
    rw [quad_identity _ M hM]
    have hP : ∀ n, 1 ≤ n → ∑ m ∈ Finset.Icc 1 n, hcoef b m * m = Rres b n :=
      fun n hn => partial_eq b hcon n hn
    rw [hP M hM]
    have h1 : ∑ n ∈ Finset.Ico 1 M, (∑ m ∈ Finset.Icc 1 n, hcoef b m * m) ^ 2 / ((n:ℝ) * (n + 1)) ≤ S := by
      rw [Finset.sum_Ico_eq_sum_range]
      have : ∀ k ∈ Finset.range (M - 1),
          (∑ m ∈ Finset.Icc 1 (1 + k), hcoef b m * m) ^ 2 / (((1 + k : ℕ):ℝ) * ((1 + k : ℕ) + 1)) =
          Rres b (k+1) ^ 2 / (((k:ℝ)+1) * ((k:ℝ)+2)) := by
        intro k _
        rw [hP (1+k) (by omega), add_comm 1 k]; push_cast; ring_nf
      rw [Finset.sum_congr rfl this]
      exact hsum.sum_le_tsum _ (fun m _ => by positivity)
    have h2 : Rres b M ^ 2 / M ≤ B ^ 2 / M := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := Rres_bound b M
      have h0 : 0 ≤ |Rres b M| := abs_nonneg _
      calc Rres b M ^ 2 = |Rres b M| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := by gcongr
    linarith
  -- pointwise limit a.e.
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))),
      Tendsto (fun M => F M x) atTop (𝓝 (error x)) := by
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ), ∀ j : Fin K, ∀ n : ℤ, ((j.val+1:ℕ):ℝ) * x ≠ n := by
      rw [ae_all_iff]; intro j
      rw [ae_all_iff]; intro n
      have : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ ({(n:ℝ) / ((j.val+1:ℕ):ℝ)} : Set ℝ)ᶜ :=
        compl_mem_ae_iff.mpr (measure_singleton _)
      filter_upwards [this] with x hx heq
      apply hx
      simp only [mem_singleton_iff]
      have hk : ((j.val+1:ℕ):ℝ) ≠ 0 := by positivity
      rw [← heq]; field_simp
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hlim := pointwise b x hx
    have hc : Continuous (fun s : ℝ => s ^ 2 / x ^ 2 / π ^ 2) := by fun_prop
    have := (hc.tendsto _).comp hlim
    convert this using 1
    · rfl
    congr 1
    simp only [error]
    have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
    have hA : ∑ j : Fin K, b j / ((j.val+1 : ℕ):ℝ) *
          (Int.fract (((j.val+1 : ℕ):ℝ)*x) - Int.fract x) =
        ∑ j : Fin K, b j / ((j.val+1 : ℕ):ℝ) * Int.fract (((j.val+1 : ℕ):ℝ)*x) -
          (∑ j : Fin K, b j / ((j.val+1 : ℕ):ℝ)) * Int.fract x := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    have hB2 : ∑ j : Fin K, b j / ((j.val+1:ℕ):ℝ) * (π * (1/2 - Int.fract (((j.val+1:ℕ):ℝ)*x))) =
        π / 2 * (∑ j : Fin K, b j / ((j.val+1 : ℕ):ℝ)) -
          π * ∑ j : Fin K, b j / ((j.val+1 : ℕ):ℝ) * Int.fract (((j.val+1 : ℕ):ℝ)*x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    try simp only [Function.comp]
    rw [hA, hB2, hcon]
    field_simp
    ring
  -- Fatou
  have hmeas : ∀ M, AEMeasurable (fun x => ENNReal.ofReal (F M x)) (volume.restrict (Ioi (0:ℝ))) := by
    intro M
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    simp only [hF]
    fun_prop
  have hfatou := lintegral_liminf_le' (u := atTop) hmeas
  have hliminf_ae : ∀ᵐ x ∂(volume.restrict (Ioi (0:ℝ))),
      liminf (fun M => ENNReal.ofReal (F M x)) atTop = ENNReal.ofReal (error x) := by
    filter_upwards [hae] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
  rw [lintegral_congr_ae hliminf_ae] at hfatou
  simp_rw [hFint] at hfatou
  have hlimQ : liminf (fun M => ENNReal.ofReal (Q M)) atTop ≤ ENNReal.ofReal S := by
    have hT : Tendsto (fun M : ℕ => ENNReal.ofReal (S + B ^ 2 / M)) atTop (𝓝 (ENNReal.ofReal S)) := by
      apply (ENNReal.continuous_ofReal.tendsto _).comp
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (B ^ 2))
    calc liminf (fun M => ENNReal.ofReal (Q M)) atTop
        ≤ liminf (fun M : ℕ => ENNReal.ofReal (S + B ^ 2 / M)) atTop := by
          refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
          filter_upwards [eventually_ge_atTop 1] with M hM
          exact ENNReal.ofReal_le_ofReal (hQb M hM)
      _ = ENNReal.ofReal S := hT.liminf_eq
  have hlin : ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (error x) ≤ ENNReal.ofReal S :=
    hfatou.trans hlimQ
  have hnn : ∀ x, 0 ≤ error x := fun x => by simp only [error]; positivity
  have hmeasE : AEStronglyMeasurable error (volume.restrict (Ioi (0:ℝ))) := by
    apply Measurable.aestronglyMeasurable
    simp only [error]
    have hf : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
    fun_prop
  have hint : IntegrableOn error (Ioi 0) :=
    ⟨hmeasE, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).mpr
      (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeasE]
  exact lt_of_le_of_lt (ENNReal.toReal_le_of_le_ofReal hS0 hlin) hlt

end MellinHabs

namespace MellinHabs

theorem real_of_bagchi
    (hb : let err (f : ℕ → ℂ) (N : ℕ) (a : Fin N → ℂ) (n : ℕ) :=
                ‖f n - ∑ j, a j * ((Int.fract ((n : ℝ)/(j.val+1 : ℕ)) : ℝ) : ℂ)‖^2 /
                  ((n : ℝ)*(n+1))
              ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℂ,
                Summable (fun m : ℕ => err (fun _ => 1) N a (m+1)) ∧
                (∑' m : ℕ, err (fun _ => 1) N a (m+1)) < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∃ b : Fin K → ℝ,
      (∑ j, b j / ((j.val+1:ℕ):ℝ) = 0) ∧
      Summable (fun m : ℕ => Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) ∧
      (∑' m : ℕ, Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) < δ := by
  intro ε hε
  obtain ⟨N, a, hsum, hlt⟩ := hb ε hε
  set S : ℝ := ∑ i : Fin N, (if i.val = 0 then 0 else (a i).re / ((i.val + 1 : ℕ) : ℝ)) with hS
  set b : Fin N → ℝ := fun j => if j.val = 0 then -S else (a j).re with hbdef
  have hcon : ∑ j, b j / ((j.val + 1 : ℕ) : ℝ) = 0 := by
    have h1 : ∀ j : Fin N, b j / ((j.val + 1 : ℕ) : ℝ) =
        (if j.val = 0 then 0 else (a j).re / ((j.val + 1 : ℕ) : ℝ)) -
          (if j.val = 0 then S else 0) := by
      intro j
      by_cases hj : j.val = 0
      · simp [hbdef, hj]
      · simp [hbdef, hj]
    simp_rw [h1, Finset.sum_sub_distrib, ← hS]
    rcases N with _ | N
    · simp [hS]
    · rw [Fin.sum_univ_succ]; simp
  have hRle : ∀ m : ℕ, Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) ≤
      ‖(1:ℂ) - ∑ j, a j * ((Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) : ℝ) : ℂ)‖^2 /
        ((((m+1 : ℕ) : ℝ))*(((m+1 : ℕ) : ℝ)+1)) := by
    intro m
    have hden : (((m+1 : ℕ) : ℝ))*(((m+1 : ℕ) : ℝ)+1) = ((m:ℝ)+1) * ((m:ℝ)+2) := by
      push_cast; ring
    rw [hden]
    apply div_le_div_of_nonneg_right _ (by positivity)
    set z : ℂ := (1:ℂ) - ∑ j, a j * ((Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) : ℝ) : ℂ)
    have hzre : z.re = Rres b (m+1) := by
      simp only [z, Rres, Complex.sub_re, Complex.one_re, Complex.re_sum, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val = 0
      · have : Int.fract ((((m+1 : ℕ) : ℝ))/((j.val+1 : ℕ) : ℝ)) = 0 := by
          rw [hj]; simp
        rw [this]; simp
      · simp [hbdef, hj]
    rw [← hzre]
    have := Complex.re_sq_le_normSq z
    rw [Complex.normSq_eq_norm_sq] at this
    nlinarith
  have hnn : ∀ m : ℕ, 0 ≤ Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2)) := fun m => by positivity
  have hRsum : Summable (fun m : ℕ => Rres b (m+1) ^ 2 / (((m:ℝ)+1) * ((m:ℝ)+2))) :=
    Summable.of_nonneg_of_le hnn hRle hsum
  refine ⟨N, b, hcon, hRsum, ?_⟩
  exact lt_of_le_of_lt (hRsum.tsum_le_tsum hRle hsum) hlt

end MellinHabs

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : Fin N → ℝ,
      let error (x : ℝ) := ((Real.sin (2*Real.pi*x)/Real.pi -
        ∑ j, a j * (Int.fract (((j.val+1 : ℕ):ℝ)*x) - Int.fract x))/x)^2
      MeasureTheory.IntegrableOn error (Set.Ioi 0) ∧
        (∫ x in Set.Ioi (0 : ℝ), error x) < ε :=
  MellinHabs.habs_of_real (MellinHabs.real_of_bagchi (bagchiConst_of_bounds
    (NymanAux.moebiusPolynomialBoundaryBound_of_riemannHypothesis riemann_hypothesis)
    (NymanAux.shiftedZetaRatioBound_of_riemannHypothesis riemann_hypothesis)))
