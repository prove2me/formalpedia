-- Prove2me | solution 1 for BroughanRH.nicolasNormalizedLimsup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T05:21:19.034276+00:00
-- url     : https://prove2.me/submissions/e1c3c52b-863b-4365-adfa-4d88421d2a67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NicolasBRH_prime_ramp_bound_of_RH
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
import Mathlib

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Filter Topology

namespace NicL

noncomputable def Eser (u : ℝ) : ℝ :=
  ∑' k : ℕ, u^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))

noncomputable def li (y : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |Real.log y| + Eser (Real.log y)

lemma Eser_hasDerivAt (u : ℝ) :
    HasDerivAt Eser (∑' k : ℕ, u^k / ((k+1).factorial : ℝ)) u := by
  set R := |u| + 1
  have hsum : Summable (fun k : ℕ => R^k / (k.factorial : ℝ)) := Real.summable_pow_div_factorial R
  have hu : Summable (fun k : ℕ => R^k / ((k+1).factorial : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hR : 0 < R := by positivity
  refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0:ℝ) R) (y₀ := 0)
    (g := fun (k : ℕ) (y : ℝ) => y^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)))
    (g' := fun (k : ℕ) (y : ℝ) => y^k / ((k+1).factorial : ℝ)) hu
    Metric.isOpen_ball (convex_ball 0 R).isPreconnected ?_ ?_ (Metric.mem_ball_self hR) ?_ ?_
  · intro k y _
    have h := (hasDerivAt_pow (k+1) y).div_const ((((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ)))
    refine h.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    have : (((k+1:ℕ)):ℝ) ≠ 0 := by positivity
    have : (((k+1).factorial:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
  · intro k y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0:ℝ) < ((k+1).factorial : ℝ))]
    gcongr
    rw [Real.norm_eq_abs] at hy; exact hy.le
  · simp
  · simp [Metric.mem_ball, R]

lemma tsum_pow_div_succ_factorial (u : ℝ) (hu : u ≠ 0) :
    ∑' k : ℕ, u^k / ((k+1).factorial : ℝ) = (Real.exp u - 1) / u := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u
  rw [← Real.exp_eq_exp_ℝ] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one] at h1
  have h2 := h1.div_const u
  have : (fun k : ℕ => u^(k+1) / ((k+1).factorial : ℝ) / u) = fun k => u^k / ((k+1).factorial : ℝ) := by
    funext k; rw [pow_succ]; field_simp
  rw [this] at h2
  exact h2.tsum_eq

lemma li_hasDerivAt (y : ℝ) (hy : 1 < y) : HasDerivAt li (1 / Real.log y) y := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy
  have hlog := Real.hasDerivAt_log hy0.ne'
  have h1 : HasDerivAt (fun z => Real.log |Real.log z|) (y⁻¹ / Real.log y) y := by
    have : (fun z => Real.log |Real.log z|) = fun z => Real.log (Real.log z) := by
      funext z; exact Real.log_abs _
    rw [this]
    exact hlog.log hl.ne'
  have h2 := (Eser_hasDerivAt (Real.log y)).comp y hlog
  have h3 := (h1.const_add Real.eulerMascheroniConstant).add h2
  have hf : li = (fun x => Real.eulerMascheroniConstant + Real.log |Real.log x|) + Eser ∘ Real.log := by
    funext x; simp [li]
  rw [hf]
  refine h3.congr_deriv ?_
  rw [tsum_pow_div_succ_factorial _ hl.ne', Real.exp_log hy0]
  field_simp
  ring


lemma hasDerivAt_li_sub (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun s => li s - s / Real.log s) (1 / (Real.log t)^2) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have h1 := li_hasDerivAt t ht
  have h2 := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0.ne') hl.ne'
  refine (h1.sub h2).congr_deriv ?_
  simp only [id]
  field_simp
  ring

lemma cont_inv_log_sq (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => 1 / (Real.log t)^2) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    apply Real.continuousOn_log.mono
    intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity

lemma li_formula (x : ℝ) (hx : 2 ≤ x) :
    li x - x / Real.log x = (li 2 - 2 / Real.log 2) + ∫ t in (2:ℝ)..x, 1 / (Real.log t)^2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => li s - s / Real.log s) (a := 2) (b := x)
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact hasDerivAt_li_sub t (by linarith [ht.1]))
    ((cont_inv_log_sq 2 x (by norm_num) hx).intervalIntegrable)
  rw [h]; ring

lemma theta_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
  Chebyshev.theta_mono.intervalIntegrable

lemma cont_inv_tlog (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => 1 / (t * (Real.log t)^2)) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    apply Real.continuousOn_log.mono
    intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have : 0 < t := by linarith [ht.1]
    positivity

/-- The basic decomposition of `li(θ(x)) - π(x)`. -/
theorem D_decomp (x : ℝ) (hx : 2 ≤ x) :
    li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ) =
      (li 2 - 2 / Real.log 2) + (∫ t in (2:ℝ)..x, (t - Chebyshev.theta t) / (t * (Real.log t)^2)) +
      (li (Chebyshev.theta x) - li x - (Chebyshev.theta x - x) / Real.log x) := by
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  have hli := li_formula x hx
  have i1 : IntervalIntegrable (fun t : ℝ => 1 / (Real.log t)^2) volume 2 x :=
    (cont_inv_log_sq 2 x (by norm_num) hx).intervalIntegrable
  have i2 : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * (Real.log t)^2)) volume 2 x := by
    refine ((theta_intervalIntegrable 2 x).mul_continuousOn (cont_inv_tlog 2 x (by norm_num) hx)).congr ?_
    intro t _; simp only; ring
  have hsub : (∫ t in (2:ℝ)..x, (t - Chebyshev.theta t) / (t * (Real.log t)^2)) =
      (∫ t in (2:ℝ)..x, 1 / (Real.log t)^2) - ∫ t in (2:ℝ)..x, Chebyshev.theta t / (t * (Real.log t)^2) := by
    rw [← intervalIntegral.integral_sub i1 i2]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only
    field_simp
  rw [hπ, hsub]
  have hlx : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have e : (Chebyshev.theta x - x) / Real.log x = Chebyshev.theta x / Real.log x - x / Real.log x := by ring
  rw [e]
  linarith

lemma abs_log_sub_le (a s m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hs : m ≤ s) :
    |Real.log a - Real.log s| ≤ |a - s| / m := by
  have ha0 : 0 < a := by linarith
  have hs0 : 0 < s := by linarith
  have h1 : Real.log a - Real.log s ≤ (a - s) / s := by
    rw [← Real.log_div ha0.ne' hs0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hs0)
    have e : a / s - 1 = (a - s) / s := by field_simp
    linarith
  have h2 : Real.log s - Real.log a ≤ (s - a) / a := by
    rw [← Real.log_div hs0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hs0 ha0)
    have e : s / a - 1 = (s - a) / a := by field_simp
    linarith
  rw [abs_le]
  constructor
  · have : (s - a) / a ≤ |a - s| / m := by
      rw [div_le_div_iff₀ ha0 hm]
      have : s - a ≤ |a - s| := by rw [abs_sub_comm]; exact le_abs_self _
      have h0 : 0 ≤ |a - s| := abs_nonneg _
      nlinarith
    linarith
  · have : (a - s) / s ≤ |a - s| / m := by
      rw [div_le_div_iff₀ hs0 hm]
      have : a - s ≤ |a - s| := le_abs_self _
      have h0 : 0 ≤ |a - s| := abs_nonneg _
      nlinarith
    linarith

/-- First-order Taylor bound for `li`. -/
theorem li_taylor (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    |li b - li a - (b - a) / Real.log a| ≤ (b - a)^2 / (min a b * (Real.log (min a b))^2) := by
  set m := min a b with hmdef
  have hm2 : 2 ≤ m := le_min ha hb
  have hm0 : 0 < m := by linarith
  have hlm : 0 < Real.log m := Real.log_pos (by linarith)
  have hsub : ∀ s ∈ Set.uIcc a b, m ≤ s := by
    intro s hs
    rcases Set.mem_uIcc.mp hs with h | h
    · exact le_trans (min_le_left a b) h.1
    · exact le_trans (min_le_right a b) h.1
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const
    · apply Real.continuousOn_log.mono
      intro t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hsub t ht]
    · intro t ht; exact (Real.log_pos (by linarith [hsub t ht])).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := li) (a := a) (b := b)
    (fun t ht => li_hasDerivAt t (by linarith [hsub t ht])) hcont.intervalIntegrable
  have hconst : (b - a) / Real.log a = ∫ t in a..b, 1 / Real.log a := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have heq : li b - li a - (b - a) / Real.log a = ∫ t in a..b, (1 / Real.log t - 1 / Real.log a) := by
    rw [intervalIntegral.integral_sub hcont.intervalIntegrable intervalIntegrable_const, hFTC, hconst]
  rw [heq]
  have hbound : ∀ t ∈ Set.uIoc a b, ‖1 / Real.log t - 1 / Real.log a‖ ≤ |b - a| / (m * (Real.log m)^2) := by
    intro t ht
    have ht' : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have hmt := hsub t ht'
    have hma : m ≤ a := min_le_left a b
    have hlt : Real.log m ≤ Real.log t := Real.log_le_log hm0 hmt
    have hla : Real.log m ≤ Real.log a := Real.log_le_log hm0 hma
    have hlt0 : 0 < Real.log t := by linarith
    have hla0 : 0 < Real.log a := by linarith
    have hdist : |a - t| ≤ |b - a| := by
      rcases Set.mem_uIcc.mp ht' with h | h
      · rw [abs_sub_comm, abs_of_nonneg (by linarith [h.1]), abs_of_nonneg (by linarith [h.2])]; linarith [h.2]
      · rw [abs_of_nonneg (by linarith [h.2]), abs_of_nonpos (by linarith [h.1])]; linarith [h.1]
    have hlog := abs_log_sub_le a t m hm0 hma hmt
    rw [Real.norm_eq_abs]
    have e : 1 / Real.log t - 1 / Real.log a = (Real.log a - Real.log t) / (Real.log t * Real.log a) := by
      field_simp
    rw [e, abs_div, abs_of_pos (by positivity : 0 < Real.log t * Real.log a)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |Real.log a - Real.log t| * m ≤ |b - a| := by
      have := (le_div_iff₀ hm0).mp hlog
      linarith
    have h2 : (Real.log m)^2 ≤ Real.log t * Real.log a := by nlinarith
    calc |Real.log a - Real.log t| * (m * Real.log m ^ 2)
        = (|Real.log a - Real.log t| * m) * Real.log m ^ 2 := by ring
      _ ≤ |b - a| * (Real.log t * Real.log a) := by
          apply mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at this
  calc _ ≤ |b - a| / (m * (Real.log m)^2) * |b - a| := this
    _ = (b - a)^2 / (m * (Real.log m)^2) := by rw [div_mul_eq_mul_div, ← sq, sq_abs]

end NicL

namespace NicS

noncomputable def Mfun (x : ℝ) : ℝ :=
  ((∑ n ∈ range (⌊x⌋₊+1), vonMangoldt n * max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)) / x

noncomputable def βc : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

noncomputable def gfun (t : ℝ) : ℝ := (Chebyshev.psi t - t) / t^2

noncomputable def Sfun (t : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊t⌋₊, (vonMangoldt k : ℝ) / k

lemma range_sum_eq (t : ℝ) (ht : 1 ≤ t) :
    (∑ n ∈ range (⌊t⌋₊+1), vonMangoldt n * max (t/(n:ℝ)-1) 0) =
      t * Sfun t - Chebyshev.psi t := by
  have hr : range (⌊t⌋₊+1) = Icc 0 ⌊t⌋₊ := by ext; simp
  rw [hr, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), Chebyshev.psi_eq_sum_Icc,
    ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [ArithmeticFunction.map_zero, zero_mul, zero_add, Sfun, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ioc] at hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
  have hkt : (k:ℝ) ≤ t := le_trans (by exact_mod_cast hk.2) (Nat.floor_le (by linarith))
  have hk0 : (0:ℝ) < k := by linarith
  rw [max_eq_left]
  · field_simp
  · rw [sub_nonneg, le_div_iff₀ hk0]; linarith

lemma Mfun_eq (t : ℝ) (ht : 1 ≤ t) :
    Mfun t = Sfun t - Chebyshev.psi t / t - Real.log t + 1 + Real.eulerMascheroniConstant := by
  rw [Mfun, range_sum_eq t ht]
  have : t ≠ 0 := by positivity
  field_simp
  ring

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable Chebyshev.psi volume a b :=
  Chebyshev.psi_mono.intervalIntegrable

lemma gfun_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable gfun volume a b := by
  have h0 : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    have : 0 < t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    exact this.ne'
  have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have h2 : ContinuousOn (fun t : ℝ => t / t^2) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht; exact pow_ne_zero 2 (h0 t ht)
  have := ((psi_intervalIntegrable a b).mul_continuousOn h1).sub (h2.intervalIntegrable)
  refine this.congr ?_
  intro t _
  simp only [gfun]
  ring

/-- `M` is a primitive of `(ψ(t)-t)/t²`. -/
theorem integral_gfun (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, gfun t = Mfun b - Mfun a := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- Abel summation with f = t⁻¹
  have hA := sum_mul_eq_sub_sub_integral_mul (fun k => (vonMangoldt k : ℝ)) ha0.le hab
    (f := fun t : ℝ => t⁻¹)
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : Set.EqOn (deriv fun t : ℝ => t⁻¹) (fun t => -(t^2)⁻¹) (Set.Icc a b) := by
        intro t _; exact deriv_inv
      refine (IntegrableOn.congr_fun ?_ this.symm measurableSet_Icc)
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (continuousOn_pow 2)
      intro t ht; exact pow_ne_zero 2 (by linarith [ht.1]))
  simp only [← Chebyshev.psi_eq_sum_Icc] at hA
  have hderiv : ∀ t ∈ Set.Ioc a b, deriv (fun t : ℝ => t⁻¹) t * Chebyshev.psi t =
      -(Chebyshev.psi t / t^2) := by
    intro t _; rw [deriv_inv]; ring
  rw [setIntegral_congr_fun measurableSet_Ioc hderiv, integral_neg,
    ← intervalIntegral.integral_of_le hab] at hA
  have hS : Sfun b = Sfun a + ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k := by
    rw [Sfun, Sfun, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hab)]
  have hS' : ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (vonMangoldt k : ℝ) / k =
      ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ((k:ℝ))⁻¹ * (vonMangoldt k : ℝ) := by
    apply Finset.sum_congr rfl; intro k _; ring
  have hpsi_int : IntervalIntegrable (fun t => Chebyshev.psi t / t^2) volume a b := by
    have h1 : ContinuousOn (fun t : ℝ => 1 / t^2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact pow_ne_zero 2 (by linarith [ht.1])
    refine ((psi_intervalIntegrable a b).mul_continuousOn h1).congr ?_
    intro t _; simp only; ring
  have hinv_int : IntervalIntegrable (fun t : ℝ => t / t^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_id (continuousOn_pow 2)
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (by linarith [ht.1])
  have hsplit : ∫ t in a..b, gfun t = (∫ t in a..b, Chebyshev.psi t / t^2) -
      ∫ t in a..b, t / t^2 := by
    rw [← intervalIntegral.integral_sub hpsi_int hinv_int]
    congr 1; funext t; simp only [gfun]; ring
  have hlog : ∫ t in a..b, t / t^2 = Real.log b - Real.log a := by
    have : ∫ t in a..b, t / t^2 = ∫ t in a..b, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      have : t ≠ 0 := by linarith [ht.1]
      simp only; field_simp
    rw [this, integral_inv (by
      rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]),
      Real.log_div hb0.ne' ha0.ne']
  rw [hsplit, hlog, Mfun_eq b (by linarith), Mfun_eq a ha, hS, hS', hA]
  have e1 : b⁻¹ * Chebyshev.psi b = Chebyshev.psi b / b := by ring
  have e2 : a⁻¹ * Chebyshev.psi a = Chebyshev.psi a / a := by ring
  rw [e1, e2]
  ring





lemma psi_rcont (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt Chebyshev.psi (Set.Ioi t) t := by
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  apply (continuousWithinAt_const (b := Chebyshev.psi t)).congr_of_eventuallyEq
  · filter_upwards [Ioo_mem_nhdsGT hlt] with u hu
    rw [Chebyshev.psi_eq_psi_coe_floor u, Chebyshev.psi_eq_psi_coe_floor t]
    congr 2
    rw [Nat.floor_eq_iff (by linarith [hu.1])]
    exact ⟨le_trans (Nat.floor_le ht) hu.1.le, hu.2⟩
  · rfl

lemma gfun_rcont (t : ℝ) (ht : 0 < t) : ContinuousWithinAt gfun (Set.Ioi t) t := by
  unfold gfun
  apply ContinuousWithinAt.div ((psi_rcont t ht.le).sub continuousWithinAt_id)
    (continuousWithinAt_id.pow 2) (pow_ne_zero 2 ht.ne')

lemma gfun_measurable : Measurable gfun := by
  unfold gfun
  have := Chebyshev.psi_mono.measurable
  fun_prop

lemma gamma_lt : Real.eulerMascheroniConstant < 0.5929 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  simp only [Real.eulerMascheroniSeq', show (32:ℕ) ≠ 0 by norm_num, if_false] at h
  have hH : ((harmonic 32 : ℚ) : ℝ) < 4.0586 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : Real.log (32:ℕ) = 5 * Real.log 2 := by
    rw [show ((32:ℕ):ℝ) = 2^5 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [hl] at h
  linarith

lemma log_four_pi_gt : 5/2 < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have h5 : Real.exp 5 < 149 := by
    rw [show (5:ℝ) = (5:ℕ) by norm_num, ← Real.exp_one_pow]
    have := Real.exp_one_lt_d9
    have h0 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 5 ≤ (2.7182818286:ℝ)^5 := pow_le_pow_left₀ h0 this.le 5
      _ < 149 := by norm_num
  have hsq : Real.exp (5/2) ^ 2 = Real.exp 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hpi := Real.pi_gt_d2
  have hpos := Real.exp_pos (5/2)
  nlinarith

lemma beta_lt : βc < 1/10 := by
  have := gamma_lt; have := log_four_pi_gt
  unfold βc; linarith
noncomputable def Kt (x : ℝ) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))

lemma re_half (hRH : RiemannHypothesis) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ρ.val.re = 1/2 := by
  obtain ⟨hz, h0, h1, -⟩ := ρ.property
  apply hRH ρ.val hz
  · rintro ⟨n, hn⟩
    have : ρ.val.re = -2 * ((n:ℝ) + 1) := by rw [hn]; simp
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at h1; simp at h1

lemma norm_Kt (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x)
    (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ‖Kt x ρ‖ = x ^ (-(1/2:ℝ)) * ((analyticOrderNatAt riemannZeta ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hre := re_half hRH ρ
  have hne : ρ.val ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hn1 : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, hre]
    ring
  rw [Kt, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hn1]
  have : (ρ.val - 1).re = -(1/2) := by simp [hre]; norm_num
  rw [this]
  simp only [Complex.norm_natCast]
  have hp : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
  field_simp

lemma summable_Kt (x : ℝ) (hx : 1 ≤ x) : Summable (fun ρ => ‖Kt x ρ‖) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  exact h.1 x hx

lemma tsum_norm_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    ∑' ρ, ‖Kt x ρ‖ ≤ βc * x ^ (-(1/2:ℝ)) := by
  have hx0 : 0 < x := by linarith
  apply (summable_Kt x hx).tsum_le_of_sum_le
  intro s
  simp_rw [norm_Kt hRH x hx0]
  rw [← Finset.mul_sum, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hL := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH
    (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro ρ hρ
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      exact ⟨r.property.1, r.property.2.1⟩)
  rw [Finset.sum_map] at hL
  simpa [βc] using hL

lemma abs_re_tsum_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    |(∑' ρ, Kt x ρ).re| ≤ βc * x ^ (-(1/2:ℝ)) :=
  (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (summable_Kt x hx)).trans
    (tsum_norm_Kt_le hRH x hx))

noncomputable def cfun (t : ℝ) : ℝ := Real.log (2*Real.pi) + (1/2) * Real.log (1 - t^(-2:ℝ))

lemma cfun_bounds (t : ℝ) (ht : 2 ≤ t) : 0 ≤ cfun t ∧ cfun t ≤ Real.log (2*Real.pi) := by
  have ht0 : 0 < t := by linarith
  have h1 : t^(-2:ℝ) ≤ 1/4 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 0 < t^(-2:ℝ) := Real.rpow_pos_of_pos ht0 _
  have h3 : Real.log (3/4) ≤ Real.log (1 - t^(-2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h3' : Real.log (1 - t^(-2:ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : Real.log 6 ≤ Real.log (2*Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h5 : Real.log (3/4) = Real.log 3 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h7 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h8 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := Real.log_two_gt_d9
  unfold cfun
  constructor <;> nlinarith

lemma cfun_cont (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t => cfun t / t^2) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : t^(-2:ℝ) < 1 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_lt_one_iff₀]; right; nlinarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold cfun
  apply ContinuousAt.div _ (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')
  apply ContinuousAt.add continuousAt_const
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.log _ (by linarith)
  apply ContinuousAt.sub continuousAt_const
  exact Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')

/-- Masullo's identity, real form. -/
theorem M_identity (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Mfun b - Mfun a = -((∑' ρ, Kt b ρ).re - (∑' ρ, Kt a ρ).re) - ∫ t in a..b, cfun t / t^2 := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  have hE := h.2 a b ha hab
  have hsa : Summable (fun ρ => Kt a ρ) := (summable_Kt a (by linarith)).of_norm
  have hsb : Summable (fun ρ => Kt b ρ) := (summable_Kt b (by linarith)).of_norm
  have hsplit : (∑' ρ : MasulloRH.ZetaZerosInTraceStrip (1/2),
      ((analyticOrderNatAt riemannZeta ρ.val : ℂ) * (b:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)) -
        (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (a:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)))) =
      (∑' ρ, Kt b ρ) - ∑' ρ, Kt a ρ := (hsb.tsum_sub hsa)
  rw [hsplit] at hE
  have hint : (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      ((∫ t in a..b, cfun t / t^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t; unfold cfun; push_cast; ring
  rw [hint] at hE
  have hre := congrArg Complex.re hE
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hMb : Mfun b = ((∑ n ∈ range (⌊b⌋₊+1), vonMangoldt n * max (b/(n:ℝ)-1) 0) -
      b*(Real.log b-1-Real.eulerMascheroniConstant)) / b := rfl
  have hMa : Mfun a = ((∑ n ∈ range (⌊a⌋₊+1), vonMangoldt n * max (a/(n:ℝ)-1) 0) -
      a*(Real.log a-1-Real.eulerMascheroniConstant)) / a := rfl
  rw [hMb, hMa]
  linarith

lemma int_c_bounds (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, cfun t / t^2 ∧
      ∫ t in a..b, cfun t / t^2 ≤ Real.log (2*Real.pi) * (1/a - 1/b) := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (cfun_bounds t (by linarith [ht.1])).1 (by positivity)
  · have hm : ∫ t in a..b, cfun t / t^2 ≤ ∫ t in a..b, Real.log (2*Real.pi) / t^2 := by
      apply intervalIntegral.integral_mono_on hab
      · exact (cfun_cont a b ha hab).intervalIntegrable
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        intro t ht; rw [Set.uIcc_of_le hab] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      · intro t ht
        exact div_le_div_of_nonneg_right (cfun_bounds t (by linarith [ht.1])).2 (by positivity)
    have he : ∫ t in a..b, Real.log (2*Real.pi) / t^2 = Real.log (2*Real.pi) * (1/a - 1/b) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.log (2*Real.pi) / t)]
      · field_simp; ring
      · intro t ht; rw [Set.uIcc_of_le hab] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have := (hasDerivAt_inv ht0).const_mul (-Real.log (2*Real.pi))
        have e1 : (fun t : ℝ => -Real.log (2*Real.pi) / t) = (fun y => -Real.log (2 * Real.pi) * y⁻¹) := by
          funext s; rw [div_eq_mul_inv]
        rw [e1]
        exact this.congr_deriv (by rw [neg_mul_neg, div_eq_mul_inv])
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        intro t ht; rw [Set.uIcc_of_le hab] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
    linarith



lemma M_bd (hRH : RiemannHypothesis) (t : ℝ) (ht : 2 ≤ t) :
    |Mfun t| ≤ βc * t ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / t :=
  NicolasBRH.prime_ramp_bound_of_RH hRH t ht

lemma log_two_pi_lt : Real.log (2*Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.pi_lt_d2
  nlinarith

lemma log_two_pi_pos : 0 < Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])



/-! ## The function `I*(t) = M(t) + Re Σ K_t` -/

noncomputable def SK (t : ℝ) : ℝ := (∑' ρ, Kt t ρ).re

noncomputable def Istar (t : ℝ) : ℝ := Mfun t + SK t

lemma Istar_sub (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Istar a - Istar b = ∫ t in a..b, cfun t / t^2 := by
  have h := M_identity a b ha hab
  simp only [Istar, SK]
  linarith

lemma beta_nonneg (hRH : RiemannHypothesis) : 0 ≤ βc := by
  have := tsum_norm_Kt_le hRH 1 le_rfl
  have h0 : 0 ≤ ∑' ρ, ‖Kt 1 ρ‖ := tsum_nonneg (fun _ => norm_nonneg _)
  simp at this
  linarith

lemma Istar_abs (hRH : RiemannHypothesis) (b : ℝ) (hb : 2 ≤ b) :
    |Istar b| ≤ 2 * βc * b ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / b := by
  have h1 := M_bd hRH b hb
  have h2 := abs_re_tsum_Kt_le hRH b (by linarith)
  calc |Istar b| ≤ |Mfun b| + |SK b| := abs_add_le _ _
    _ ≤ _ := by simp only [SK]; linarith

lemma Istar_tendsto (hRH : RiemannHypothesis) : Tendsto Istar atTop (𝓝 0) := by
  have hb : Tendsto (fun b : ℝ => 2 * βc * b ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / b) atTop (𝓝 0) := by
    have h1 : Tendsto (fun b : ℝ => b ^ (-(1/2:ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
    have h2 : Tendsto (fun b : ℝ => Real.log (2*Real.pi) / b) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h1.const_mul (2 * βc)).add h2
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun b => abs_nonneg _)) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with b hb2
  exact Istar_abs hRH b hb2

lemma Istar_bounds (hRH : RiemannHypothesis) (a : ℝ) (ha : 2 ≤ a) :
    0 ≤ Istar a ∧ Istar a ≤ Real.log (2*Real.pi) / a := by
  have hT := Istar_tendsto hRH
  have key : ∀ b, a ≤ b → Istar b ≤ Istar a ∧ Istar a ≤ Istar b + Real.log (2*Real.pi) / a := by
    intro b hab
    have h := Istar_sub a b ha hab
    have hc := int_c_bounds a b ha hab
    have hb0 : 0 < b := by linarith
    have : Real.log (2*Real.pi) * (1/a - 1/b) ≤ Real.log (2*Real.pi) / a := by
      have : 0 ≤ Real.log (2*Real.pi) / b := div_nonneg log_two_pi_pos.le hb0.le
      have e : Real.log (2*Real.pi) * (1/a - 1/b) = Real.log (2*Real.pi) / a - Real.log (2*Real.pi) / b := by ring
      linarith
    constructor <;> linarith [hc.1, hc.2]
  constructor
  · exact le_of_tendsto hT (by filter_upwards [eventually_ge_atTop a] with b hb; exact (key b hb).1)
  · have hT' : Tendsto (fun b => Istar b + Real.log (2*Real.pi) / a) atTop (𝓝 (0 + Real.log (2*Real.pi) / a)) :=
      hT.add tendsto_const_nhds
    rw [zero_add] at hT'
    exact ge_of_tendsto hT' (by filter_upwards [eventually_ge_atTop a] with b hb; exact (key b hb).2)


/-! ## The antiderivative `F` of `Re Σ K_t` -/

abbrev ZZ := MasulloRH.ZetaZerosInTraceStrip (1/2)

lemma rho_ne_zero (hRH : RiemannHypothesis) (ρ : ZZ) : ρ.val ≠ 0 := by
  intro h; have := re_half hRH ρ; rw [h] at this; simp at this

lemma rho_sub_one_ne_zero (hRH : RiemannHypothesis) (ρ : ZZ) : ρ.val - 1 ≠ 0 := by
  intro h; have := re_half hRH ρ; rw [sub_eq_zero.mp h] at this; norm_num at this

lemma norm_rho_sub_one (hRH : RiemannHypothesis) (ρ : ZZ) : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
  have hre := re_half hRH ρ
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, hre]
  ring

lemma norm_rho_ge (hRH : RiemannHypothesis) (ρ : ZZ) : 1/2 ≤ ‖ρ.val‖ := by
  have := Complex.abs_re_le_norm ρ.val
  rw [re_half hRH ρ] at this
  simpa using this

noncomputable def Gz (x : ℝ) (ρ : ZZ) : ℂ := Kt 1 ρ * ((x:ℂ)^ρ.val / ρ.val)

noncomputable def Ffun (x : ℝ) : ℝ := (∑' ρ, Gz x ρ).re

lemma Kt_eq (x : ℝ) (ρ : ZZ) : Kt x ρ = Kt 1 ρ * (x:ℂ)^(ρ.val - 1) := by
  simp only [Kt, Complex.ofReal_one, Complex.one_cpow]
  ring

lemma Gz_hasDerivAt (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) (ρ : ZZ) :
    HasDerivAt (fun y => Gz y ρ) (Kt x ρ) x := by
  have hr : ρ.val - 1 ≠ -1 := by
    intro h; apply rho_ne_zero hRH ρ; linear_combination h
  have h := hasDerivAt_ofReal_cpow_const' hx.ne' hr
  rw [sub_add_cancel] at h
  rw [Kt_eq]
  exact h.const_mul (Kt 1 ρ)

lemma norm_cpow_rho (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) (ρ : ZZ) :
    ‖(x:ℂ)^ρ.val‖ = x ^ (1/2:ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, re_half hRH ρ]

lemma norm_Gz (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) (ρ : ZZ) :
    ‖Gz x ρ‖ = ‖Kt 1 ρ‖ * (x ^ (1/2:ℝ) / ‖ρ.val‖) := by
  rw [Gz, norm_mul, norm_div, norm_cpow_rho hRH x hx]

lemma norm_Gz_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) (ρ : ZZ) :
    ‖Gz x ρ‖ ≤ 2 * x ^ (1/2:ℝ) * ‖Kt 1 ρ‖ := by
  rw [norm_Gz hRH x hx]
  have h1 := norm_rho_ge hRH ρ
  have h2 : x ^ (1/2:ℝ) / ‖ρ.val‖ ≤ 2 * x ^ (1/2:ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ x ^ (1/2:ℝ) := by positivity
    nlinarith
  have h3 : 0 ≤ ‖Kt 1 ρ‖ := norm_nonneg _
  nlinarith

lemma summable_Gz (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) : Summable (fun ρ => ‖Gz x ρ‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_Gz_le hRH x hx)
    ((summable_Kt 1 le_rfl).mul_left _)

lemma norm_Kt_le_one (hRH : RiemannHypothesis) (y : ℝ) (hy : 1 ≤ y) (ρ : ZZ) :
    ‖Kt y ρ‖ ≤ ‖Kt 1 ρ‖ := by
  rw [norm_Kt hRH y (by linarith), norm_Kt hRH 1 one_pos, Real.one_rpow, one_mul]
  have : y ^ (-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have h0 : 0 ≤ (analyticOrderNatAt riemannZeta ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by positivity
  nlinarith

lemma Ffun_hasDerivAt (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 < x) :
    HasDerivAt Ffun (SK x) x := by
  have h := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioi (1:ℝ)) (y₀ := 2)
    (g := fun (ρ : ZZ) (y : ℝ) => Gz y ρ) (g' := fun (ρ : ZZ) (y : ℝ) => Kt y ρ)
    (summable_Kt 1 le_rfl) isOpen_Ioi isPreconnected_Ioi
    (fun ρ y hy => Gz_hasDerivAt hRH y (lt_trans one_pos hy) ρ)
    (fun ρ y hy => norm_Kt_le_one hRH y (le_of_lt hy) ρ)
    (by norm_num) (summable_Gz hRH 2 (by norm_num)).of_norm hx
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  exact h2

lemma Ffun_abs (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) :
    |Ffun x| ≤ 2 * βc * x ^ (1/2:ℝ) := by
  have hs := summable_Gz hRH x hx
  have h1 : |Ffun x| ≤ ∑' ρ, ‖Gz x ρ‖ :=
    (Complex.abs_re_le_norm _).trans (norm_tsum_le_tsum_norm hs)
  have h2 : ∑' ρ, ‖Gz x ρ‖ ≤ ∑' ρ, 2 * x ^ (1/2:ℝ) * ‖Kt 1 ρ‖ :=
    hs.tsum_le_tsum (norm_Gz_le hRH x hx) ((summable_Kt 1 le_rfl).mul_left _)
  rw [tsum_mul_left] at h2
  have h3 := tsum_norm_Kt_le hRH 1 le_rfl
  rw [Real.one_rpow, mul_one] at h3
  have : 0 ≤ 2 * x ^ (1/2:ℝ) := by positivity
  nlinarith

lemma xK_sub_G (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x) (ρ : ZZ) :
    ‖(x:ℂ) * Kt x ρ - Gz x ρ‖ = ‖Kt 1 ρ‖ * x ^ (1/2:ℝ) := by
  have hne := rho_ne_zero hRH ρ
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : (x:ℂ) * Kt x ρ - Gz x ρ = Kt 1 ρ * ((x:ℂ)^ρ.val * ((ρ.val - 1) / ρ.val)) := by
    rw [Kt_eq, Gz]
    have : (x:ℂ)^ρ.val = (x:ℂ)^(ρ.val - 1) * x := by
      conv_lhs => rw [show ρ.val = (ρ.val - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ hx', Complex.cpow_one]
    rw [this]
    field_simp
  rw [e, norm_mul, norm_mul, norm_div, norm_cpow_rho hRH x hx, norm_rho_sub_one hRH,
    div_self (norm_ne_zero_iff.mpr hne), mul_one]

lemma xSK_sub_F (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    |x * SK x - Ffun x| ≤ βc * x ^ (1/2:ℝ) := by
  have hx0 : 0 < x := by linarith
  have hsK := (summable_Kt x hx).of_norm
  have hsG := (summable_Gz hRH x hx0).of_norm
  have e : x * SK x - Ffun x = (∑' ρ, ((x:ℂ) * Kt x ρ - Gz x ρ)).re := by
    rw [(hsK.mul_left (x:ℂ)).tsum_sub hsG, tsum_mul_left, Complex.sub_re, Complex.re_ofReal_mul]
    rfl
  have hsD : Summable (fun ρ => ‖(x:ℂ) * Kt x ρ - Gz x ρ‖) := by
    simp_rw [xK_sub_G hRH x hx0]
    exact (summable_Kt 1 le_rfl).mul_right _
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hsD).trans ?_)
  simp_rw [xK_sub_G hRH x hx0]
  rw [tsum_mul_right]
  have h3 := tsum_norm_Kt_le hRH 1 le_rfl
  rw [Real.one_rpow, mul_one] at h3
  have : 0 ≤ x ^ (1/2:ℝ) := by positivity
  nlinarith


/-! ## Continuity of `M` and the primitive `N` -/

lemma Mfun_contOn (b : ℝ) (hb : 1 ≤ b) : ContinuousOn Mfun (Set.Icc 1 b) := by
  have hI : IntegrableOn gfun (Set.uIcc 1 b) volume := by
    rw [Set.uIcc_of_le hb]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb).mp
      (gfun_intervalIntegrable 1 b one_pos (by linarith))
  have hc := intervalIntegral.continuousOn_primitive_interval hI
  rw [Set.uIcc_of_le hb] at hc
  have : Set.EqOn Mfun (fun t => Mfun 1 + ∫ s in (1:ℝ)..t, gfun s) (Set.Icc 1 b) := by
    intro t ht
    simp only
    rw [integral_gfun 1 t le_rfl ht.1]; ring
  exact (continuousOn_const.add hc).congr this

lemma Mfun_contAt (t : ℝ) (ht : 1 < t) : ContinuousAt Mfun t := by
  have h := Mfun_contOn (t+1) (by linarith)
  exact h.continuousAt (Icc_mem_nhds ht (by linarith))

lemma Mfun_contOn_Ioi : ContinuousOn Mfun (Set.Ioi 1) :=
  fun t ht => (Mfun_contAt t ht).continuousWithinAt

lemma Mfun_ii (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : IntervalIntegrable Mfun volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply Mfun_contOn_Ioi.mono
  intro t ht
  rcases Set.mem_uIcc.mp ht with h | h
  · exact lt_of_lt_of_le ha h.1
  · exact lt_of_lt_of_le hb h.1

noncomputable def Nfun (t : ℝ) : ℝ := ∫ s in (2:ℝ)..t, Mfun s

lemma Nfun_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt Nfun (Mfun t) t :=
  intervalIntegral.integral_hasDerivAt_right (Mfun_ii 2 t (by norm_num) ht)
    (Mfun_contOn_Ioi.stronglyMeasurableAtFilter isOpen_Ioi t ht) (Mfun_contAt t ht)

lemma Istar_antitoneOn : AntitoneOn Istar (Set.Ici 2) := by
  intro a ha b hb hab
  have := Istar_sub a b ha hab
  have h0 := (int_c_bounds a b ha hab).1
  linarith

lemma Istar_ii (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) : IntervalIntegrable Istar volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply Istar_antitoneOn.mono
  intro t ht
  rcases Set.mem_uIcc.mp ht with h | h
  · exact le_trans ha h.1
  · exact le_trans hb h.1

lemma SK_ii (a b : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) : IntervalIntegrable SK volume a b := by
  refine ((Istar_ii a b ha hb).sub (Mfun_ii a b (by linarith) (by linarith))).congr ?_
  intro t _; simp [Istar]

lemma int_SK (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, SK t = Ffun x - Ffun 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact Ffun_hasDerivAt hRH t (by linarith [ht.1])
  · exact SK_ii 2 x le_rfl hx

lemma Nfun_eq (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    Nfun x = (∫ t in (2:ℝ)..x, Istar t) - (Ffun x - Ffun 2) := by
  rw [← int_SK hRH x hx, ← intervalIntegral.integral_sub (Istar_ii 2 x le_rfl hx) (SK_ii 2 x le_rfl hx)]
  apply intervalIntegral.integral_congr
  intro t _; simp [Istar]


/-! ## Integration by parts against `g(t) = t / log² t` -/

noncomputable def gg (t : ℝ) : ℝ := t / (Real.log t)^2
noncomputable def gg1 (t : ℝ) : ℝ := 1 / (Real.log t)^2 - 2 / (Real.log t)^3
noncomputable def gg2 (t : ℝ) : ℝ := -2 / (t * (Real.log t)^3) + 6 / (t * (Real.log t)^4)

lemma gg_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt gg (gg1 t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (hasDerivAt_id t).div ((Real.hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl)
  refine h.congr_deriv ?_
  simp only [gg1, id, Pi.pow_apply]
  field_simp
  ring

lemma gg1_hasDerivAt (t : ℝ) (ht : 1 < t) : HasDerivAt gg1 (gg2 t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := (hasDerivAt_const t (1:ℝ)).div ((Real.hasDerivAt_log ht0).pow 2) (pow_ne_zero 2 hl)
  have h2 := (hasDerivAt_const t (2:ℝ)).div ((Real.hasDerivAt_log ht0).pow 3) (pow_ne_zero 3 hl)
  refine (h1.sub h2).congr_deriv ?_
  simp only [gg2, Pi.pow_apply]
  field_simp
  ring

lemma gg2_contAt (t : ℝ) (ht : 1 < t) : ContinuousAt gg2 t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h3 : t * Real.log t ^ 3 ≠ 0 := by positivity
  have h4 : t * Real.log t ^ 4 ≠ 0 := by positivity
  unfold gg2
  fun_prop (disch := assumption)

lemma contOn_of_gt_one (f : ℝ → ℝ) (hf : ∀ t, 1 < t → ContinuousAt f t) (a b : ℝ) (ha : 1 < a)
    (hb : 1 < b) : ContinuousOn f (Set.uIcc a b) := by
  intro t ht
  apply (hf t _).continuousWithinAt
  rcases Set.mem_uIcc.mp ht with h | h
  · exact lt_of_lt_of_le ha h.1
  · exact lt_of_lt_of_le hb h.1

lemma ibp1 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, gfun t * gg t =
      Mfun x * gg x - Mfun 2 * gg 2 - ∫ t in (2:ℝ)..x, Mfun t * gg1 t := by
  have h2 : (0:ℝ) < 2 := by norm_num
  let u : ℝ → ℝ := fun t => ∫ s in (2:ℝ)..t, gfun s
  have hgi : IntervalIntegrable gfun volume 2 x := gfun_intervalIntegrable 2 x h2 (by linarith)
  have hIcc : IntegrableOn gfun (Set.uIcc 2 x) volume := by
    rw [Set.uIcc_of_le hx]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mp hgi
  have hu_cont : ContinuousOn u (Set.uIcc 2 x) :=
    intervalIntegral.continuousOn_primitive_interval hIcc
  have hu_eq : ∀ t ∈ Set.uIcc (2:ℝ) x, u t = Mfun t - Mfun 2 := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht
    exact integral_gfun 2 t (by norm_num) ht.1
  have hggc : ContinuousOn gg (Set.uIcc 2 x) :=
    contOn_of_gt_one gg (fun t ht => (gg_hasDerivAt t ht).continuousAt) 2 x (by norm_num) (by linarith)
  have hgg1c : ContinuousOn gg1 (Set.uIcc 2 x) :=
    contOn_of_gt_one gg1 (fun t ht => (gg1_hasDerivAt t ht).continuousAt) 2 x (by norm_num) (by linarith)
  have hu_der : ∀ t ∈ Set.Ioo (min (2:ℝ) x) (max 2 x),
      HasDerivWithinAt u (gfun t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hx, max_eq_right hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h := intervalIntegral.integral_hasDerivWithinAt_right
      (gfun_intervalIntegrable 2 t h2 ht0)
      (s := Set.Ici t) (t := Set.Ioi t)
      (gfun_measurable.stronglyMeasurable.stronglyMeasurableAtFilter) (gfun_rcont t ht0)
    exact h.mono Set.Ioi_subset_Ici_self
  have hv_der : ∀ t ∈ Set.Ioo (min (2:ℝ) x) (max 2 x),
      HasDerivWithinAt gg (gg1 t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hx] at ht
    exact (gg_hasDerivAt t (by linarith [ht.1])).hasDerivWithinAt
  have hvd_int : IntervalIntegrable gg1 volume 2 x := hgg1c.intervalIntegrable
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    hu_cont hggc hu_der hv_der hgi hvd_int
  have hu2 : u 2 = 0 := intervalIntegral.integral_same
  have hun : u x = Mfun x - Mfun 2 := hu_eq x Set.right_mem_uIcc
  rw [hu2, hun] at hparts
  have hgv : IntervalIntegrable (fun t => gfun t * gg t) volume 2 x :=
    hgi.mul_continuousOn hggc
  have huv : IntervalIntegrable (fun t => u t * gg1 t) volume 2 x :=
    (hu_cont.mul hgg1c).intervalIntegrable
  rw [intervalIntegral.integral_add hgv huv] at hparts
  have e2 : ∫ t in (2:ℝ)..x, u t * gg1 t =
      ∫ t in (2:ℝ)..x, (Mfun t * gg1 t - Mfun 2 * gg1 t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only; rw [hu_eq t ht]; ring
  have hMi : IntervalIntegrable (fun t => Mfun t * gg1 t) volume 2 x :=
    (Mfun_ii 2 x (by norm_num) (by linarith)).mul_continuousOn hgg1c
  rw [e2, intervalIntegral.integral_sub hMi (hvd_int.const_mul _),
    intervalIntegral.integral_const_mul] at hparts
  have e3 : ∫ t in (2:ℝ)..x, gg1 t = gg x - gg 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht; rw [Set.uIcc_of_le hx] at ht
      exact gg_hasDerivAt t (by linarith [ht.1])
    · exact hvd_int
  rw [e3] at hparts
  linarith

lemma ibp2 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, Mfun t * gg1 t = Nfun x * gg1 x - ∫ t in (2:ℝ)..x, Nfun t * gg2 t := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 2) (b := x)
    (u := Nfun) (u' := Mfun) (v := gg1) (v' := gg2)
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact Nfun_hasDerivAt t (by linarith [ht.1]))
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      exact gg1_hasDerivAt t (by linarith [ht.1]))
    (Mfun_ii 2 x (by norm_num) (by linarith))
    ((contOn_of_gt_one gg2 gg2_contAt 2 x (by norm_num) (by linarith)).intervalIntegrable)
  have hN2 : Nfun 2 = 0 := intervalIntegral.integral_same
  rw [hN2] at h
  linarith

/-- The zero-sum integral `J₁(x) = ∫₂ˣ (t - ψ(t)) / (t log² t) dt`. -/
noncomputable def J1 (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, (t - Chebyshev.psi t) / (t * (Real.log t)^2)

lemma J1_eq (x : ℝ) (hx : 2 ≤ x) :
    J1 x = -(Mfun x * gg x) + Mfun 2 * gg 2 + Nfun x * gg1 x - ∫ t in (2:ℝ)..x, Nfun t * gg2 t := by
  have h1 : J1 x = -∫ t in (2:ℝ)..x, gfun t * gg t := by
    rw [J1, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [gfun, gg]
    field_simp
    ring
  rw [h1, ibp1 x hx, ibp2 x hx]
  ring


/-! ## Bounds -/

lemma log_le_two_sqrt (t : ℝ) (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  rw [Real.log_sqrt ht.le] at h
  linarith

lemma rpow_half_eq (t : ℝ) (ht : 0 ≤ t) : t ^ (1/2:ℝ) = Real.sqrt t := (Real.sqrt_eq_rpow t).symm

lemma int_Istar_bounds (hRH : RiemannHypothesis) (t : ℝ) (ht : 2 ≤ t) :
    0 ≤ ∫ s in (2:ℝ)..t, Istar s ∧ ∫ s in (2:ℝ)..t, Istar s ≤ Real.log (2*Real.pi) * Real.log t := by
  constructor
  · apply intervalIntegral.integral_nonneg ht
    intro s hs; exact (Istar_bounds hRH s hs.1).1
  · have hinv : IntervalIntegrable (fun s : ℝ => Real.log (2*Real.pi) * s⁻¹) volume 2 t := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ continuousOn_id
      intro s hs; rw [Set.uIcc_of_le ht] at hs; simp only [id]; linarith [hs.1]
    have h1 : ∫ s in (2:ℝ)..t, Istar s ≤ ∫ s in (2:ℝ)..t, Real.log (2*Real.pi) * s⁻¹ := by
      apply intervalIntegral.integral_mono_on ht (Istar_ii 2 t le_rfl ht) hinv
      intro s hs
      have := (Istar_bounds hRH s hs.1).2
      rwa [div_eq_mul_inv] at this
    rw [intervalIntegral.integral_const_mul, integral_inv (by
      rw [Set.uIcc_of_le ht]; intro h; linarith [h.1])] at h1
    have : Real.log (t / 2) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
    have hl := log_two_pi_pos
    nlinarith

lemma Nfun_abs (hRH : RiemannHypothesis) (t : ℝ) (ht : 2 ≤ t) :
    |Nfun t| ≤ (2 * Real.log (2*Real.pi) + 4 * βc) * Real.sqrt t := by
  have hβ := beta_nonneg hRH
  rw [Nfun_eq hRH t ht]
  have h1 := int_Istar_bounds hRH t ht
  have h2 := Ffun_abs hRH t (by linarith)
  have h3 := Ffun_abs hRH 2 (by norm_num)
  rw [rpow_half_eq t (by linarith)] at h2
  rw [rpow_half_eq 2 (by norm_num)] at h3
  have h4 : Real.sqrt 2 ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  have h5 := log_le_two_sqrt t (by linarith)
  have hl := log_two_pi_pos
  rw [abs_le] at h2 h3 ⊢
  constructor <;> nlinarith

lemma gg2_abs (t : ℝ) (ht : 2 ≤ t) : |gg2 t| ≤ 11 / (t * (Real.log t)^3) := by
  have hl2 := Real.log_two_gt_d9
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hL : 0.69 < Real.log t := by linarith
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < Real.log t := by linarith
  have e : gg2 t = (-2 + 6 / Real.log t) / (t * (Real.log t)^3) := by
    simp only [gg2]; field_simp
  rw [e, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 3)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 6 / Real.log t ≤ 9 := by rw [div_le_iff₀ hL0]; linarith
  have : 0 ≤ 6 / Real.log t := by positivity
  rw [abs_le]; constructor <;> linarith

noncomputable def w3 (t : ℝ) : ℝ := 1 / (Real.sqrt t * (Real.log t)^3)

lemma w3_contAt (t : ℝ) (ht : 1 < t) : ContinuousAt w3 t := by
  have ht0 : 0 < t := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
  have hd : Real.sqrt t * Real.log t ^ 3 ≠ 0 := by positivity
  have ht0' : t ≠ 0 := ht0.ne'
  unfold w3
  fun_prop (disch := assumption)

lemma int_inv_sqrt (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.sqrt t = 2 * Real.sqrt b - 2 * Real.sqrt a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * Real.sqrt t)
  · intro t ht; rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have := (Real.hasDerivAt_sqrt ht0.ne').const_mul 2
    refine this.congr_deriv ?_
    have : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    field_simp
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
    intro t ht; rw [Set.uIcc_of_le hab] at ht
    exact (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'

lemma int_w3_le (x : ℝ) (hx : 4 ≤ x) :
    ∫ t in (2:ℝ)..x, w3 t ≤
      2 * Real.sqrt (Real.sqrt x) / (Real.log 2)^3 + 16 * Real.sqrt x / (Real.log x)^3 := by
  set y := Real.sqrt x with hy
  have hy2 : 2 ≤ y := by
    rw [hy, show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hyx : y ≤ x := by
    rw [hy]; nth_rewrite 2 [← Real.sq_sqrt (show (0:ℝ) ≤ x by linarith)]
    nlinarith [Real.sqrt_nonneg x]
  have hw : ∀ a b, 2 ≤ a → a ≤ b → IntervalIntegrable w3 volume a b := fun a b ha hab =>
    (contOn_of_gt_one w3 w3_contAt a b (by linarith) (by linarith)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hw 2 y le_rfl hy2) (hw y x hy2 hyx)]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log x = 2 * Real.log y := by
    rw [hy, Real.log_sqrt (by linarith)]; ring
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hcs : ∀ a b, 0 < a → a ≤ b → IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
    intro t ht; rw [Set.uIcc_of_le hab] at ht
    exact (Real.sqrt_pos.mpr (by linarith [ht.1])).ne'
  have h1 : ∫ t in (2:ℝ)..y, w3 t ≤ ∫ t in (2:ℝ)..y, (1 / (Real.log 2)^3) * (1 / Real.sqrt t) := by
    apply intervalIntegral.integral_mono_on hy2 (hw 2 y le_rfl hy2) ((hcs 2 y (by norm_num) hy2).const_mul _)
    intro t ht
    have ht0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith [ht.1])
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
    simp only [w3]
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have : (Real.log 2)^3 ≤ (Real.log t)^3 := pow_le_pow_left₀ hl2.le hlt 3
    nlinarith
  have h2 : ∫ t in y..x, w3 t ≤ ∫ t in y..x, (1 / (Real.log y)^3) * (1 / Real.sqrt t) := by
    apply intervalIntegral.integral_mono_on hyx (hw y x hy2 hyx) ((hcs y x (by linarith) hyx).const_mul _)
    intro t ht
    have ht0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith [ht.1])
    have hlt : Real.log y ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    simp only [w3]
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have : (Real.log y)^3 ≤ (Real.log t)^3 := pow_le_pow_left₀ hly.le hlt 3
    nlinarith
  rw [intervalIntegral.integral_const_mul, int_inv_sqrt 2 y (by norm_num) hy2] at h1
  rw [intervalIntegral.integral_const_mul, int_inv_sqrt y x (by linarith) hyx] at h2
  have hsy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have e1 : 1 / Real.log 2 ^ 3 * (2 * Real.sqrt y - 2 * Real.sqrt 2) ≤ 2 * Real.sqrt y / Real.log 2 ^ 3 := by
    rw [div_mul_eq_mul_div, one_mul]
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have e2 : 1 / Real.log y ^ 3 * (2 * Real.sqrt x - 2 * Real.sqrt y) ≤ 16 * Real.sqrt x / Real.log x ^ 3 := by
    rw [hL, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hy0 : 0 ≤ y := by linarith
    have : (2 * Real.sqrt x - 2 * Real.sqrt y) * (2 * Real.log y)^3 = 8 * ((2 * Real.sqrt x - 2 * Real.sqrt y) * Real.log y ^ 3) := by ring
    rw [this]
    have : 0 ≤ Real.log y ^ 3 := by positivity
    nlinarith
  rw [← hy] at h2 e2
  linarith


lemma J1_decomp (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    J1 x = (x * SK x - Ffun x) / (Real.log x)^2 + 2 * Ffun x / (Real.log x)^3
      - Istar x * x / (Real.log x)^2
      + ((∫ t in (2:ℝ)..x, Istar t) + Ffun 2) * (1 / (Real.log x)^2 - 2 / (Real.log x)^3)
      + Mfun 2 * gg 2 - ∫ t in (2:ℝ)..x, Nfun t * gg2 t := by
  rw [J1_eq x hx, Nfun_eq hRH x hx]
  simp only [gg, gg1, Istar]
  ring

lemma int_Ngg2 (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    |∫ t in (2:ℝ)..x, Nfun t * gg2 t| ≤
      (11 * (2 * Real.log (2*Real.pi) + 4 * βc)) * ∫ t in (2:ℝ)..x, w3 t := by
  have hβ := beta_nonneg hRH
  have hl := log_two_pi_pos
  rw [← intervalIntegral.integral_const_mul]
  have hw : IntervalIntegrable (fun t => (11 * (2 * Real.log (2*Real.pi) + 4 * βc)) * w3 t) volume 2 x :=
    ((contOn_of_gt_one w3 w3_contAt 2 x (by norm_num) (by linarith)).intervalIntegrable).const_mul _
  have := intervalIntegral.norm_integral_le_of_norm_le hx (f := fun t => Nfun t * gg2 t)
    (g := fun t => (11 * (2 * Real.log (2*Real.pi) + 4 * βc)) * w3 t) ?_ hw
  · simpa [Real.norm_eq_abs] using this
  · refine Eventually.of_forall (fun t ht => ?_)
    have ht2 : 2 ≤ t := le_of_lt ht.1
    have h1 := Nfun_abs hRH t ht2
    have h2 := gg2_abs t ht2
    have ht0 : 0 < t := by linarith
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hL : 0 < Real.log t := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_mul]
    have hc : 0 ≤ 2 * Real.log (2*Real.pi) + 4 * βc := by positivity
    calc |Nfun t| * |gg2 t| ≤ ((2 * Real.log (2*Real.pi) + 4 * βc) * Real.sqrt t) * (11 / (t * (Real.log t)^3)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (11 * (2 * Real.log (2*Real.pi) + 4 * βc)) * w3 t := by
          have key : Real.sqrt t / t = 1 / Real.sqrt t := by
            rw [div_eq_div_iff ht0.ne' hs.ne', one_mul, Real.mul_self_sqrt ht0.le]
          simp only [w3]
          calc ((2 * Real.log (2*Real.pi) + 4 * βc) * Real.sqrt t) * (11 / (t * (Real.log t)^3))
              = 11 * (2 * Real.log (2*Real.pi) + 4 * βc) * ((Real.sqrt t / t) / (Real.log t)^3) := by
                field_simp
            _ = _ := by rw [key, div_div]

theorem J1_bound (hRH : RiemannHypothesis) : ∃ C : ℝ, ∀ x : ℝ, 4 ≤ x →
    |J1 x| ≤ βc * Real.sqrt x / (Real.log x)^2 +
      C * (Real.sqrt x / (Real.log x)^3 + Real.sqrt (Real.sqrt x) + 1) := by
  have hβ := beta_nonneg hRH
  have hl := log_two_pi_pos
  set C3 := 11 * (2 * Real.log (2*Real.pi) + 4 * βc) with hC3def
  have hC3 : 0 ≤ C3 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * βc + 16 * C3 + 4 * Real.log (2*Real.pi) + 9 * βc + |Mfun 2 * gg 2| + 2 * C3 / (Real.log 2)^3, ?_⟩
  intro x hx
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hx0 : 0 < x := by linarith
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hssx : 0 ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_nonneg _
  rw [J1_decomp hRH x (by linarith)]
  -- individual bounds
  have b1 : |(x * SK x - Ffun x) / L^2| ≤ βc * Real.sqrt x / L^2 := by
    have := xSK_sub_F hRH x (by linarith)
    rw [rpow_half_eq x hx0.le] at this
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < L^2)]
    exact div_le_div_of_nonneg_right this (by positivity)
  have b2 : |2 * Ffun x / L^3| ≤ 4 * βc * (Real.sqrt x / L^3) := by
    have := Ffun_abs hRH x hx0
    rw [rpow_half_eq x hx0.le] at this
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L^3), abs_two, mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity); linarith
  have b3 : |Istar x * x / L^2| ≤ Real.log (2*Real.pi) := by
    have h := Istar_bounds hRH x (by linarith)
    have h1 : Istar x * x ≤ Real.log (2*Real.pi) := by
      have := h.2; rw [le_div_iff₀ hx0] at this; linarith
    have h0 : 0 ≤ Istar x * x := mul_nonneg h.1 hx0.le
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : 1 ≤ L^2 := by nlinarith
    nlinarith
  have b4 : |((∫ t in (2:ℝ)..x, Istar t) + Ffun 2) * (1 / L^2 - 2 / L^3)| ≤
      3 * Real.log (2*Real.pi) + 9 * βc := by
    have hI := int_Istar_bounds hRH x (by linarith)
    rw [← hLdef] at hI
    have hF2 := Ffun_abs hRH 2 (by norm_num)
    rw [rpow_half_eq 2 (by norm_num)] at hF2
    have hs2 : Real.sqrt 2 < 1.5 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hA : |(∫ t in (2:ℝ)..x, Istar t) + Ffun 2| ≤ Real.log (2*Real.pi) * L + 3 * βc := by
      rw [abs_le] at hF2 ⊢; constructor <;> nlinarith
    have hB : |1 / L^2 - 2 / L^3| ≤ 3 / L^2 := by
      have h1 : 0 < 1 / L^2 := by positivity
      have h2 : 0 < 2 / L^3 := by positivity
      have h3 : 2 / L^3 ≤ 2 / L^2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
      rw [abs_le]; constructor
      · have : -(3 / L^2) = -(1/L^2) - 2/L^2 := by ring
        linarith
      · have : (3 / L^2) = 3 * (1/L^2) := by ring
        linarith
    rw [abs_mul]
    calc _ ≤ (Real.log (2*Real.pi) * L + 3 * βc) * (3 / L^2) :=
          mul_le_mul hA hB (abs_nonneg _) (by positivity)
      _ = 3 * Real.log (2*Real.pi) * (1 / L) + 9 * βc * (1 / L^2) := by field_simp; ring
      _ ≤ 3 * Real.log (2*Real.pi) * 1 + 9 * βc * 1 := by
          have : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; exact hL1
          have : 1 / L^2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
          gcongr
      _ = _ := by ring
  have b5 : |∫ t in (2:ℝ)..x, Nfun t * gg2 t| ≤
      2 * C3 / (Real.log 2)^3 * Real.sqrt (Real.sqrt x) + 16 * C3 * (Real.sqrt x / L^3) := by
    have h1 := int_Ngg2 hRH x (by linarith)
    have h2 := int_w3_le x hx
    rw [← hC3def] at h1
    have := mul_le_mul_of_nonneg_left h2 hC3
    have e : C3 * (2 * Real.sqrt (Real.sqrt x) / Real.log 2 ^ 3 + 16 * Real.sqrt x / L ^ 3) =
        2 * C3 / (Real.log 2)^3 * Real.sqrt (Real.sqrt x) + 16 * C3 * (Real.sqrt x / L^3) := by ring
    linarith
  rw [abs_le] at b1 b2 b3 b4 b5
  have hM := le_abs_self (Mfun 2 * gg 2)
  have hM' := neg_abs_le (Mfun 2 * gg 2)
  have hq : 0 ≤ Real.sqrt x / L^3 := by positivity
  have hfin : ∀ c : ℝ, 0 ≤ c → c * (Real.sqrt x / L^3) + c * Real.sqrt (Real.sqrt x) + c * 1 =
      c * (Real.sqrt x / L ^ 3 + Real.sqrt (Real.sqrt x) + 1) := fun c _ => by ring
  have hc1 : 0 ≤ 2 * C3 / (Real.log 2)^3 := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hβ hq, mul_nonneg hC3 hq, mul_nonneg hc1 hssx, abs_nonneg (Mfun 2 * gg 2),
      mul_nonneg (abs_nonneg (Mfun 2 * gg 2)) hq, mul_nonneg (abs_nonneg (Mfun 2 * gg 2)) hssx,
      mul_nonneg hl.le hq, mul_nonneg hl.le hssx, mul_nonneg hβ hssx, mul_nonneg hC3 hssx,
      mul_nonneg hc1 hq]
  · nlinarith [mul_nonneg hβ hq, mul_nonneg hC3 hq, mul_nonneg hc1 hssx, abs_nonneg (Mfun 2 * gg 2),
      mul_nonneg (abs_nonneg (Mfun 2 * gg 2)) hq, mul_nonneg (abs_nonneg (Mfun 2 * gg 2)) hssx,
      mul_nonneg hl.le hq, mul_nonneg hl.le hssx, mul_nonneg hβ hssx, mul_nonneg hC3 hssx,
      mul_nonneg hc1 hq]


/-! ## The prime-power part `J₂` -/

lemma psi_err (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
    |Chebyshev.psi y - y| ≤ 2 + C * Real.sqrt y * (Real.log y)^2 := by
  obtain ⟨C, hC⟩ := LandauCriterion.psi_error_of_riemannHypothesis hRH
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  rcases lt_or_ge y 2 with h | h
  · rw [Chebyshev.psi_eq_zero_of_lt_two h]
    have : 0 ≤ max C 0 * Real.sqrt y * (Real.log y)^2 := by
      have := le_max_right C 0; positivity
    rw [zero_sub, abs_neg, abs_of_nonneg hy]; linarith
  · have h1 := hC y h
    have : C * Real.sqrt y * (Real.log y)^2 ≤ max C 0 * Real.sqrt y * (Real.log y)^2 := by
      have : 0 ≤ Real.sqrt y * (Real.log y)^2 := by positivity
      nlinarith [le_max_left C 0]
    linarith

lemma sqrt_rpow_half (t : ℝ) (ht : 0 ≤ t) : t ^ (2:ℝ)⁻¹ = Real.sqrt t := by
  rw [Real.sqrt_eq_rpow]; norm_num

lemma psi_sub_theta_near (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    |Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t| ≤
      2 + C * Real.sqrt (Real.sqrt t) * (Real.log t)^2 + 2 * (Real.log 4 + 4) * t ^ (3:ℝ)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := psi_err hRH
  refine ⟨C / 4, by positivity, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hs := hC (Real.sqrt t) (Real.sqrt_nonneg t)
  rw [Real.log_sqrt ht0] at hs
  have e : C * Real.sqrt (Real.sqrt t) * (Real.log t / 2)^2 = C / 4 * Real.sqrt (Real.sqrt t) * (Real.log t)^2 := by ring
  rw [e] at hs
  have hup := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t
  have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi ht0
  rw [sqrt_rpow_half t ht0] at hup hlo
  have h3 : Chebyshev.psi (t ^ (3:ℝ)⁻¹) ≤ (Real.log 4 + 4) * t ^ (3:ℝ)⁻¹ :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have h5 : Chebyshev.psi (t ^ (5:ℝ)⁻¹) ≤ Chebyshev.psi (t ^ (3:ℝ)⁻¹) := by
    apply Chebyshev.psi_mono
    apply Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h0a := Chebyshev.psi_nonneg (t ^ (3:ℝ)⁻¹)
  have h0b := Chebyshev.psi_nonneg (t ^ (7:ℝ)⁻¹)
  rw [abs_le] at hs ⊢
  constructor <;> linarith

lemma int_inv_tlog2 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, 1 / (t * (Real.log t)^2) = 1 / Real.log 2 - 1 / Real.log x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(1 / Real.log t))
    (f' := fun t => 1 / (t * (Real.log t)^2)) (a := 2) (b := x)
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have := ((hasDerivAt_const t (1:ℝ)).div (Real.hasDerivAt_log ht0) hl).neg
      refine this.congr_deriv ?_
      field_simp
      ring)
    ((NicL.cont_inv_tlog 2 x (by norm_num) hx).intervalIntegrable)
  rw [h]; ring

lemma int_qrt (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, Real.sqrt (Real.sqrt t) / t = 4 * Real.sqrt (Real.sqrt x) - 4 * Real.sqrt (Real.sqrt 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 4 * Real.sqrt (Real.sqrt t))
  · intro t ht; rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hq : 0 < Real.sqrt (Real.sqrt t) := Real.sqrt_pos.mpr hs
    have h1 := Real.hasDerivAt_sqrt ht0.ne'
    have h2 := ((Real.hasDerivAt_sqrt hs.ne').comp t h1).const_mul 4
    refine h2.congr_deriv ?_
    have e1 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t := Real.sq_sqrt hs.le
    have e2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
    have key : Real.sqrt (Real.sqrt t) / t = 1 / (Real.sqrt (Real.sqrt t) * Real.sqrt t) := by
      rw [div_eq_div_iff ht0.ne' (by positivity)]
      linear_combination (Real.sqrt t) * e1 + e2
    rw [key]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (Real.continuous_sqrt.comp Real.continuous_sqrt).continuousOn continuousOn_id
    intro t ht; rw [Set.uIcc_of_le hx] at ht; simp only [id]; linarith [ht.1]


noncomputable def w2 (t : ℝ) : ℝ := 1 / (Real.sqrt t * (Real.log t)^2)

lemma int_w2 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, w2 t = 2 * Real.sqrt x / (Real.log x)^2 - 2 * Real.sqrt 2 / (Real.log 2)^2
      + 4 * ∫ t in (2:ℝ)..x, w3 t := by
  have hw3 : IntervalIntegrable w3 volume 2 x :=
    (contOn_of_gt_one w3 w3_contAt 2 x (by norm_num) (by linarith)).intervalIntegrable
  have hcw2 : ∀ t, 1 < t → ContinuousAt w2 t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hd : Real.sqrt t * Real.log t ^ 2 ≠ 0 := by positivity
    have ht0' : t ≠ 0 := ht0.ne'
    unfold w2
    fun_prop (disch := assumption)
  have hw2 : IntervalIntegrable w2 volume 2 x :=
    (contOn_of_gt_one w2 hcw2 2 x (by norm_num) (by linarith)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * Real.sqrt t / (Real.log t)^2)
    (f' := fun t => w2 t - 4 * w3 t) (a := 2) (b := x)
    (fun t ht => by
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have := ((Real.hasDerivAt_sqrt ht0.ne').const_mul 2).div
        ((Real.hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl)
      refine this.congr_deriv ?_
      have hti : t⁻¹ = (Real.sqrt t * Real.sqrt t)⁻¹ := by rw [Real.mul_self_sqrt ht0.le]
      simp only [w2, w3, Pi.pow_apply]
      rw [hti]
      field_simp
      ring)
    (hw2.sub (hw3.const_mul 4))
  rw [intervalIntegral.integral_sub hw2 (hw3.const_mul 4), intervalIntegral.integral_const_mul] at h
  linarith

lemma gJ2_contAt (C K0 t : ℝ) (ht : 1 < t) : ContinuousAt (fun t : ℝ => 2 * (1 / (t * (Real.log t)^2)) + C * (Real.sqrt (Real.sqrt t) / t)
    + (2 * K0 / (Real.log 2)^2) * t ^ ((3:ℝ)⁻¹ - 1)) t := by
  have ht0 : t ≠ 0 := (by linarith : (0:ℝ) < t).ne'
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
  have h1 : ContinuousAt (fun t : ℝ => 2 * (1 / (t * Real.log t ^ 2)) + C * (Real.sqrt (Real.sqrt t) / t)) t := by
    fun_prop (disch := assumption)
  have h3 : ContinuousAt (fun t : ℝ => t ^ ((3:ℝ)⁻¹ - 1)) t := Real.continuousAt_rpow_const t _ (Or.inl ht0)
  exact h1.add (continuousAt_const.mul h3)

noncomputable def J2 (x : ℝ) : ℝ :=
  ∫ t in (2:ℝ)..x, (Chebyshev.psi t - Chebyshev.theta t) / (t * (Real.log t)^2)

lemma int_rpow_23 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, t ^ ((3:ℝ)⁻¹ - 1) = 3 * (x ^ (3:ℝ)⁻¹ - 2 ^ (3:ℝ)⁻¹) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show (3:ℝ)⁻¹ - 1 + 1 = (3:ℝ)⁻¹ by ring]
  field_simp

theorem J2_bound (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ x : ℝ, 4 ≤ x →
    |J2 x - 2 * Real.sqrt x / (Real.log x)^2| ≤
      K * (Real.sqrt x / (Real.log x)^3 + Real.sqrt (Real.sqrt x) + x ^ (3:ℝ)⁻¹ + 1) := by
  obtain ⟨C, hC0, hC⟩ := psi_sub_theta_near hRH
  set K0 := Real.log 4 + 4 with hK0
  have hK0p : 0 < K0 := by have := Real.log_pos (show (1:ℝ) < 4 by norm_num); linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := 2 / Real.log 2 + 2 * Real.sqrt 2 / (Real.log 2)^2 + 8 / (Real.log 2)^3 + 4 * C
    + 6 * K0 / (Real.log 2)^2 + 64 with hK
  refine ⟨K, fun x hx => ?_⟩
  have hx2 : (2:ℝ) ≤ x := by linarith
  set g : ℝ → ℝ := fun t => 2 * (1 / (t * (Real.log t)^2)) + C * (Real.sqrt (Real.sqrt t) / t)
    + (2 * K0 / (Real.log 2)^2) * t ^ ((3:ℝ)⁻¹ - 1) with hg
  have hcg : ContinuousOn g (Set.uIcc 2 x) := by
    rw [hg]
    exact contOn_of_gt_one _ (fun t ht => gJ2_contAt C K0 t ht) 2 x (by norm_num) (by linarith)
  have hint_g : ∫ t in (2:ℝ)..x, g t ≤ 2 / Real.log 2 + 4 * C * Real.sqrt (Real.sqrt x)
      + 6 * K0 / (Real.log 2)^2 * x ^ (3:ℝ)⁻¹ := by
    have i1 : IntervalIntegrable (fun t : ℝ => 1 / (t * (Real.log t)^2)) volume 2 x :=
      (NicL.cont_inv_tlog 2 x (by norm_num) hx2).intervalIntegrable
    have i2 : IntervalIntegrable (fun t : ℝ => Real.sqrt (Real.sqrt t) / t) volume 2 x := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div (Real.continuous_sqrt.comp Real.continuous_sqrt).continuousOn continuousOn_id
      intro t ht; rw [Set.uIcc_of_le hx2] at ht; simp only [id]; linarith [ht.1]
    have i3 : IntervalIntegrable (fun t : ℝ => t ^ ((3:ℝ)⁻¹ - 1)) volume 2 x :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    simp only [hg]
    rw [intervalIntegral.integral_add ((i1.const_mul 2).add (i2.const_mul C)) (i3.const_mul _),
      intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul C),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, int_inv_tlog2 x hx2, int_qrt x hx2, int_rpow_23 x hx2]
    have hL : 0 < 1 / Real.log x := by have := Real.log_pos (show (1:ℝ) < x by linarith); positivity
    have h1 : 0 ≤ Real.sqrt (Real.sqrt 2) := Real.sqrt_nonneg _
    have h2 : 0 ≤ (2:ℝ) ^ (3:ℝ)⁻¹ := by positivity
    have h3 : 0 ≤ 2 * K0 / (Real.log 2)^2 := by positivity
    have e : 2 * K0 / Real.log 2 ^ 2 * (3 * (x ^ (3:ℝ)⁻¹ - 2 ^ (3:ℝ)⁻¹)) =
        6 * K0 / (Real.log 2)^2 * x ^ (3:ℝ)⁻¹ - 6 * K0 / (Real.log 2)^2 * 2 ^ (3:ℝ)⁻¹ := by ring
    have h4 : 0 ≤ 6 * K0 / (Real.log 2)^2 * 2 ^ (3:ℝ)⁻¹ := by positivity
    have k1 : 2 * (1 / Real.log 2 - 1 / Real.log x) ≤ 2 / Real.log 2 := by
      have : 2 / Real.log 2 = 2 * (1 / Real.log 2) := by ring
      linarith
    have k2 : C * (4 * Real.sqrt (Real.sqrt x) - 4 * Real.sqrt (Real.sqrt 2)) ≤ 4 * C * Real.sqrt (Real.sqrt x) := by
      nlinarith [mul_nonneg hC0 h1]
    rw [e]
    linarith
  -- the difference J2 - ∫ w2
  have hψi : IntervalIntegrable (fun t => (Chebyshev.psi t - Chebyshev.theta t) / (t * (Real.log t)^2)) volume 2 x := by
    refine (((psi_intervalIntegrable 2 x).sub (NicL.theta_intervalIntegrable 2 x)).mul_continuousOn
      (NicL.cont_inv_tlog 2 x (by norm_num) hx2)).congr ?_
    intro t _; ring
  have hcw2 : ∀ t, 1 < t → ContinuousAt w2 t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hd : Real.sqrt t * Real.log t ^ 2 ≠ 0 := by positivity
    have ht0' : t ≠ 0 := ht0.ne'
    unfold w2
    fun_prop (disch := assumption)
  have hw2 : IntervalIntegrable w2 volume 2 x :=
    (contOn_of_gt_one w2 hcw2 2 x (by norm_num) (by linarith)).intervalIntegrable
  have hdiff : J2 x - ∫ t in (2:ℝ)..x, w2 t =
      ∫ t in (2:ℝ)..x, (Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t) / (t * (Real.log t)^2) := by
    rw [J2, ← intervalIntegral.integral_sub hψi hw2]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx2] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have e : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have hL2 : 0 < Real.log t ^ 2 := by positivity
    have key : 1 / (Real.sqrt t * Real.log t ^ 2) = Real.sqrt t / (t * Real.log t ^ 2) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (-(Real.log t ^ 2)) * e
    simp only [w2]
    rw [key]
    ring
  have hbound : |∫ t in (2:ℝ)..x, (Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t) / (t * (Real.log t)^2)|
      ≤ ∫ t in (2:ℝ)..x, g t := by
    have := intervalIntegral.norm_integral_le_of_norm_le hx2
      (f := fun t => (Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t) / (t * (Real.log t)^2))
      (g := g) (μ := volume) ?_ (hcg.intervalIntegrable (μ := volume))
    · simpa [Real.norm_eq_abs] using this
    refine Eventually.of_forall (fun t ht => ?_)
    have ht2 : 2 ≤ t := le_of_lt ht.1
    have ht0 : 0 < t := by linarith
    have hL : 0 < Real.log t := Real.log_pos (by linarith)
    have hLt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have h := hC t ht2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < t * (Real.log t)^2)]
    have hr : t ^ (3:ℝ)⁻¹ / t = t ^ ((3:ℝ)⁻¹ - 1) := (Real.rpow_sub_one ht0.ne' _).symm
    have hrpos : 0 ≤ t ^ ((3:ℝ)⁻¹ - 1) := by positivity
    calc |Chebyshev.psi t - Chebyshev.theta t - Real.sqrt t| / (t * Real.log t ^ 2)
        ≤ (2 + C * Real.sqrt (Real.sqrt t) * (Real.log t)^2 + 2 * K0 * t ^ (3:ℝ)⁻¹) / (t * Real.log t ^ 2) :=
          div_le_div_of_nonneg_right h (by positivity)
      _ = 2 * (1 / (t * (Real.log t)^2)) + C * (Real.sqrt (Real.sqrt t) / t)
            + (2 * K0 / (Real.log t)^2) * (t ^ (3:ℝ)⁻¹ / t) := by
          field_simp
      _ ≤ g t := by
          simp only [hg]
          rw [hr]
          gcongr
  have hw := int_w2 x hx2
  have hw3 := int_w3_le x hx
  have hw3p : 0 ≤ ∫ t in (2:ℝ)..x, w3 t := by
    apply intervalIntegral.integral_nonneg hx2
    intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith [ht.1])
    simp only [w3]; positivity
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hssx : 0 ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_nonneg _
  have hcx : 0 ≤ x ^ (3:ℝ)⁻¹ := by positivity
  have hLx : 0 < Real.log x := Real.log_pos (by linarith)
  have hq : 0 ≤ Real.sqrt x / Real.log x ^ 3 := by positivity
  rw [abs_le] at hbound ⊢
  have hs2 : 0 ≤ 2 * Real.sqrt 2 / Real.log 2 ^ 2 := by positivity
  have hc8 : 0 ≤ 8 / Real.log 2 ^ 3 := by positivity
  have e3 : 4 * (2 * Real.sqrt (Real.sqrt x) / Real.log 2 ^ 3 + 16 * Real.sqrt x / Real.log x ^ 3) =
      8 / Real.log 2 ^ 3 * Real.sqrt (Real.sqrt x) + 64 * (Real.sqrt x / Real.log x ^ 3) := by ring
  have hK6 : 0 ≤ 6 * K0 / (Real.log 2)^2 := by positivity
  have hl22 : 0 ≤ 2 / Real.log 2 := by positivity
  constructor
  · nlinarith [mul_nonneg hl22 hq, mul_nonneg hs2 hq, mul_nonneg hc8 hq, mul_nonneg hC0 hq,
      mul_nonneg hK6 hq, mul_nonneg hl22 hssx, mul_nonneg hs2 hssx, mul_nonneg hC0 hssx,
      mul_nonneg hK6 hssx, mul_nonneg hl22 hcx, mul_nonneg hs2 hcx, mul_nonneg hc8 hcx,
      mul_nonneg hC0 hcx, mul_nonneg hc8 hssx]
  · nlinarith [mul_nonneg hl22 hq, mul_nonneg hs2 hq, mul_nonneg hc8 hq, mul_nonneg hC0 hq,
      mul_nonneg hK6 hq, mul_nonneg hl22 hssx, mul_nonneg hs2 hssx, mul_nonneg hC0 hssx,
      mul_nonneg hK6 hssx, mul_nonneg hl22 hcx, mul_nonneg hs2 hcx, mul_nonneg hc8 hcx,
      mul_nonneg hC0 hcx, mul_nonneg hc8 hssx]


/-! ## Assembly -/

lemma beta_eq : βc = 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2 := by
  unfold βc
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast; ring

noncomputable def Anorm (x : ℝ) : ℝ :=
  (NicL.li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x

lemma J12 (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, (t - Chebyshev.theta t) / (t * (Real.log t)^2) = J1 x + J2 x := by
  have hc := NicL.cont_inv_tlog 2 x (by norm_num) hx
  have i1 : IntervalIntegrable (fun t => (t - Chebyshev.psi t) / (t * (Real.log t)^2)) volume 2 x := by
    refine ((intervalIntegral.intervalIntegrable_id.sub (psi_intervalIntegrable 2 x)).mul_continuousOn hc).congr ?_
    intro t _; simp only [Pi.sub_apply, id]; ring
  have i2 : IntervalIntegrable (fun t => (Chebyshev.psi t - Chebyshev.theta t) / (t * (Real.log t)^2)) volume 2 x := by
    refine (((psi_intervalIntegrable 2 x).sub (NicL.theta_intervalIntegrable 2 x)).mul_continuousOn hc).congr ?_
    intro t _; ring
  rw [J1, J2, ← intervalIntegral.integral_add i1 i2]
  apply intervalIntegral.integral_congr
  intro t _; simp only; ring

lemma E2_bound (x δ : ℝ) (hx : 4 ≤ x) (hδ : |Chebyshev.theta x - x| ≤ δ) (hδx : δ ≤ x / 2) :
    |NicL.li (Chebyshev.theta x) - NicL.li x - (Chebyshev.theta x - x) / Real.log x| ≤
      8 * δ^2 / (x * (Real.log x)^2) := by
  have hθ : x / 2 ≤ Chebyshev.theta x := by rw [abs_le] at hδ; linarith
  have hT := NicL.li_taylor x (Chebyshev.theta x) (by linarith) (by linarith)
  set m := min x (Chebyshev.theta x) with hm
  have hm2 : x / 2 ≤ m := le_min (by linarith) hθ
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlm : Real.log x / 2 ≤ Real.log m := by
    have h1 : Real.log (x/2) ≤ Real.log m := Real.log_le_log (by linarith) hm2
    have h2 : Real.log x ≤ 2 * Real.log (x/2) := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log hx0
      rw [show (x/2) ^ (2:ℝ) = (x/2)^2 by norm_num]
      nlinarith
    linarith
  have hlm0 : 0 < Real.log m := by linarith
  have hden : x * (Real.log x)^2 / 8 ≤ m * (Real.log m)^2 := by
    have : (Real.log x / 2)^2 ≤ (Real.log m)^2 := pow_le_pow_left₀ (by positivity) hlm 2
    calc x * (Real.log x)^2 / 8 = (x/2) * (Real.log x / 2)^2 := by ring
      _ ≤ m * (Real.log m)^2 := mul_le_mul hm2 this (by positivity) (by linarith)
  have hsq : (Chebyshev.theta x - x)^2 ≤ δ^2 := by
    have := sq_abs (Chebyshev.theta x - x)
    rw [← this]
    exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  refine hT.trans ?_
  rw [div_le_div_iff₀ (mul_pos (by linarith) (pow_pos hlm0 2)) (mul_pos hx0 (pow_pos hlx 2))]
  have h0 : 0 ≤ (Chebyshev.theta x - x)^2 := sq_nonneg _
  have : (Chebyshev.theta x - x)^2 * (x * Real.log x ^ 2) ≤ δ^2 * (8 * (m * Real.log m ^ 2)) := by
    have := mul_le_mul hsq (by linarith : x * Real.log x ^ 2 ≤ 8 * (m * Real.log m ^ 2)) (by positivity) (by positivity)
    linarith
  linarith

lemma u_facts (x : ℝ) (hx : 0 < x) :
    Real.sqrt x = (x ^ (1/12:ℝ))^6 ∧ Real.sqrt (Real.sqrt x) = (x ^ (1/12:ℝ))^3 ∧
    x ^ (3:ℝ)⁻¹ = (x ^ (1/12:ℝ))^4 ∧ x ^ (1/6:ℝ) = (x ^ (1/12:ℝ))^2 := by
  have p : ∀ n : ℕ, (x ^ (1/12:ℝ))^n = x ^ ((n:ℝ)/12) := by
    intro n; rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p, Real.sqrt_eq_rpow]; norm_num
  · rw [p, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; norm_num
  · rw [p]; norm_num
  · rw [p]; norm_num

lemma final_alg (b K3 Cd L u : ℝ) (hL1 : 1 ≤ L) (hu1 : 1 ≤ u) (hK3p : 0 ≤ K3) :
    (b * u^6 / L^2 + K3 * (u^6 / L^3 + u^3 + u^4 + 1) + 8 * Cd^2 * L^2) * (L^2 / u^6) ≤
      b + (K3 + 3 * K3 + 8 * Cd^2) * (1 / L + L^4 / u^2) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have key : (b * u^6 / L^2 + K3 * (u^6 / L^3 + u^3 + u^4 + 1) + 8 * Cd^2 * L^2) * (L^2 / u^6)
      = b + K3 * (1 / L) + (K3 * (L^2 / u^3) + K3 * (L^2 / u^2) + K3 * (L^2 / u^6)) + 8 * Cd^2 * (L^4 / u^6) := by
    field_simp; ring
  rw [key]
  have hL24 : L^2 ≤ L^4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hu23 : u^2 ≤ u^3 := pow_le_pow_right₀ hu1 (by norm_num)
  have hu26 : u^2 ≤ u^6 := pow_le_pow_right₀ hu1 (by norm_num)
  have b1 : L^2 / u^3 ≤ L^4 / u^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul hL24 hu23 (by positivity) (by positivity)
  have b2 : L^2 / u^2 ≤ L^4 / u^2 := div_le_div_of_nonneg_right hL24 (by positivity)
  have b3 : L^2 / u^6 ≤ L^4 / u^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul hL24 hu26 (by positivity) (by positivity)
  have b4 : L^4 / u^6 ≤ L^4 / u^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hu26
  have hq1 : 0 ≤ 1 / L := by positivity
  have hq2 : 0 ≤ L^4 / u^2 := by positivity
  have m1 := mul_le_mul_of_nonneg_left b1 hK3p
  have m2 := mul_le_mul_of_nonneg_left b2 hK3p
  have m3 := mul_le_mul_of_nonneg_left b3 hK3p
  have m4 := mul_le_mul_of_nonneg_left b4 (by positivity : (0:ℝ) ≤ 8 * Cd^2)
  have m5 : 0 ≤ (3 * K3 + 8 * Cd^2) * (1 / L) := mul_nonneg (by positivity) hq1
  have m6 : 0 ≤ K3 * (L^4 / u^2) := mul_nonneg hK3p hq2
  have e : (K3 + 3 * K3 + 8 * Cd^2) * (1 / L + L^4 / u^2) =
      K3 * (1 / L) + (3 * K3 + 8 * Cd^2) * (1 / L) + 4 * (K3 * (L^4 / u^2)) + 8 * Cd^2 * (L^4 / u^2) := by ring
  rw [e]
  linarith

theorem A_bound (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ᶠ x in atTop,
    |Anorm x - 2| ≤ βc + K * (1 / Real.log x + (Real.log x)^4 / x ^ (1/6:ℝ)) := by
  obtain ⟨C1', hC1⟩ := J1_bound hRH
  obtain ⟨K2', hK2⟩ := J2_bound hRH
  obtain ⟨Cψ, hCψ0, hCψ⟩ := psi_err hRH
  set C1 := max C1' 0
  set K2 := max K2' 0
  have hC1p : 0 ≤ C1 := le_max_right _ _
  have hK2p : 0 ≤ K2 := le_max_right _ _
  set Cδ := Cψ + 4 with hCδ
  have hCδp : 0 < Cδ := by linarith
  set K0' := NicL.li 2 - 2 / Real.log 2
  set K3 := |K0'| + C1 + K2 with hK3
  have hK3p : 0 ≤ K3 := by positivity
  refine ⟨K3 + 3 * K3 + 8 * Cδ^2, ?_⟩
  -- eventually `Cδ √x L² ≤ x/2`
  have hlim : Tendsto (fun x : ℝ => (Real.log x)^2 / Real.sqrt x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
  have hev : ∀ᶠ x : ℝ in atTop, (Real.log x)^2 / Real.sqrt x ≤ 1 / (2 * Cδ) :=
    (tendsto_order.1 hlim).2 _ (by positivity) |>.mono (fun x h => h.le)
  filter_upwards [hev, eventually_ge_atTop 4] with x hev hx
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  have hsx1 : 1 ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  -- δ
  have hδ : |Chebyshev.theta x - x| ≤ Cδ * Real.sqrt x * L^2 := by
    have h1 := hCψ x hx0.le
    have h2 := Chebyshev.psi_sub_theta_le (show 1 ≤ x by linarith)
    have h3 := Chebyshev.theta_le_psi x
    have hL2 : L ≤ L^2 := by nlinarith
    have e1 : 2 ≤ 2 * Real.sqrt x * L^2 := by nlinarith
    have e2 : 2 * Real.sqrt x * L ≤ 2 * Real.sqrt x * L^2 := by nlinarith
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith
  have hδx : Cδ * Real.sqrt x * L^2 ≤ x / 2 := by
    rw [div_le_iff₀ hsx] at hev
    have hxs : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    have : L^2 * (2 * Cδ) ≤ Real.sqrt x := by
      have := hev; rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at this; linarith
    nlinarith
  have hE2 := E2_bound x _ hx hδ hδx
  have hE2' : |NicL.li (Chebyshev.theta x) - NicL.li x - (Chebyshev.theta x - x) / L| ≤ 8 * Cδ^2 * L^2 := by
    refine hE2.trans (le_of_eq ?_)
    have hlx : Real.log x = L := rfl
    rw [hlx]
    have hL0 : L ≠ 0 := by linarith
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0.le]
    field_simp
  -- decomposition
  have hD := NicL.D_decomp x (by linarith)
  rw [J12 x (by linarith)] at hD
  have hJ1 := hC1 x hx
  have hJ2 := hK2 x hx
  set P := Real.sqrt x / L^3
  set Q := Real.sqrt (Real.sqrt x)
  set R := x ^ (3:ℝ)⁻¹
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hR : 0 ≤ R := by positivity
  have hJ1' : |J1 x| ≤ βc * Real.sqrt x / L^2 + C1 * (P + Q + 1) :=
    hJ1.trans (by gcongr; exact le_max_left _ _)
  have hJ2' : |J2 x - 2 * Real.sqrt x / L^2| ≤ K2 * (P + Q + R + 1) :=
    hJ2.trans (by gcongr; exact le_max_left _ _)
  have hDb : |(NicL.li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) - 2 * Real.sqrt x / L^2| ≤
      βc * Real.sqrt x / L^2 + K3 * (P + Q + R + 1) + 8 * Cδ^2 * L^2 := by
    rw [hD]
    have e : K0' + (J1 x + J2 x) + (NicL.li (Chebyshev.theta x) - NicL.li x - (Chebyshev.theta x - x) / L)
        - 2 * Real.sqrt x / L^2 = K0' + J1 x + (J2 x - 2 * Real.sqrt x / L^2) +
          (NicL.li (Chebyshev.theta x) - NicL.li x - (Chebyshev.theta x - x) / L) := by ring
    rw [e]
    have hK0 := abs_nonneg K0'
    have t1 := abs_add_le (K0' + J1 x + (J2 x - 2 * Real.sqrt x / L^2))
      (NicL.li (Chebyshev.theta x) - NicL.li x - (Chebyshev.theta x - x) / L)
    have t2 := abs_add_le (K0' + J1 x) (J2 x - 2 * Real.sqrt x / L^2)
    have t3 := abs_add_le K0' (J1 x)
    have k1 : C1 * (P + Q + 1) ≤ C1 * (P + Q + R + 1) := mul_le_mul_of_nonneg_left (by linarith) hC1p
    have k2 : |K0'| ≤ |K0'| * (P + Q + R + 1) := by
      have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ P + Q + R + 1 by linarith) hK0
      linarith
    have k3 : K3 * (P + Q + R + 1) = |K0'| * (P + Q + R + 1) + C1 * (P + Q + R + 1) + K2 * (P + Q + R + 1) := by
      rw [hK3]; ring
    linarith
  -- normalize
  obtain ⟨hu6, hu3, hu4, hu2⟩ := u_facts x hx0
  set u := x ^ (1/12:ℝ) with hudef
  have hu0 : 0 < u := by positivity
  have hu1 : 1 ≤ u := Real.one_le_rpow (by linarith) (by norm_num)
  have hA : Anorm x - 2 = ((NicL.li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) -
      2 * Real.sqrt x / L^2) * (L^2 / Real.sqrt x) := by
    simp only [Anorm]; rw [← hLdef]
    have hL0 : L ≠ 0 := by linarith
    field_simp
  rw [hA, abs_mul, abs_of_pos (by positivity : 0 < L^2 / Real.sqrt x)]
  have hpos : 0 ≤ L^2 / Real.sqrt x := by positivity
  refine (mul_le_mul_of_nonneg_right hDb hpos).trans ?_
  rw [hu2]
  have hQ' : Q = u^3 := hu3
  have hR' : R = u^4 := hu4
  have hS : Real.sqrt x = u^6 := hu6
  have hP' : P = u^6 / L^3 := by simp only [P]; rw [hS]
  rw [hP', hQ', hR', hS]
  exact final_alg βc K3 Cδ L u (by linarith) hu1 hK3p

lemma err_tendsto (K : ℝ) :
    Tendsto (fun x : ℝ => K * (1 / Real.log x + (Real.log x)^4 / x ^ (1/6:ℝ))) atTop (𝓝 0) := by
  have t1 : Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have t2 : Tendsto (fun x : ℝ => (Real.log x)^4 / x ^ (1/6:ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (show (0:ℝ) < 1/6 by norm_num)).tendsto_div_nhds_zero
    refine h.congr' (Eventually.of_forall (fun x => ?_))
    simp only
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simpa using (t1.add t2).const_mul K

theorem limsup_of_RH (hRH : RiemannHypothesis) :
    Filter.limsup (fun x : ℝ => (Anorm x : EReal)) atTop ≤ ((2 + βc : ℝ) : EReal) := by
  obtain ⟨K, hK⟩ := A_bound hRH
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have hz' : 2 + βc < z := by exact_mod_cast hz
  have hev := (tendsto_order.1 (err_tendsto K)).2 (z - (2 + βc)) (by linarith)
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hK, hev] with x h1 h2
  have : Anorm x ≤ z := by rw [abs_le] at h1; linarith
  exact_mod_cast this

theorem liminf_of_RH (hRH : RiemannHypothesis) :
    ((2 - βc : ℝ) : EReal) ≤ Filter.liminf (fun x : ℝ => (Anorm x : EReal)) atTop := by
  obtain ⟨K, hK⟩ := A_bound hRH
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro z hz
  have hz' : z < 2 - βc := by exact_mod_cast hz
  have hev := (tendsto_order.1 (err_tendsto K)).2 ((2 - βc) - z) (by linarith)
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [hK, hev] with x h1 h2
  have : z ≤ Anorm x := by rw [abs_le] at h1; linarith
  exact_mod_cast this

end NicS

theorem solution :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    Filter.limsup (fun x : ℝ => (A x : EReal)) Filter.atTop ≤ ((2 + β : ℝ) : EReal) := by
  intro li A β
  have h := NicS.limsup_of_RH riemann_hypothesis
  rw [NicS.beta_eq] at h
  exact h
