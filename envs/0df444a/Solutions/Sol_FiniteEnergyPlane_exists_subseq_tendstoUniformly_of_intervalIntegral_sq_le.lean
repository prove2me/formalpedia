-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T23:31:12.898444+00:00
-- url     : https://prove2.me/submissions/c025adb9-4765-4f6d-8cd1-44a2cc8fa65e

import Mathlib
import Theorems.Thm_TeschlODE_IVP_arzela_ascoli

open MeasureTheory Filter Topology
open Set Filter MeasureTheory Topology

/-! Uniform subconvergence of periodic loops with `L²`-bounded values and derivatives. -/


namespace FiniteEnergyPlane.HCC1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Cauchy–Schwarz on an interval. -/
lemma cs1 {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have hL : 0 < b - a := by linarith
  have hg' : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  set I := ∫ x in a..b, g x
  set m := I / (b - a)
  have i1 : IntervalIntegrable (fun x => g x ^ 2) volume a b := (hg'.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun x => 2 * m * g x) volume a b :=
    (continuousOn_const.mul hg').intervalIntegrable
  have h0 : 0 ≤ ∫ x in a..b, (g x ^ 2 - 2 * m * g x + m ^ 2) :=
    intervalIntegral.integral_nonneg hab fun x _ => by nlinarith [sq_nonneg (g x - m)]
  rw [intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at h0
  have hm : m * (b - a) = I := by simp only [m]; field_simp
  nlinarith

/-- oscillation of a `C¹` function by the `L²` norm of its derivative -/
lemma osc_sq {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {s t : ℝ} (hst : s ≤ t) :
    ‖f t - f s‖ ^ 2 ≤ (t - s) * ∫ x in s..t, ‖f' x‖ ^ 2 := by
  have h1 : f t - f s = ∫ x in s..t, f' x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hf'.intervalIntegrable _ _)).symm
  rw [h1]
  have h2 : ‖∫ x in s..t, f' x‖ ≤ ∫ x in s..t, ‖f' x‖ :=
    intervalIntegral.norm_integral_le_integral_norm hst
  have h3 := cs1 hst hf'.norm.continuousOn
  have h0 := norm_nonneg (∫ x in s..t, f' x)
  nlinarith

/-- oscillation on `[0, 1]` -/
lemma osc01 {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {B : ℝ} (hB : ∫ t in (0:ℝ)..1, ‖f' t‖ ^ 2 ≤ B) :
    ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, ‖f t - f s‖ ^ 2 ≤ |t - s| * B := by
  have key : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, s ≤ t →
      ‖f t - f s‖ ^ 2 ≤ |t - s| * B := by
    intro s hs t ht hst
    have h1 := osc_sq hf hf' hst
    have h2 : ∫ x in s..t, ‖f' x‖ ^ 2 ≤ ∫ x in (0:ℝ)..1, ‖f' x‖ ^ 2 :=
      intervalIntegral.integral_mono_interval hs.1 hst ht.2
        (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
        ((hf'.norm.pow 2).intervalIntegrable _ _)
    rw [abs_of_nonneg (by linarith)]
    have : 0 ≤ t - s := by linarith
    calc ‖f t - f s‖ ^ 2 ≤ (t - s) * ∫ x in s..t, ‖f' x‖ ^ 2 := h1
      _ ≤ (t - s) * B := mul_le_mul_of_nonneg_left (h2.trans hB) this
  intro s hs t ht
  rcases le_total s t with h | h
  · exact key s hs t ht h
  · rw [norm_sub_rev, abs_sub_comm]; exact key t ht s hs h

/-- pointwise bound on `[0, 1]` -/
lemma sup01 {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {A B : ℝ} (hA : ∫ t in (0:ℝ)..1, ‖f t‖ ^ 2 ≤ A) (hB : ∫ t in (0:ℝ)..1, ‖f' t‖ ^ 2 ≤ B) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ^ 2 ≤ 2 * A + 2 * B := by
  intro t ht
  have hc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hpt : ∀ s ∈ Icc (0:ℝ) 1, ‖f t‖ ^ 2 ≤ 2 * ‖f s‖ ^ 2 + 2 * B := by
    intro s hs
    have h1 := osc01 hf hf' hB s hs t ht
    have h2 : |t - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    have hB0 : 0 ≤ B := le_trans (intervalIntegral.integral_nonneg zero_le_one
      fun x _ => by positivity) hB
    have h3 : ‖f t‖ ≤ ‖f s‖ + ‖f t - f s‖ := norm_le_norm_add_norm_sub' _ _
    have h4 : |t - s| * B ≤ B := by nlinarith [abs_nonneg (t - s)]
    have h5 : ‖f t‖ ^ 2 ≤ (‖f s‖ + ‖f t - f s‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (‖f s‖ - ‖f t - f s‖)]
  have hc2 : Continuous fun x => 2 * ‖f x‖ ^ 2 := by fun_prop
  have hint : ∫ _ in (0:ℝ)..1, ‖f t‖ ^ 2 ≤ ∫ x in (0:ℝ)..1, (2 * ‖f x‖ ^ 2 + 2 * B) :=
    intervalIntegral.integral_mono_on (zero_le_one' ℝ) intervalIntegrable_const
      ((hc2.add continuous_const).intervalIntegrable 0 1) hpt
  have e1 : ∫ x in (0:ℝ)..1, (2 * ‖f x‖ ^ 2 + 2 * B) =
      2 * (∫ x in (0:ℝ)..1, ‖f x‖ ^ 2) + 2 * B := by
    rw [intervalIntegral.integral_add (f := fun x => 2 * ‖f x‖ ^ 2) (g := fun _ => 2 * B)
      (hc2.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    simp
  have e2 : ∫ _ in (0:ℝ)..1, ‖f t‖ ^ 2 = ‖f t‖ ^ 2 := by simp
  rw [e1, e2] at hint
  linarith

theorem exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le_aux
    {ι : Type*} [Fintype ι]
    (f f' : ℕ → ℝ → EuclideanSpace ℝ ι) (hf : ∀ k t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ k, Continuous (f' k)) (hper : ∀ k, Function.Periodic (f k) 1)
    (A B : ℝ) (hA : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 ≤ A)
    (hB : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → EuclideanSpace ℝ ι,
      TendstoUniformly (fun k => f (φ k)) e atTop := by
  let T : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  have hc : ∀ k, Continuous (f k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hf k t).continuousAt
  have hB0 : 0 ≤ B := le_trans (intervalIntegral.integral_nonneg zero_le_one
    fun x _ => by positivity) (hB 0)
  obtain ⟨φ, hφ, y, hy⟩ := TeschlODE.IVP.arzela_ascoli 0 1 (fun k t => T (f k t))
    (fun k => (T.continuous.comp (hc k)).continuousOn)
    (by
      intro ε hε
      refine ⟨ε ^ 2 / (B + 1), by positivity, fun m t ht s hs hts => ?_⟩
      rw [← map_sub, T.norm_map]
      have h1 := osc01 (hf m) (hf' m) (hB m) s hs t ht
      have h2 : |t - s| * B ≤ ε ^ 2 := by
        have : ε ^ 2 / (B + 1) * B ≤ ε ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg ε]
        nlinarith [abs_nonneg (t - s)]
      nlinarith [norm_nonneg (f m t - f m s)])
    ⟨2 * A + 2 * B + 1, fun m t ht => by
      rw [T.norm_map]
      have := sup01 (hf m) (hf' m) (hA m) (hB m) t ht
      nlinarith [norm_nonneg (f m t)]⟩
  refine ⟨φ, hφ, fun t => T.symm (y (Int.fract t)), ?_⟩
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformlyOn_iff] at hy
  intro ε hε
  filter_upwards [hy ε hε] with k hk t
  have hfr : f (φ k) (Int.fract t) = f (φ k) t := by
    have := (hper (φ k)).sub_int_mul_eq (x := t) ⌊t⌋
    rwa [mul_one, Int.self_sub_floor] at this
  have hmem : Int.fract t ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have := hk _ hmem
  rw [← T.dist_map, T.apply_symm_apply, ← hfr]
  exact this

end FiniteEnergyPlane.HCC1

open FiniteEnergyPlane

theorem solution
    {ι : Type*} [Fintype ι]
    (f f' : ℕ → ℝ → EuclideanSpace ℝ ι) (hf : ∀ k t, HasDerivAt (f k) (f' k t) t)
    (hf' : ∀ k, Continuous (f' k)) (hper : ∀ k, Function.Periodic (f k) 1)
    (A B : ℝ) (hA : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 ≤ A)
    (hB : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → EuclideanSpace ℝ ι,
      TendstoUniformly (fun k => f (φ k)) e atTop :=
  HCC1.exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le_aux f f' hf hf' hper A B hA hB
