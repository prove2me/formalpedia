-- Prove2me | solution 1 for FiniteEnergyPlane.exists_subseq_tendstoUniformly_isLoopEigen
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T23:40:35.222027+00:00
-- url     : https://prove2.me/submissions/691d32cc-6655-47c4-92e9-aee3ac17f38d

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
import Theorems.Thm_FiniteEnergyPlane_contDiff_of_hasDerivAt_clm_apply

open scoped Topology ContDiff RealInnerProductSpace
open Set Filter CauchyRiemannIndex MeasureTheory
open scoped Interval

/-! Elementary facts for loops: `J₀² = -1`, interval Cauchy–Schwarz, oscillation bounds. -/


namespace HCC

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

lemma J_sq (x : Vec n) :
    Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (J₀ n) x) = -x := by
  have h : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n) (J₀ n)) *
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n) (J₀ n)) = -1 := by
    rw [← map_mul, J₀, Matrix.J_squared, map_neg, map_one]
  have := congrArg (fun T : Op n => T x) h
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.one_apply] at this
  exact this

lemma TL_eq_sum (M : Mat n) :
    TL n M = ∑ i, ∑ j, M i j • TL n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul]
  congr 1
  ext a b
  simp [Matrix.single_apply]

lemma contDiff_TL {k : WithTop ℕ∞} (S : ℝ → Mat n)
    (hS : ∀ i j, ContDiff ℝ k (fun t => S t i j)) :
    ContDiff ℝ k (fun t => TL n (S t)) := by
  have : (fun t => TL n (S t)) = fun t => ∑ i, ∑ j, S t i j • TL n (Matrix.single i j 1) := by
    funext t; exact TL_eq_sum _
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hS i j).smul contDiff_const

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
lemma osc_sq {f f' : ℝ → Vec n} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
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

/-- derivatives of periodic functions are periodic -/
lemma deriv_periodic {f f' : ℝ → Vec n} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hper : Function.Periodic f 1) : Function.Periodic f' 1 := fun t => by
  have h1 : HasDerivAt (fun x => f (x + 1)) (f' (t + 1)) t := by
    have := (hf (t + 1)).comp_add_const t 1
    exact this
  have h2 : (fun x => f (x + 1)) = f := funext fun x => hper x
  rw [h2] at h1
  exact h1.unique (hf t)

end HCC

/-! Normalized approximate loop eigenfunctions subconverge uniformly to an eigenfunction. -/


namespace HCC

variable {n : ℕ}

lemma JJ (x : Vec n) : TL n (J₀ n) (TL n (J₀ n) x) = -x := J_sq x

theorem exists_subseq_tendstoUniformly_isLoopEigen_aux (Sinf : ℝ → Mat n)
    (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) (f f' : ℕ → ℝ → Vec n)
    (hf : ∀ k t, HasDerivAt (f k) (f' k t) t) (hf' : ∀ k, Continuous (f' k))
    (hper : ∀ k, Function.Periodic (f k) 1)
    (hnorm : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 = 1)
    (hres : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      ‖-(Matrix.toEuclideanLin (J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → Vec n, FiniteEnergyPlane.IsLoopEigen Sinf μ e ∧
      TendstoUniformly (fun k => f (φ k)) e atTop := by
  set Jc : Op n := TL n (J₀ n) with hJc
  set cJ := ‖Jc‖
  have hcJ : 0 ≤ cJ := norm_nonneg _
  -- the operator loop
  have hAs : ContDiff ℝ ∞ (fun t => TL n (Sinf t)) := contDiff_TL Sinf hSinf'
  have hAc : Continuous (fun t => TL n (Sinf t)) := hAs.continuous
  have hAper : Function.Periodic (fun t => TL n (Sinf t)) 1 := fun t => by
    simp only [hSinf.2.1 t]
  obtain ⟨K, hK⟩ := (hAper.compact_of_continuous one_ne_zero hAc).isBounded.exists_norm_le
  have hK' : ∀ t, ‖TL n (Sinf t)‖ ≤ K := fun t => hK _ ⟨t, rfl⟩
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK' 0)
  set Bop : ℝ → Op n := fun x => Jc.comp (TL n (Sinf x) + μ • ContinuousLinearMap.id ℝ (Vec n))
    with hBop_def
  have hBs : ContDiff ℝ ∞ Bop := contDiff_const.clm_comp (hAs.add contDiff_const)
  have hBc : Continuous Bop := hBs.continuous
  set CB := cJ * (K + |μ|)
  have hCB : 0 ≤ CB := mul_nonneg hcJ (by positivity)
  have hBn : ∀ x, ‖Bop x‖ ≤ CB := fun x => by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hcJ)
    refine (norm_add_le _ _).trans (add_le_add (hK' x) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  have hBapp : ∀ x v, Bop x v = Jc (TL n (Sinf x) v + μ • v) := fun x v => by
    simp [hBop_def]
  -- residuals
  set ρ : ℕ → ℝ → Vec n := fun k t => -(Jc (f' k t)) - TL n (Sinf t) (f k t) - μ • f k t
    with hρ_def
  set r : ℕ → ℝ := fun k => ∫ t in (0:ℝ)..1, ‖ρ k t‖ ^ 2 with hr_def
  have hres' : Tendsto r atTop (𝓝 0) := hres
  have hc : ∀ k, Continuous (f k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hf k t).continuousAt
  have hρc : ∀ k, Continuous (ρ k) := fun k =>
    ((Jc.continuous.comp (hf' k)).neg.sub (hAc.clm_apply (hc k))).sub
      ((continuous_const (y := μ)).smul (hc k))
  have hid : ∀ k t, f' k t = Jc (ρ k t) + Bop t (f k t) := fun k t => by
    rw [hBapp, ← map_add]
    have : ρ k t + (TL n (Sinf t) (f k t) + μ • f k t) = -(Jc (f' k t)) := by
      simp only [hρ_def]; abel
    rw [this, map_neg, hJc, JJ, neg_neg]
  -- derivative bound
  obtain ⟨R, hR⟩ := hres'.bddAbove_range
  have hrR : ∀ k, r k ≤ R := fun k => hR ⟨k, rfl⟩
  have hpt : ∀ k t, ‖f' k t‖ ^ 2 ≤ 2 * cJ ^ 2 * ‖ρ k t‖ ^ 2 + 2 * CB ^ 2 * ‖f k t‖ ^ 2 :=
    fun k t => by
    have h1 : ‖f' k t‖ ≤ cJ * ‖ρ k t‖ + CB * ‖f k t‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (Jc.le_opNorm _)
        ((Bop t).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hBn t) (norm_nonneg _))))
    have h2 : ‖f' k t‖ ^ 2 ≤ (cJ * ‖ρ k t‖ + CB * ‖f k t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (cJ * ‖ρ k t‖ - CB * ‖f k t‖)]
  have hdB : ∀ k, ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤ 2 * cJ ^ 2 * R + 2 * CB ^ 2 := fun k => by
    have hcρ : Continuous fun t => 2 * cJ ^ 2 * ‖ρ k t‖ ^ 2 := by
      have := (hρc k).norm.pow 2; fun_prop
    have hcf : Continuous fun t => 2 * CB ^ 2 * ‖f k t‖ ^ 2 := by
      have := (hc k).norm.pow 2; fun_prop
    have hm : ∫ t in (0:ℝ)..1, ‖f' k t‖ ^ 2 ≤
        ∫ t in (0:ℝ)..1, (2 * cJ ^ 2 * ‖ρ k t‖ ^ 2 + 2 * CB ^ 2 * ‖f k t‖ ^ 2) :=
      intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      (((hf' k).norm.pow 2).intervalIntegrable 0 1) ((hcρ.add hcf).intervalIntegrable 0 1)
      (fun t _ => hpt k t)
    rw [intervalIntegral.integral_add (hcρ.intervalIntegrable _ _) (hcf.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hnorm k] at hm
    have : 2 * cJ ^ 2 * r k ≤ 2 * cJ ^ 2 * R := mul_le_mul_of_nonneg_left (hrR k) (by positivity)
    simp only [hr_def] at this
    linarith
  -- compactness
  obtain ⟨φ, hφ, e, he⟩ := FiniteEnergyPlane.exists_subseq_tendstoUniformly_of_intervalIntegral_sq_le
    f f' hf hf' hper 1 _ (fun k => (hnorm k).le) hdB
  have hec : Continuous e := he.continuous (Frequently.of_forall fun k => hc (φ k))
  have hept : ∀ t, Tendsto (fun k => f (φ k) t) atTop (𝓝 (e t)) := fun t => he.tendsto_at t
  have heper : Function.Periodic e 1 := fun t => by
    refine tendsto_nhds_unique (hept (t + 1)) ?_
    have : (fun k => f (φ k) (t + 1)) = fun k => f (φ k) t := funext fun k => hper _ t
    rw [this]; exact hept t
  set G : ℝ → Vec n := fun x => Bop x (e x) with hG_def
  have hGc : Continuous G := hBc.clm_apply hec
  -- periodic residual norms
  have hρper : ∀ k, Function.Periodic (fun t => ‖ρ k t‖) 1 := fun k t => by
    have h1 := deriv_periodic (hf k) (hper k) t
    simp only [hρ_def, h1, hper k t, hSinf.2.1 t]
  have hρL1 : ∀ k a t, a ≤ t → t ≤ a + 1 → ∫ x in a..t, ‖ρ k x‖ ≤ Real.sqrt (r k) := by
    intro k a t hat hta
    have h1 : ∫ x in a..t, ‖ρ k x‖ ≤ ∫ x in a..a + 1, ‖ρ k x‖ :=
      intervalIntegral.integral_mono_interval le_rfl hat hta
        (Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
        ((hρc k).norm.intervalIntegrable _ _)
    have h2 : ∫ x in a..a + 1, ‖ρ k x‖ = ∫ x in (0:ℝ)..0 + 1, ‖ρ k x‖ :=
      (hρper k).intervalIntegral_add_eq a 0
    rw [zero_add] at h2
    have h3 := cs1 (zero_le_one' ℝ) (hρc k).norm.continuousOn
    rw [sub_zero, one_mul] at h3
    have h4 : ∫ x in (0:ℝ)..1, ‖ρ k x‖ ≤ Real.sqrt (r k) :=
      (le_abs_self _).trans (Real.abs_le_sqrt h3)
    linarith
  -- the limit identity
  have hlim : ∀ a t, a ≤ t → t ≤ a + 1 → e t - e a = ∫ x in a..t, G x := by
    intro a t hat hta
    have hsplit : ∀ k, f (φ k) t - f (φ k) a =
        (∫ x in a..t, Jc (ρ (φ k) x)) + ∫ x in a..t, Bop x (f (φ k) x) := fun k => by
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf (φ k) x)
        ((hf' _).intervalIntegrable _ _)]
      exact (intervalIntegral.integral_congr fun x _ => hid _ x).trans
        (intervalIntegral.integral_add ((Jc.continuous.comp (hρc _)).intervalIntegrable _ _)
          ((hBc.clm_apply (hc _)).intervalIntegrable _ _))
    have T1 : Tendsto (fun k => ∫ x in a..t, Jc (ρ (φ k) x)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun k => cJ * Real.sqrt (r (φ k))) atTop (𝓝 0) := by
        have := ((hres'.comp hφ.tendsto_atTop).sqrt).const_mul cJ
        simpa using this
      refine squeeze_zero_norm (fun k => ?_) hsq
      calc ‖∫ x in a..t, Jc (ρ (φ k) x)‖ ≤ ∫ x in a..t, ‖Jc (ρ (φ k) x)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hat
        _ ≤ ∫ x in a..t, cJ * ‖ρ (φ k) x‖ :=
            intervalIntegral.integral_mono_on hat
              ((Jc.continuous.comp (hρc _)).norm.intervalIntegrable _ _)
              ((continuous_const.mul (hρc _).norm).intervalIntegrable _ _)
              (fun x _ => Jc.le_opNorm _)
        _ = cJ * ∫ x in a..t, ‖ρ (φ k) x‖ := intervalIntegral.integral_const_mul _ _
        _ ≤ cJ * Real.sqrt (r (φ k)) :=
            mul_le_mul_of_nonneg_left (hρL1 _ a t hat hta) hcJ
    have T2 : Tendsto (fun k => ∫ x in a..t, Bop x (f (φ k) x)) atTop
        (𝓝 (∫ x in a..t, G x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hη : 0 < ε / (CB + 1) / 2 := by positivity
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformly_iff.1 he) _ hη)
      refine ⟨N, fun k hk => ?_⟩
      rw [dist_eq_norm, ← intervalIntegral.integral_sub
        ((hBc.clm_apply (hc _)).intervalIntegrable _ _) (hGc.intervalIntegrable _ _)]
      have hb : ∀ x ∈ Ι a t, ‖Bop x (f (φ k) x) - G x‖ ≤ CB * (ε / (CB + 1) / 2) := by
        intro x _
        rw [hG_def, ← map_sub]
        refine ((Bop x).le_opNorm _).trans (mul_le_mul (hBn x) ?_ (norm_nonneg _) hCB)
        have := hN k hk x
        rw [dist_eq_norm, norm_sub_rev] at this
        exact this.le
      refine lt_of_le_of_lt (intervalIntegral.norm_integral_le_of_norm_le_const hb) ?_
      have hta' : |t - a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h1 : CB * (ε / (CB + 1) / 2) < ε := by
        have h0 : CB * (ε / (CB + 1)) ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
        have h0' : CB * (ε / (CB + 1) / 2) = CB * (ε / (CB + 1)) / 2 := by ring
        rw [h0']; linarith
      calc CB * (ε / (CB + 1) / 2) * |t - a| ≤ CB * (ε / (CB + 1) / 2) * 1 :=
            mul_le_mul_of_nonneg_left hta' (by positivity)
        _ < ε := by rw [mul_one]; exact h1
    have T3 : Tendsto (fun k => f (φ k) t - f (φ k) a) atTop (𝓝 (0 + ∫ x in a..t, G x)) := by
      rw [funext hsplit]; exact T1.add T2
    rw [zero_add] at T3
    exact tendsto_nhds_unique ((hept t).sub (hept a)) T3
  -- derivative of the limit
  have hd : ∀ t, HasDerivAt e (G t) t := fun t => by
    set a := t - 1 / 2
    have h1 : HasDerivAt (fun u => e a + ∫ x in a..u, G x) (G t) t :=
      (hGc.integral_hasStrictDerivAt a t).hasDerivAt.const_add (e a)
    refine h1.congr_of_eventuallyEq ?_
    have hmem : Ioo a (a + 1) ∈ 𝓝 t := Ioo_mem_nhds (by simp only [a]; linarith) (by simp only [a]; linarith)
    filter_upwards [hmem] with u hu
    have := hlim a u hu.1.le hu.2.le
    rw [sub_eq_iff_eq_add'] at this
    exact this
  have hderiv : ∀ t, deriv e t = G t := fun t => (hd t).deriv
  refine ⟨φ, hφ, e, ⟨?_, heper, ?_, fun t => ?_⟩, he⟩
  · exact FiniteEnergyPlane.contDiff_of_hasDerivAt_clm_apply Bop hBs e hd
  · by_contra hz
    push_neg at hz
    obtain ⟨k, hk⟩ := ((Metric.tendstoUniformly_iff.1 he) (1 / 2) (by norm_num)).exists
    have hsm : ∀ x ∈ Icc (0:ℝ) 1, ‖f (φ k) x‖ ^ 2 ≤ 1 / 4 := fun x _ => by
      have := hk x
      rw [hz x, dist_zero_left] at this
      nlinarith [norm_nonneg (f (φ k) x)]
    have hm : ∫ x in (0:ℝ)..1, ‖f (φ k) x‖ ^ 2 ≤ ∫ _ in (0:ℝ)..1, (1:ℝ) / 4 :=
      intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      (((hc (φ k)).norm.pow 2).intervalIntegrable 0 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (1:ℝ) / 4) volume 0 1) hsm
    rw [hnorm, intervalIntegral.integral_const] at hm
    norm_num at hm
  · show -(Jc (deriv e t)) - TL n (Sinf t) (e t) = μ • e t
    rw [hderiv, hG_def]
    simp only
    rw [hBapp, hJc, JJ, neg_neg]
    abel

end HCC

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) (f f' : ℕ → ℝ → CauchyRiemannIndex.Vec n)
    (hf : ∀ k t, HasDerivAt (f k) (f' k t) t) (hf' : ∀ k, Continuous (f' k))
    (hper : ∀ k, Function.Periodic (f k) 1)
    (hnorm : ∀ k, ∫ t in (0:ℝ)..1, ‖f k t‖ ^ 2 = 1)
    (hres : Tendsto (fun k => ∫ t in (0:ℝ)..1,
      ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (f' k t)) -
        Matrix.toEuclideanLin (Sinf t) (f k t) - μ • f k t‖ ^ 2) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoUniformly (fun k => f (φ k)) e atTop :=
  HCC.exists_subseq_tendstoUniformly_isLoopEigen_aux Sinf hSinf hSinf' μ f f' hf hf' hper hnorm hres
