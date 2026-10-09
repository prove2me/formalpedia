-- Prove2me | solution 1 for GaussianMatrix.gaussian_lipschitz_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:52:52.498516+00:00
-- url     : https://prove2.me/submissions/0dde6a3a-699f-4acb-a9e8-e28da4c2442b

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gaussian_logsobolev
import Theorems.Thm_GaussianMatrix_lipschitz_smooth_approx

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.LipEnt

lemma grad_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : Differentiable ℝ g) (L : ℝ)
    (hLip : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (x : ι → ℝ) :
    ∑ i, (fderiv ℝ g x (Pi.single i 1)) ^ 2 ≤ L ^ 2 := by
  set D := fderiv ℝ g x with hD
  set v : ι → ℝ := fun i => D (Pi.single i 1) with hv
  set S := ∑ i, v i ^ 2 with hS
  have hDv : D v = S := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i 1 := by
      ext j; by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [this, map_smul, smul_eq_mul, sq]
  have hderiv : HasDerivAt (fun t : ℝ => g (x + t • v)) S 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt g D (x + (0:ℝ) • v) := by
      simpa using (hg x).hasFDerivAt
    rw [← hDv]
    exact h2.comp_hasDerivAt (x := (0:ℝ)) h1
  have ht := hderiv.tendsto_slope_zero_right
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hle : S ≤ L * Real.sqrt S := by
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
    have h := hLip (x + (0 + t) • v) (x + (0:ℝ) • v)
    have hsq : ∑ i, ((x + (0 + t) • v) i - (x + (0:ℝ) • v) i) ^ 2 = t ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp; ring
    rw [hsq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq htp.le] at h
    rw [smul_eq_mul]
    have h3 := (le_abs_self _).trans h
    rw [inv_mul_le_iff₀ htp]
    simp only [zero_add] at h3 ⊢
    linarith
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have hsp : 0 < Real.sqrt S := Real.sqrt_pos.mpr h0
    have hsL : Real.sqrt S ≤ L := by
      have : Real.sqrt S * Real.sqrt S ≤ L * Real.sqrt S := by
        rw [Real.mul_self_sqrt hS0]; exact hle
      exact le_of_mul_le_mul_right this hsp
    have : S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
    rw [this]
    exact pow_le_pow_left₀ hsp.le hsL 2

lemma abs_mul_exp_le (u : ℝ) : |u * Real.exp u| ≤ Real.exp (2 * u) + 1 := by
  have e2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos u
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg (mul_nonneg h hpos.le), e2]
    have := Real.add_one_le_exp u
    nlinarith
  · rw [abs_of_nonpos (by nlinarith)]
    have := Real.add_one_le_exp (-u)
    have e : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right this hpos.le
    nlinarith [Real.exp_pos (2 * u)]


/-- `√(∑ xᵢ²) ≤ ∑ |xᵢ|`. -/
lemma sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := by
  have h0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [Real.sqrt_le_left h0]
  have : ∑ i, x i ^ 2 = ∑ i, |x i| ^ 2 := by simp [sq_abs]
  rw [this]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _

/-- A function that is `L`-Lipschitz for the Euclidean distance is continuous. -/
lemma continuous_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) : Continuous f := by
  have h : ∀ x y, dist (f x) (f y) ≤ (L * Fintype.card ι) * dist x y := by
    intro x y
    rw [Real.dist_eq]
    refine (hLip x y).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hL
    refine (sqrt_sum_sq_le_sum_abs (fun i => x i - y i)).trans ?_
    calc ∑ i, |x i - y i| ≤ ∑ _i : ι, dist x y := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
      _ = Fintype.card ι * dist x y := by simp
  exact (LipschitzWith.of_dist_le' h).continuous

/-- `exp (a |y|)` is integrable for the standard Gaussian. -/
lemma integrable_exp_mul_abs_gaussianReal (a : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a * |y|)) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussianReal a).add
    (integrable_exp_mul_gaussianReal (-a))) (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-a * y)]
  · rw [abs_of_nonpos hy]
    have : a * -y = -a * y := by ring
    rw [this]; linarith [Real.exp_pos (a * y)]

/-- `exp (a ∑ |xᵢ|)` is integrable for the standard Gaussian product measure. -/
lemma integrable_exp_mul_sum_abs {ι : Type*} [Fintype ι] (a : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (a * ∑ i, |x i|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have h := Integrable.fintype_prod (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun _ y => Real.exp (a * |y|)) (fun _ => integrable_exp_mul_abs_gaussianReal a)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Finset.mul_sum, Real.exp_sum]

/-- Exponential integrability of Lipschitz functions under the standard Gaussian. -/
lemma integrable_exp_mul_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    Integrable (fun x => Real.exp (s * f x)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hc := continuous_of_lip f L hL hLip
  refine Integrable.mono' ((integrable_exp_mul_sum_abs (ι := ι) (|s| * L)).const_mul
    (Real.exp (|s| * |f 0|))) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have h1 : |f x| ≤ |f 0| + L * ∑ i, |x i| := by
    have := hLip x 0
    simp only [Pi.zero_apply, sub_zero] at this
    have h2 : Real.sqrt (∑ i, x i ^ 2) ≤ ∑ i, |x i| := sqrt_sum_sq_le_sum_abs x
    have h3 : |f x| ≤ |f 0| + |f x - f 0| := by
      have := abs_sub_abs_le_abs_sub (f x) (f 0); linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hL]
  have h4 : s * f x ≤ |s| * |f x| := by
    rw [← abs_mul]; exact le_abs_self _
  have h5 := mul_le_mul_of_nonneg_left h1 (abs_nonneg s)
  nlinarith

/-- Integrability of Lipschitz functions under the standard Gaussian. -/
lemma integrable_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hc := continuous_of_lip f L hL hLip
  refine Integrable.mono' ((integrable_exp_mul_of_lip f L hL hLip 1).add
    (integrable_exp_mul_of_lip f L hL hLip (-1))) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply]
  rcases le_total 0 (f x) with h | h
  · rw [abs_of_nonneg h]
    linarith [Real.add_one_le_exp (f x), Real.exp_pos (-f x)]
  · rw [abs_of_nonpos h]
    linarith [Real.add_one_le_exp (-f x), Real.exp_pos (f x)]


lemma lip_abs {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) :
    ∀ x y, |f x - f y| ≤ |L| * Real.sqrt (∑ i, (x i - y i) ^ 2) := fun x y =>
  (hLip x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (Real.sqrt_nonneg _))

lemma integrable_mul_exp_of_lip {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    Integrable (fun x => s * f x * Real.exp (s * f x))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hL := lip_abs f L hLip
  have hc := continuous_of_lip f |L| (abs_nonneg L) hL
  refine Integrable.mono' ((integrable_exp_mul_of_lip f |L| (abs_nonneg L) hL (2 * s)).add
    (integrable_const 1)) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply, mul_assoc 2 s]
  exact abs_mul_exp_le _

lemma ent_bound_smooth {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g) (L : ℝ)
    (hLip : ∀ x y, |g x - g y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    ∫ x, s * g x * Real.exp (s * g x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, Real.exp (s * g x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, Real.exp (s * g x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ s ^ 2 * L ^ 2 / 2 * ∫ x, Real.exp (s * g x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  set μ := Measure.pi fun _ : ι => gaussianReal 0 1 with hμ
  have hLa := lip_abs g L hLip
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hexp := integrable_exp_mul_of_lip g |L| (abs_nonneg L) hLa s
  set G : (ι → ℝ) → ℝ := fun x => Real.exp (s / 2 * g x) with hG
  have hGc : ContDiff ℝ 1 G := Real.contDiff_exp.comp (contDiff_const.mul hg)
  have hG2 : ∀ x, G x ^ 2 = Real.exp (s * g x) := by
    intro x; rw [hG, sq, ← Real.exp_add]; congr 1; ring
  have hGd : ∀ x i, fderiv ℝ G x (Pi.single i 1)
      = Real.exp (s / 2 * g x) * (s / 2 * fderiv ℝ g x (Pi.single i 1)) := by
    intro x i
    have h := (((hdiff x).hasFDerivAt.const_mul (s / 2)).exp)
    rw [h.fderiv]
    simp [smul_eq_mul]
  have hGd2 : ∀ x, ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2
      = s ^ 2 / 4 * Real.exp (s * g x) * ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2 := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGd, ← hG2 x]
    simp only [hG]
    ring
  have hbd : ∀ x, ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2 ≤ s ^ 2 * L ^ 2 / 4 * Real.exp (s * g x) := by
    intro x
    rw [hGd2]
    have := grad_sq_le g hdiff L hLip x
    have h0 : 0 ≤ s ^ 2 / 4 * Real.exp (s * g x) := by positivity
    calc s ^ 2 / 4 * Real.exp (s * g x) * ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2
        ≤ s ^ 2 / 4 * Real.exp (s * g x) * L ^ 2 := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have hdg_meas : AEStronglyMeasurable (fun x => ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2) μ := by
    refine Measurable.aestronglyMeasurable ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_fderiv_apply_const ℝ G (Pi.single i 1)).pow_const 2
  have hdg : Integrable (fun x => ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2) μ := by
    refine Integrable.mono' (hexp.const_mul (s ^ 2 * L ^ 2 / 4)) hdg_meas
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact hbd x
  have e1 : (fun x => G x ^ 2) = fun x => Real.exp (s * g x) := funext hG2
  have e2 : (fun x => G x ^ 2 * Real.log (G x ^ 2)) = fun x => s * g x * Real.exp (s * g x) := by
    funext x; rw [hG2, Real.log_exp]; ring
  have hg2 : Integrable (fun x => G x ^ 2) μ := by rw [e1]; exact hexp
  have hglog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) μ := by
    rw [e2]; exact integrable_mul_exp_of_lip g L hLip s
  have key := gaussian_logsobolev G hGc hg2 hglog hdg
  rw [e1, e2] at key
  refine key.trans ?_
  calc 2 * ∫ x, ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2 ∂μ
      ≤ 2 * ∫ x, s ^ 2 * L ^ 2 / 4 * Real.exp (s * g x) ∂μ := by
        exact mul_le_mul_of_nonneg_left (integral_mono hdg (hexp.const_mul _) hbd) (by norm_num)
    _ = _ := by rw [integral_const_mul]; ring

end GaussianMatrix.LipEnt

open GaussianMatrix

theorem solution {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ)
    (hLip : ∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) (s : ℝ) :
    ∫ x, s * f x * Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      - (∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
        * Real.log (∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      ≤ s ^ 2 * L ^ 2 / 2 * ∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  classical
  open GaussianMatrix.LipEnt in
  have hLa := lip_abs f L hLip
  have hexpf := integrable_exp_mul_of_lip f |L| (abs_nonneg L) hLa s
  have hexpf2 := integrable_exp_mul_of_lip f |L| (abs_nonneg L) hLa (2 * s)
  choose g hgs hgl hgf using fun n : ℕ =>
    lipschitz_smooth_approx f L hLip (1 / ((n : ℝ) + 1)) (by positivity)
  have hgc : ∀ n, ContDiff ℝ 1 (g n) := fun n => by simpa using hgs n 1
  have hgcont : ∀ n, Continuous (g n) := fun n => (hgc n).continuous
  have hlim : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (f x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact hgf n x)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hε : ∀ n x, |g n x - f x| ≤ 1 := fun n x => (hgf n x).trans (by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have hsg : ∀ n x, s * g n x ≤ |s| + s * f x := by
    intro n x
    have h1 := le_abs_self (s * (g n x - f x))
    rw [abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hε n x) (abs_nonneg s)
    nlinarith
  have hB : Filter.Tendsto (fun n => ∫ x, Real.exp (s * g n x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) Filter.atTop
      (nhds (∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => Real.exp |s| * Real.exp (s * f x))
      (fun n => ?_) (hexpf.const_mul _) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ((hlim x).const_mul s).rexp)
    · have := hgcont n; exact (by fun_prop : Continuous fun x => Real.exp (s * g n x)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
      exact hsg n x
  have hA : Filter.Tendsto (fun n => ∫ x, s * g n x * Real.exp (s * g n x)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) Filter.atTop
      (nhds (∫ x, s * f x * Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => Real.exp (2 * |s|) * Real.exp ((2 * s) * f x) + 1)
      (fun n => ?_) ((hexpf2.const_mul _).add (integrable_const 1)) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ((hlim x).const_mul s).mul ((hlim x).const_mul s).rexp)
    · have := hgcont n
      exact (by fun_prop : Continuous fun x => s * g n x * Real.exp (s * g n x)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_mul_exp_le _).trans ?_
      have : Real.exp (2 * (s * g n x)) ≤ Real.exp (2 * |s|) * Real.exp ((2 * s) * f x) := by
        rw [← Real.exp_add, Real.exp_le_exp]; linarith [hsg n x]
      linarith
  have hBpos : 0 < ∫ x, Real.exp (s * f x) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integral_exp_pos hexpf
  exact le_of_tendsto_of_tendsto' (hA.sub (hB.mul (hB.log hBpos.ne'))) (hB.const_mul _)
    (fun n => ent_bound_smooth (g n) (hgc n) L (hgl n) s)
