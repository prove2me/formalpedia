-- Prove2me | solution 1 for DynSampleSize.Stoch.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T11:49:37.67384+00:00
-- url     : https://prove2.me/submissions/f8316de2-7886-4a6b-8ff9-f9b8947e806f

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity
import Definitions.Def_DynSampleSize_Stoch_Model
import Definitions.Def_DynSampleSize_Stoch_Run

open MeasureTheory ProbabilityTheory
open DynSampleSize.Stoch
namespace DynamicPast

lemma measurable_run {m : ℕ} {Z : Type*} [MeasurableSpace Z]
    (L : ℝ) (g : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hg : Measurable (Function.uncurry g)) (n : ℕ → ℕ)
    (w0 : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    Measurable (fun ξ : ℕ × ℕ → Z => run L g n w0 ξ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [run,batchGrad]
    have hsum : Measurable (fun ξ : ℕ × ℕ → Z => ∑ i : Fin (n k), g (run L g n w0 ξ k) (ξ (k,i))) :=
      Finset.measurable_sum Finset.univ (fun i _ => hg.comp (ih.prodMk (measurable_pi_apply (k,(i : ℕ)))))
    exact ih.sub ((hsum.const_smul (1 / (n k : ℝ))).const_smul (1/L))

lemma run_depends {m : ℕ} {Z : Type*} (L : ℝ)
    (g : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (n : ℕ → ℕ) (w0 : EuclideanSpace ℝ (Fin m)) (k : ℕ)
    (ξ η : ℕ × ℕ → Z) (h : ∀ t < k, ∀ i < n t, ξ (t,i) = η (t,i)) :
    run L g n w0 ξ k = run L g n w0 η k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hw := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    simp only [run,hw,batchGrad]
    congr 3
    apply Finset.sum_congr rfl
    intro i hi
    rw [h k (Nat.lt_succ_self k) i i.isLt]

def past (n : ℕ → ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range k).biUnion fun t => {t} ×ˢ Finset.range (n t)

def batch (n : ℕ → ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  {k} ×ˢ Finset.range (n k)

@[simp] lemma mem_past (n : ℕ → ℕ) (k : ℕ) (x : ℕ × ℕ) :
    x ∈ past n k ↔ x.1 < k ∧ x.2 < n x.1 := by
  simp only [past,Finset.mem_biUnion,Finset.mem_range,Finset.mem_product,Finset.mem_singleton]
  constructor
  · rintro ⟨t,ht,he,hi⟩
    subst t
    exact ⟨ht,hi⟩
  · rintro ⟨ht,hi⟩
    exact ⟨x.1,ht,rfl,hi⟩

@[simp] lemma mem_batch (n : ℕ → ℕ) (k : ℕ) (x : ℕ × ℕ) :
    x ∈ batch n k ↔ x.1 = k ∧ x.2 < n k := by simp only [batch, Finset.mem_product, Finset.mem_singleton, Finset.mem_range]

lemma disjoint_past_batch (n : ℕ → ℕ) (k : ℕ) : Disjoint (past n k) (batch n k) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have h := (mem_past n k x).mp hx
  have h' := (mem_batch n k x).mp hy
  omega

noncomputable def extend {Z : Type*} (z0 : Z) (S : Finset (ℕ × ℕ))
    (x : S → Z) : ℕ × ℕ → Z := fun i => if h : i ∈ S then x ⟨i,h⟩ else z0

lemma measurable_extend {Z : Type*} [MeasurableSpace Z] (z0 : Z) (S : Finset (ℕ × ℕ)) :
    Measurable (extend z0 S) := by
  apply measurable_pi_lambda
  intro i
  unfold extend
  by_cases h : i ∈ S
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const

lemma run_extend {m : ℕ} {Z : Type*} (L : ℝ)
    (g : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (n : ℕ → ℕ) (w0 : EuclideanSpace ℝ (Fin m)) (k : ℕ) (z0 : Z)
    (ξ : ℕ × ℕ → Z) :
    run L g n w0 (extend z0 (past n k) (fun i => ξ i)) k = run L g n w0 ξ k := by
  apply run_depends
  intro t ht i hi
  simp [extend,ht,hi]

lemma independent_run_batch {m : ℕ} {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsProbabilityMeasure P] (L : ℝ)
    (g : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hg : Measurable (Function.uncurry g)) (n : ℕ → ℕ)
    (w0 : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    IndepFun (fun ξ => run L g n w0 ξ k)
      (fun ξ (i : Fin (n k)) => ξ (k,i)) (sampleLaw P) := by
  classical
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure P
  let z0 : Z := Classical.choice ‹Nonempty Z›
  have hind : iIndepFun (fun i (ξ : ℕ × ℕ → Z) => ξ i) (sampleLaw P) :=
    iIndepFun_infinitePi (X := fun _ z => z) (fun _ => measurable_id)
  have h := hind.indepFun_finset (past n k) (batch n k) (disjoint_past_batch n k)
    (fun _ => measurable_pi_apply _)
  let F := fun x : past n k → Z => run L g n w0 (extend z0 (past n k) x) k
  let G := fun x : batch n k → Z => fun i : Fin (n k) => x ⟨(k,i),by simp [i.isLt]⟩
  have hF : Measurable F := (measurable_run L g hg n w0 k).comp (measurable_extend z0 (past n k))
  have hG : Measurable G := by fun_prop
  have hc := h.comp hF hG
  convert hc using 1
  · funext ξ
    exact (run_extend L g n w0 k z0 ξ).symm
  · rfl

lemma batch_law {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (n k : ℕ) : (sampleLaw P).map (fun ξ (i : Fin n) => ξ (k,i)) =
      Measure.pi (fun _ : Fin n => P) := by
  have hi : Function.Injective (fun i : Fin n => (k,(i : ℕ))) := by
    intro i j h
    exact Fin.ext (Prod.mk.inj h).2
  simpa [sampleLaw, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ × ℕ => P) hi)

#print axioms measurable_run
#print axioms run_depends
#print axioms independent_run_batch
#print axioms batch_law
end DynamicPast

open MeasureTheory
namespace DynamicProduct

lemma nonnegative_product_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (u : A → ℝ) (hu : Integrable u μ) (hbound : ∀ x, (∫ y, f (x,y) ∂ν) ≤ u x) :
    Integrable f (μ.prod ν) ∧ (∫ z, f z ∂(μ.prod ν)) ≤ ∫ x, u x ∂μ := by
  have hnorm (x : A) : (∫ y, ‖f (x,y)‖ ∂ν) = ∫ y, f (x,y) ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => Real.norm_of_nonneg (hf0 (x,y)))
  have houter : Integrable (fun x => ∫ y, ‖f (x,y)‖ ∂ν) μ := by
    apply hu.mono_nonneg (hf.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun x => integral_nonneg (fun y => norm_nonneg _))
    · exact Filter.Eventually.of_forall (fun x => by rw [hnorm]; exact hbound x)
  have hp : Integrable f (μ.prod ν) :=
    (integrable_prod_iff hf.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hfi,houter⟩
  refine ⟨hp,?_⟩
  rw [integral_prod f hp]
  exact integral_mono hp.integral_prod_left hu hbound

#print axioms nonnegative_product_bound
end DynamicProduct


set_option autoImplicit false
open MeasureTheory ProbabilityTheory DynSampleSize.Stoch



lemma dss_oneD (φ g h : ℝ → ℝ) (c : ℝ) (hφ : ∀ t, HasDerivAt φ (g t) t)
    (hg : ∀ t, HasDerivAt g (h t) t) (hh : ∀ t, h t ≤ c) : φ 1 ≤ φ 0 + g 0 + c / 2 := by
  have hgt : ∀ t, 0 ≤ t → g t ≤ g 0 + c * t := by
    intro t ht
    have hF : ∀ x, HasDerivAt (fun x => g x - c * x) (h x - c) x := fun x =>
      ((hg x).sub ((hasDerivAt_id' x).const_mul c)).congr_deriv (by ring)
    have hanti : Antitone (fun x => g x - c * x) :=
      antitone_of_deriv_nonpos (fun x => (hF x).differentiableAt) (fun x => by
        rw [(hF x).deriv]; linarith [hh x])
    have := hanti ht
    simp only [mul_zero, sub_zero] at this
    linarith
  have hF : ∀ x, HasDerivAt (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (g x - g 0 - c * x) x := by
    intro x
    have h1 := (hφ x).sub ((hasDerivAt_id' x).const_mul (g 0))
    have h2 := ((hasDerivAt_pow 2 x).const_mul (c / 2))
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    norm_num <;> ring
  have hanti : AntitoneOn (fun x => φ x - g 0 * x - c / 2 * x ^ 2) (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun x _ => (hF x).continuousAt.continuousWithinAt
    · exact fun x _ => (hF x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hF x).deriv]
      linarith [hgt x hx.1.le]
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [mul_zero, sub_zero, zero_pow two_ne_zero, mul_one, one_pow] at this
  linarith

lemma dss_quad {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w d : EuclideanSpace ℝ (Fin m)) :
    J w + inner ℝ (gradient J w) d + lam / 2 * ‖d‖ ^ 2 ≤ J (w + d) ∧
      J (w + d) ≤ J w + inner ℝ (gradient J w) d + L / 2 * ‖d‖ ^ 2 := by
  obtain ⟨hC, -, -, hH⟩ := hJ
  have hdiff : Differentiable ℝ J := hC.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (fderiv ℝ J) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set γ : ℝ → EuclideanSpace ℝ (Fin m) := fun t => w + t • d with hγ
  have hγd : ∀ t, HasDerivAt γ d t := fun t => by
    simpa [hγ] using ((hasDerivAt_id' t).smul_const d).const_add w
  have h1 : ∀ t, HasDerivAt (fun t => J (γ t)) (fderiv ℝ J (γ t) d) t := fun t =>
    (hdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have h2 : ∀ t, HasDerivAt (fun t => fderiv ℝ J (γ t) d)
      (fderiv ℝ (fderiv ℝ J) (γ t) d d) t := fun t => by
    have := (hdiff2 (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    exact (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp_hasDerivAt t this
  have hgrad : fderiv ℝ J w d = inner ℝ (gradient J w) d := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have e0 : γ 0 = w := by simp [hγ]
  have e1 : γ 1 = w + d := by simp [hγ]
  constructor
  · have := dss_oneD (fun t => -J (γ t)) (fun t => -fderiv ℝ J (γ t) d)
      (fun t => -fderiv ℝ (fderiv ℝ J) (γ t) d d) (-(lam * ‖d‖ ^ 2))
      (fun t => (h1 t).neg) (fun t => (h2 t).neg) (fun t => by linarith [(hH (γ t) d).1])
    simp only [e0, e1, hgrad] at this
    linarith
  · have := dss_oneD (fun t => J (γ t)) (fun t => fderiv ℝ J (γ t) d)
      (fun t => fderiv ℝ (fderiv ℝ J) (γ t) d d) (L * ‖d‖ ^ 2)
      h1 h2 (fun t => (hH (γ t) d).2)
    simp only [e0, e1, hgrad] at this
    linarith

lemma dss_taylor {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J (w - (1 / L) • g) ≤ J w - (1 / L) * inner ℝ (gradient J w) g + 1 / (2 * L) * ‖g‖ ^ 2 := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).2
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right, norm_smul, mul_pow] at this
  have h2 : ‖-(1 / L)‖ ^ 2 = (1 / L) ^ 2 := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
  rw [h2] at this
  have h3 : L / 2 * ((1 / L) ^ 2 * ‖g‖ ^ 2) = 1 / (2 * L) * ‖g‖ ^ 2 := by
    field_simp
  rw [h3] at this
  linarith

lemma dss_lower {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J w - (1 / L) * (‖gradient J w‖ * ‖g‖) ≤ J (w - (1 / L) • g) := by
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hlam : 0 < lam := hJ.2.1
  have := (dss_quad J lam L hJ w ((-(1 / L)) • g)).1
  have e : w + (-(1 / L)) • g = w - (1 / L) • g := by rw [neg_smul, sub_eq_add_neg]
  rw [e, inner_smul_right] at this
  have h1 : inner ℝ (gradient J w) g ≤ ‖gradient J w‖ * ‖g‖ := by
    have := abs_real_inner_le_norm (gradient J w) g
    linarith [le_abs_self (inner ℝ (gradient J w) g)]
  have h2 : 0 ≤ lam / 2 * ‖(-(1 / L)) • g‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 / L by positivity)]


lemma dss_gd {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) := by
  have hlam : 0 < lam := hJ.2.1
  have h := (dss_quad J lam L hJ w (wstar - w)).1
  rw [add_sub_cancel] at h
  have h1 := hwstar w
  have h2 : -(‖gradient J w‖ * ‖wstar - w‖) ≤ inner ℝ (gradient J w) (wstar - w) := by
    have := abs_real_inner_le_norm (gradient J w) (wstar - w)
    linarith [neg_abs_le (inner ℝ (gradient J w) (wstar - w))]
  rw [real_inner_self_eq_norm_sq]
  set G := ‖gradient J w‖
  set r := ‖wstar - w‖
  have h3 : J w - J wstar ≤ G * r - lam / 2 * r ^ 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hlam.le, sq_nonneg (G - lam * r), sq_nonneg G]




section meas

variable {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]

lemma dss_memLp_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) :
    MemLp (batchGrad gradℓ n w) 2 (Measure.pi (fun _ : Fin n => P)) := by
  unfold batchGrad
  have h : ∀ i : Fin n, MemLp (fun b : Fin n → Z => gradℓ w (b i)) 2
      (Measure.pi (fun _ : Fin n => P)) := fun i =>
    hgrad.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P) i)
  have hs := memLp_finsetSum' (s := Finset.univ) (fun i _ => h i)
  have e : (fun b : Fin n → Z => (1 / (n : ℝ)) • ∑ i, gradℓ w (b i)) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) := by
    ext b
    simp
  rw [e]
  exact hs.const_smul _

lemma dss_integral_eval (f : Z → EuclideanSpace ℝ (Fin m)) (hf : AEStronglyMeasurable f P)
    (n : ℕ) (i : Fin n) :
    ∫ b : Fin n → Z, f (b i) ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, f z ∂P := by
  have hmp := measurePreserving_eval (fun _ : Fin n => P) i
  have h := integral_map (μ := Measure.pi (fun _ : Fin n => P)) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := f) (by rw [hmp.map_eq]; exact hf)
  rw [hmp.map_eq] at h
  exact h.symm

lemma dss_integral_batch (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    ∫ b, batchGrad gradℓ n w b ∂(Measure.pi (fun _ : Fin n => P)) = ∫ z, gradℓ w z ∂P := by
  unfold batchGrad
  rw [integral_smul, integral_finsetSum]
  · have h : ∀ i : Fin n, ∫ b : Fin n → Z, gradℓ w (b i) ∂(Measure.pi (fun _ : Fin n => P)) =
        ∫ z, gradℓ w z ∂P := fun i => dss_integral_eval P (gradℓ w) hgrad.1 n i
    simp only [h]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (by omega)), one_smul]
  · intro i _
    exact (hgrad.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => P) i)).integrable one_le_two

end meas

lemma dss_sq_decomp {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    ∫ x, ‖Y x‖ ^ 2 ∂μ = ‖∫ x, Y x ∂μ‖ ^ 2 + ∫ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 ∂μ := by
  set c := ∫ x, Y x ∂μ with hc
  have hint : Integrable Y μ := hY.integrable one_le_two
  have hsq : Integrable (fun x => ‖Y x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hY.1).1 hY)
  have hYc : MemLp (fun x => Y x - c) 2 μ := hY.sub (memLp_const c)
  have hsq2 : Integrable (fun x => ‖Y x - c‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hYc.1).1 hYc)
  have hinner : Integrable (fun x => inner ℝ c (Y x - c)) μ :=
    (hint.sub (integrable_const c)).const_inner c
  have hpt : ∀ x, ‖Y x‖ ^ 2 = ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2 := by
    intro x
    have := norm_add_sq_real c (Y x - c)
    simpa using this
  have hsub : Integrable (fun x => Y x - c) μ := hint.sub (integrable_const c)
  have h0 : ∫ x, inner ℝ c (Y x - c) ∂μ = 0 := by
    have := integral_inner (𝕜 := ℝ) hsub c
    rw [this, integral_sub hint (integrable_const c)]
    simp [hc]
  have e1 : Integrable (fun x => ‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) μ :=
    (integrable_const _).add (hinner.const_mul 2)
  have i1 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ =
      (∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ) + ∫ x, ‖Y x - c‖ ^ 2 ∂μ :=
    integral_add e1 hsq2
  have i2 : ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c)) ∂μ =
      (∫ x, ‖c‖ ^ 2 ∂μ) + ∫ x, 2 * inner ℝ c (Y x - c) ∂μ :=
    integral_add (integrable_const _) (hinner.const_mul 2)
  have i3 : ∫ x, 2 * inner ℝ c (Y x - c) ∂μ = 2 * ∫ x, inner ℝ c (Y x - c) ∂μ :=
    integral_const_mul 2 _
  calc ∫ x, ‖Y x‖ ^ 2 ∂μ
      = ∫ x, (‖c‖ ^ 2 + 2 * inner ℝ c (Y x - c) + ‖Y x - c‖ ^ 2) ∂μ := by
        congr 1; ext x; exact hpt x
    _ = ‖c‖ ^ 2 + ∫ x, ‖Y x - c‖ ^ 2 ∂μ := by
        rw [i1, i2, i3, h0]
        simp

lemma dss_vecVar_eq {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → EuclideanSpace ℝ (Fin m)) (hY : MemLp Y 2 μ) :
    vecVar μ Y = ∑ k, variance (fun x => Y x k) μ := by
  have hk : ∀ k, MemLp (fun x => Y x k) 2 μ := fun k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hY
  have hmean : ∀ k, (∫ x, Y x ∂μ) k = ∫ x, Y x k ∂μ := fun k => by
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).integral_comp_comm
      (hY.integrable one_le_two)
    simpa using this.symm
  unfold vecVar
  have e : ∀ x, ‖Y x - ∫ y, Y y ∂μ‖ ^ 2 = ∑ k, (Y x k - ∫ y, Y y k ∂μ) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, hmean k]
  simp_rw [e]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [variance_eq_integral (hk k).aemeasurable]
  · intro k _
    exact ((hk k).sub (memLp_const _)).integrable_sq

lemma dss_smv {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) (hgrad : MemLp (gradℓ w) 2 P) (n : ℕ) (hn : 1 ≤ n) :
    vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) =
      vecVar P (gradℓ w) / n := by
  rw [dss_vecVar_eq _ _ (dss_memLp_batch P gradℓ w hgrad n), dss_vecVar_eq P _ hgrad,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hX : MemLp (fun z => gradℓ w z k) 2 P :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).comp_memLp' hgrad
  have e : (fun b : Fin n → Z => batchGrad gradℓ n w b k) =
      (1 / (n : ℝ)) • ∑ i : Fin n, fun b : Fin n → Z => gradℓ w (b i) k := by
    ext b
    simp [batchGrad, Finset.sum_apply]
  rw [e, variance_smul, variance_sum_pi (X := fun _ : Fin n => fun z => gradℓ w z k)
    (fun _ => hX)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp


lemma dss_step {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      Integrable (fun b => ‖batchGrad gradℓ n w b‖ ^ 2) (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / L * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L) * ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, ‖batchGrad gradℓ n w b‖ ^ 2 ∂(Measure.pi (fun _ : Fin n => P)) =
        ‖gradient (objective P ℓ) w‖ ^ 2 +
          vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) := by
  set J := objective P ℓ with hJdef
  set μ := Measure.pi (fun _ : Fin n => P) with hμ
  set g := batchGrad gradℓ n w with hg
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hg2 : MemLp g 2 μ := dss_memLp_batch P gradℓ w (hmodel.memLp_grad w) n
  have hg1 : Integrable g μ := hg2.integrable one_le_two
  have hsq : Integrable (fun b => ‖g b‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hg2.1).1 hg2)
  have hnorm : Integrable (fun b => ‖g b‖) μ := hg1.norm
  have hmean : ∫ b, g b ∂μ = gradient J w := by
    rw [hg, hμ, dss_integral_batch P gradℓ w (hmodel.memLp_grad w) n hn]
    exact ((hmodel.hasGradientAt_objective w).gradient).symm
  have hdecomp := dss_sq_decomp μ g hg2
  have hFm : AEStronglyMeasurable (fun b => J (w - (1 / L) • g b)) μ :=
    hJ.1.continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.sub (hg2.1.const_smul (1 / L)))
  have hF : Integrable (fun b => J (w - (1 / L) • g b)) μ := by
    have hB : Integrable (fun b => (1 / L) * (‖gradient J w‖ * ‖g b‖) +
        1 / (2 * L) * ‖g b‖ ^ 2) μ :=
      (hnorm.const_mul (‖gradient J w‖)).const_mul (1 / L) |>.add (hsq.const_mul _)
    have hd : Integrable (fun b => J (w - (1 / L) • g b) - J w) μ := by
      refine Integrable.mono' hB (hFm.sub aestronglyMeasurable_const) ?_
      refine Filter.Eventually.of_forall (fun b => ?_)
      have h1 := dss_taylor J lam L hJ w (g b)
      have h2 := dss_lower J lam L hJ w (g b)
      have h3 : inner ℝ (gradient J w) (g b) ≥ -(‖gradient J w‖ * ‖g b‖) := by
        have := abs_real_inner_le_norm (gradient J w) (g b)
        linarith [neg_abs_le (inner ℝ (gradient J w) (g b))]
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · nlinarith [mul_nonneg (show 0 ≤ 1 / L by positivity) (mul_nonneg (norm_nonneg (gradient J w)) (norm_nonneg (g b))), sq_nonneg ‖g b‖,
          show 0 ≤ 1 / (2 * L) by positivity]
      · have h4 : (1 / L) * inner ℝ (gradient J w) (g b) ≥ -((1 / L) * (‖gradient J w‖ * ‖g b‖)) := by
          nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 1 / L by positivity)]
        linarith
    refine (hd.add (integrable_const (J w))).congr (Filter.Eventually.of_forall (fun b => ?_))
    simp
  refine ⟨hF, hsq, ?_, ?_⟩
  · have hR : Integrable (fun b => J w - (1 / L) * inner ℝ (gradient J w) (g b) +
        1 / (2 * L) * ‖g b‖ ^ 2) μ :=
      ((integrable_const _).sub ((hg1.const_inner (gradient J w)).const_mul (1 / L))).add
        (hsq.const_mul _)
    have hle := integral_mono hF hR (fun b => dss_taylor J lam L hJ w (g b))
    refine hle.trans (le_of_eq ?_)
    have eA : Integrable (fun b => J w - 1 / L * inner ℝ (gradient J w) (g b)) μ :=
      (integrable_const _).sub ((hg1.const_inner (gradient J w)).const_mul (1 / L))
    have i1 : ∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b) + 1 / (2 * L) * ‖g b‖ ^ 2) ∂μ =
        (∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b)) ∂μ) +
          ∫ b, 1 / (2 * L) * ‖g b‖ ^ 2 ∂μ := integral_add eA (hsq.const_mul _)
    have i2 : ∫ b, (J w - 1 / L * inner ℝ (gradient J w) (g b)) ∂μ =
        (∫ b, J w ∂μ) - ∫ b, 1 / L * inner ℝ (gradient J w) (g b) ∂μ :=
      integral_sub (integrable_const _) ((hg1.const_inner (gradient J w)).const_mul (1 / L))
    have i3 : ∫ b, 1 / L * inner ℝ (gradient J w) (g b) ∂μ =
        1 / L * ∫ b, inner ℝ (gradient J w) (g b) ∂μ := integral_const_mul _ _
    have i4 : ∫ b, inner ℝ (gradient J w) (g b) ∂μ = inner ℝ (gradient J w) (∫ b, g b ∂μ) :=
      integral_inner hg1 _
    have i5 : ∫ b, 1 / (2 * L) * ‖g b‖ ^ 2 ∂μ = 1 / (2 * L) * ∫ b, ‖g b‖ ^ 2 ∂μ :=
      integral_const_mul _ _
    rw [i1, i2, i3, i4, i5, hmean]
    simp [real_inner_self_eq_norm_sq]
  · have hv : vecVar μ g = ∫ x, ‖g x - ∫ y, g y ∂μ‖ ^ 2 ∂μ := rfl
    rw [hv, hdecomp, hmean]


lemma dss_426 {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P)) ≤
        objective P ℓ w - 1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2 +
          1 / (2 * L * n) * vecVar P (gradℓ w) := by
  obtain ⟨hF, hsq, h3, h4⟩ := dss_step P ℓ gradℓ hmodel lam L hJ w n hn
  refine ⟨hF, ?_⟩
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hv := dss_smv P gradℓ w (hmodel.memLp_grad w) n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [h4] at h3
  have h5 : 1 / (2 * L) * vecVar (Measure.pi (fun _ : Fin n => P)) (batchGrad gradℓ n w) ≤
      1 / (2 * L * n) * vecVar P (gradℓ w) := by
    have e : 1 / (2 * L * n) * vecVar P (gradℓ w) = 1 / (2 * L) * (vecVar P (gradℓ w) / n) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hv.le (by positivity)
  have e2 : 1 / L * ‖gradient (objective P ℓ) w‖ ^ 2 =
      2 * (1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2) := by
    field_simp
  nlinarith [h3, h5, e2]

theorem fixed_recurrence {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (wstar : EuclideanSpace ℝ (Fin m)) (hwstar : ∀ w, objective P ℓ wstar ≤ objective P ℓ w)
    (ω : ℝ) (hω : ∀ w, vecVar P (gradℓ w) ≤ ω)
    (w : EuclideanSpace ℝ (Fin m)) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun b => objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b))
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ b, (objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) - objective P ℓ wstar)
          ∂(Measure.pi (fun _ : Fin n => P)) ≤
        (1 - lam / (2 * L)) * (objective P ℓ w - objective P ℓ wstar) + ω / (2 * L * n) := by
  obtain ⟨hF, h426⟩ := dss_426 P ℓ gradℓ hmodel lam L hJ w n hn
  refine ⟨hF, ?_⟩
  have hL : 0 < L := hJ.2.1.trans hJ.2.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hgd := dss_gd (objective P ℓ) lam L hJ wstar hwstar w
  rw [real_inner_self_eq_norm_sq] at hgd
  have hI : ∫ b, (objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) - objective P ℓ wstar)
        ∂(Measure.pi (fun _ : Fin n => P)) =
      ∫ b, objective P ℓ (w - (1 / L) • batchGrad gradℓ n w b) ∂(Measure.pi (fun _ : Fin n => P))
        - objective P ℓ wstar := by
    rw [integral_sub hF (integrable_const _)]
    simp
  rw [hI]
  have h1 : 1 / (2 * L) * (lam * (objective P ℓ w - objective P ℓ wstar)) ≤
      1 / (2 * L) * ‖gradient (objective P ℓ) w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hgd (by positivity)
  have h2 : 1 / (2 * L * n) * vecVar P (gradℓ w) ≤ ω / (2 * L * n) := by
    calc 1 / (2 * L * n) * vecVar P (gradℓ w) ≤ 1 / (2 * L * n) * ω :=
          mul_le_mul_of_nonneg_left (hω w) (by positivity)
      _ = ω / (2 * L * n) := by ring
  have h3 : 1 / (2 * L) * (lam * (objective P ℓ w - objective P ℓ wstar)) =
      lam / (2 * L) * (objective P ℓ w - objective P ℓ wstar) := by ring
  nlinarith [h426, h1, h2, h3]

open MeasureTheory ProbabilityTheory DynSampleSize.Stoch DynamicPast DynamicProduct
namespace DynamicStep

lemma adaptive_step {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ g) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (wstar : EuclideanSpace ℝ (Fin m)) (hwstar : ∀ w, objective P ℓ wstar ≤ objective P ℓ w)
    (ω : ℝ) (hω : ∀ w, vecVar P (g w) ≤ ω) (n : ℕ → ℕ)
    (w0 : EuclideanSpace ℝ (Fin m)) (k : ℕ) (hn : 1 ≤ n k)
    (hI : Integrable (fun ξ => objective P ℓ (run L g n w0 ξ k)) (sampleLaw P)) :
    Integrable (fun ξ => objective P ℓ (run L g n w0 ξ (k+1))) (sampleLaw P) ∧
    (∫ ξ, (objective P ℓ (run L g n w0 ξ (k+1))-objective P ℓ wstar) ∂(sampleLaw P)) ≤
      (1-lam/(2*L)) * (∫ ξ, (objective P ℓ (run L g n w0 ξ k)-objective P ℓ wstar) ∂(sampleLaw P)) +
        ω/(2*L*(n k : ℝ)) := by
  let μ := sampleLaw P
  letI : IsProbabilityMeasure μ := by dsimp [μ,sampleLaw]; infer_instance
  let W := fun ξ => run L g n w0 ξ k
  let B := fun ξ : ℕ × ℕ → Z => fun i : Fin (n k) => ξ (k,i)
  let ν := Measure.pi (fun _ : Fin (n k) => P)
  have hW : Measurable W := measurable_run L g hmodel.measurable_grad n w0 k
  have hB : Measurable B := by fun_prop
  letI : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  let F := fun z : EuclideanSpace ℝ (Fin m) × (Fin (n k) → Z) =>
    objective P ℓ (z.1 - (1/L) • batchGrad g (n k) z.1 z.2) - objective P ℓ wstar
  let U := fun w => (1-lam/(2*L))*(objective P ℓ w-objective P ℓ wstar)+ω/(2*L*(n k : ℝ))
  have hmJ : Measurable (objective P ℓ) := hJ.1.continuous.measurable
  have hsum : Measurable (fun z : EuclideanSpace ℝ (Fin m) × (Fin (n k) → Z) =>
      ∑ i : Fin (n k), g z.1 (z.2 i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hmodel.measurable_grad.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hF : Measurable F :=
    (hmJ.comp (measurable_fst.sub ((hsum.const_smul (1/(n k : ℝ))).const_smul (1/L)))).sub_const _
  have hU : Integrable U (μ.map W) := by
    have hprev : Integrable (fun w => objective P ℓ w-objective P ℓ wstar) (μ.map W) :=
      (integrable_map_measure (hmJ.sub_const _).aestronglyMeasurable hW.aemeasurable).mpr
        (hI.sub (integrable_const _))
    exact (hprev.const_mul _).add (integrable_const _)
  have hfi (w : EuclideanSpace ℝ (Fin m)) := fixed_recurrence P ℓ g hmodel lam L hJ wstar hwstar ω hω w (n k) hn
  have hprod := nonnegative_product_bound (μ.map W) ν F hF
    (fun z => sub_nonneg.mpr (hwstar _))
    (fun w => (hfi w).1.sub (integrable_const _)) U hU (fun w => (hfi w).2)
  have hp : μ.map (fun ξ => (W ξ,B ξ)) = (μ.map W).prod ν := by
    have h := (independent_run_batch P L g hmodel.measurable_grad n w0 k).map_prod_eq_prod_map_map
      hW.aemeasurable hB.aemeasurable
    simpa only [μ,B,batch_law] using h
  have hFmap : Integrable F (μ.map (fun ξ => (W ξ,B ξ))) := by rw [hp]; exact hprod.1
  have hnext : Integrable (fun ξ => objective P ℓ (run L g n w0 ξ (k+1))-objective P ℓ wstar) μ := by
    simpa only [Function.comp_def,F,W,B,run] using hFmap.comp_measurable (hW.prodMk hB)
  have hleft : (∫ z, F z ∂((μ.map W).prod ν)) = ∫ ξ, F (W ξ,B ξ) ∂μ := by
    rw [← hp]
    exact integral_map (hW.prodMk hB).aemeasurable hF.aestronglyMeasurable
  have hright : (∫ w, U w ∂(μ.map W)) =
      (1-lam/(2*L))*(∫ ξ, (objective P ℓ (W ξ)-objective P ℓ wstar) ∂μ)+ω/(2*L*(n k : ℝ)) := by
    rw [integral_map hW.aemeasurable hU.aestronglyMeasurable]
    dsimp [U]
    have hgap : Integrable (fun ξ => objective P ℓ (W ξ)-objective P ℓ wstar) μ :=
      hI.sub (integrable_const _)
    have hs : Integrable (fun ξ => (1-lam/(2*L))*(objective P ℓ (W ξ)-objective P ℓ wstar)) μ :=
      hgap.const_mul _
    rw [integral_add hs (integrable_const _), integral_const_mul]
    simp
  constructor
  · have h := hnext.add (integrable_const (objective P ℓ wstar))
    change Integrable (fun ξ => (objective P ℓ (run L g n w0 ξ (k+1))-objective P ℓ wstar)+objective P ℓ wstar) μ at h
    simpa only [sub_add_cancel] using h
  · have h := hprod.2
    rw [hleft,hright] at h
    simpa only [F,W,B,run] using h

#print axioms adaptive_step
end DynamicStep

namespace StochasticRate

lemma scalar_rate (E : ℕ → ℝ) (lam L ω a : ℝ) (n : ℕ → ℕ)
    (hlam : 0 < lam) (hlamL : lam < L) (hω : 0 ≤ ω) (ha : 1 < a)
    (hn : ∀ k, a^k ≤ (n k : ℝ))
    (hrec : ∀ k, E (k+1) ≤ (1-lam/(2*L))*E k+ω/(2*L*(n k : ℝ))) :
    max (1-lam/(4*L)) (1/a) < 1 ∧
      ∀ k, E k ≤ max (E 0) (2*ω/lam)*(max (1-lam/(4*L)) (1/a))^k := by
  let ρ := max (1-lam/(4*L)) (1/a)
  let C := max (E 0) (2*ω/lam)
  have hL : 0 < L := hlam.trans hlamL
  have ha0 : 0 < a := by linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity : 0 < 1/a) (le_max_right _ _)
  have hρ1 : ρ < 1 := by
    apply max_lt
    · have hp : 0 < lam/(4*L) := by positivity
      linarith
    · exact (div_lt_one ha0).mpr ha
  have hCω : 2*ω/lam ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ 2*ω/lam).trans hCω
  have hc0 : 0 ≤ 1-lam/(2*L) := by
    have hl : lam/(2*L) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hcoeff : ω/(2*L) ≤ C*lam/(4*L) := by
    have hh : 2*ω ≤ C*lam := (div_le_iff₀ hlam).mp hCω
    calc _ = (2*ω)/(4*L) := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right hh (by positivity)
  have hinv (k : ℕ) : 1/(n k : ℝ) ≤ ρ^k := by
    calc _ ≤ 1/(a^k) := div_le_div_of_nonneg_left (by norm_num) (pow_pos ha0 k) (hn k)
      _ = (1/a)^k := by rw [div_pow,one_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (le_max_right _ _) k
  have hnoise (k : ℕ) : ω/(2*L*(n k : ℝ)) ≤ (C*lam/(4*L))*ρ^k := by
    calc _ = (ω/(2*L))*(1/(n k : ℝ)) := by ring
      _ ≤ (ω/(2*L))*ρ^k := mul_le_mul_of_nonneg_left (hinv k) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  refine ⟨hρ1,?_⟩
  intro k
  change E k ≤ C*ρ^k
  induction k with
  | zero => simpa [C] using (le_max_left (E 0) (2*ω/lam))
  | succ k ih =>
    calc E (k+1) ≤ (1-lam/(2*L))*E k+ω/(2*L*(n k : ℝ)) := hrec k
      _ ≤ (1-lam/(2*L))*(C*ρ^k)+(C*lam/(4*L))*ρ^k :=
        add_le_add (mul_le_mul_of_nonneg_left ih hc0) (hnoise k)
      _ = (C*ρ^k)*(1-lam/(4*L)) := by ring
      _ ≤ (C*ρ^k)*ρ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = C*ρ^(k+1) := by rw [pow_succ]; ring

#print axioms scalar_rate
end StochasticRate


open MeasureTheory
namespace DynSampleSize.Stoch

/-- Theorem 4.2, p. 12: if the sample sizes satisfy `n_k ≥ a^k` for some `a > 1` and (4.22) holds,
the dynamic batch run (4.24) satisfies `E[J(w_k) − J(w*)] ≤ C ρ^k` for all `k`, with
`ρ = max{1 − λ/(4L), 1/a} < 1` and `C = max{J(w₀) − J(w*), 2ω/λ}` (4.28)–(4.29). -/
theorem conditional_root {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (wstar : EuclideanSpace ℝ (Fin m)) (hwstar : ∀ w, objective P ℓ wstar ≤ objective P ℓ w)
    (ω : ℝ) (hω : ∀ w, vecVar P (gradℓ w) ≤ ω)
    (a : ℝ) (ha : 1 < a) (n : ℕ → ℕ) (hn : ∀ k, a ^ k ≤ (n k : ℝ))
    (w0 : EuclideanSpace ℝ (Fin m))
    (hInt : ∀ k : ℕ, Integrable (fun ξ => objective P ℓ (run L gradℓ n w0 ξ k)) (sampleLaw P))
    (hRec : ∀ k : ℕ,
      (∫ ξ, (objective P ℓ (run L gradℓ n w0 ξ (k+1)) - objective P ℓ wstar) ∂(sampleLaw P)) ≤
        (1-lam/(2*L)) * (∫ ξ, (objective P ℓ (run L gradℓ n w0 ξ k) - objective P ℓ wstar) ∂(sampleLaw P)) +
          ω/(2*L*(n k : ℝ))) :
    max (1 - lam / (4 * L)) (1 / a) < 1 ∧
      ∀ k : ℕ,
        Integrable (fun ξ => objective P ℓ (run L gradℓ n w0 ξ k)) (sampleLaw P) ∧
          ∫ ξ, (objective P ℓ (run L gradℓ n w0 ξ k) - objective P ℓ wstar) ∂(sampleLaw P) ≤
            max (objective P ℓ w0 - objective P ℓ wstar) (2 * ω / lam) *
              (max (1 - lam / (4 * L)) (1 / a)) ^ k  := by
  letI : IsProbabilityMeasure (sampleLaw P) := by unfold sampleLaw; infer_instance
  let E : ℕ → ℝ := fun k => ∫ ξ, (objective P ℓ (run L gradℓ n w0 ξ k)-objective P ℓ wstar) ∂(sampleLaw P)
  have hω0 : 0 ≤ ω := (integral_nonneg (fun _ => sq_nonneg _)).trans (hω wstar)
  have hE0 : E 0 = objective P ℓ w0-objective P ℓ wstar := by simp [E,run]
  have hbound := StochasticRate.scalar_rate E lam L ω a n hJ.2.1 hJ.2.2.1 hω0 ha hn hRec
  refine ⟨hbound.1, fun k => ⟨hInt k, ?_⟩⟩
  simpa only [hE0] using hbound.2 k

end DynSampleSize.Stoch

#print axioms DynSampleSize.Stoch.conditional_root

open MeasureTheory
namespace DynSampleSize.Stoch

/-- Theorem 4.2, p. 12: if the sample sizes satisfy `n_k ≥ a^k` for some `a > 1` and (4.22) holds,
the dynamic batch run (4.24) satisfies `E[J(w_k) − J(w*)] ≤ C ρ^k` for all `k`, with
`ρ = max{1 − λ/(4L), 1/a} < 1` and `C = max{J(w₀) − J(w*), 2ω/λ}` (4.28)–(4.29). -/
theorem _root_.solution {m : ℕ} {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin m) → Z → ℝ)
    (gradℓ : EuclideanSpace ℝ (Fin m) → Z → EuclideanSpace ℝ (Fin m))
    (hmodel : StochModel P ℓ gradℓ) (lam L : ℝ) (hJ : UniformlyConvex (objective P ℓ) lam L)
    (wstar : EuclideanSpace ℝ (Fin m)) (hwstar : ∀ w, objective P ℓ wstar ≤ objective P ℓ w)
    (ω : ℝ) (hω : ∀ w, vecVar P (gradℓ w) ≤ ω)
    (a : ℝ) (ha : 1 < a) (n : ℕ → ℕ) (hn : ∀ k, a ^ k ≤ (n k : ℝ))
    (w0 : EuclideanSpace ℝ (Fin m)) :
    max (1 - lam / (4 * L)) (1 / a) < 1 ∧
      ∀ k : ℕ,
        Integrable (fun ξ => objective P ℓ (run L gradℓ n w0 ξ k)) (sampleLaw P) ∧
          ∫ ξ, (objective P ℓ (run L gradℓ n w0 ξ k) - objective P ℓ wstar) ∂(sampleLaw P) ≤
            max (objective P ℓ w0 - objective P ℓ wstar) (2 * ω / lam) *
              (max (1 - lam / (4 * L)) (1 / a)) ^ k := by
  letI : IsProbabilityMeasure (sampleLaw P) := by unfold sampleLaw; infer_instance
  have hn' (k : ℕ) : 1 ≤ n k := by
    have h : (1 : ℝ) ≤ (n k : ℝ) := (one_le_pow₀ ha.le).trans (hn k)
    exact_mod_cast h
  have hInt : ∀ k : ℕ, Integrable (fun ξ => objective P ℓ (run L gradℓ n w0 ξ k)) (sampleLaw P) := by
    intro k
    induction k with
    | zero => simpa only [run] using (integrable_const (objective P ℓ w0) : Integrable (fun _ : ℕ × ℕ → Z => objective P ℓ w0) (sampleLaw P))
    | succ k ih => exact (DynamicStep.adaptive_step P ℓ gradℓ hmodel lam L hJ wstar hwstar ω hω n w0 k (hn' k) ih).1
  exact conditional_root P ℓ gradℓ hmodel lam L hJ wstar hwstar ω hω a ha n hn w0 hInt
    (fun k => (DynamicStep.adaptive_step P ℓ gradℓ hmodel lam L hJ wstar hwstar ω hω n w0 k (hn' k) (hInt k)).2)


end DynSampleSize.Stoch

#print axioms solution
