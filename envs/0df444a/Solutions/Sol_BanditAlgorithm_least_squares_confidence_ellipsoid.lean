-- Prove2me | solution 1 for BanditAlgorithm.least_squares_confidence_ellipsoid
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:52.141423+00:00
-- url     : https://prove2.me/submissions/efbab5be-6d6f-42a8-823b-d048c51e2f7b

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

-- Accepted source: Harry_Xu, submission e9d7d334-6d28-446e-ac3e-ab5633b62021.

open MeasureTheory ProbabilityTheory Matrix

namespace BanditAlgorithm

private lemma selfNormalizedSum_succ_scratch {Ω : Type} {d : ℕ}
    (η : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    selfNormalizedSum d η A (t + 1) ω =
      selfNormalizedSum d η A t ω + η (t + 1) ω • A (t + 1) ω := by
  simp [selfNormalizedSum, Finset.sum_range_succ]

private lemma regularizedDesignMatrix_succ_scratch {Ω : Type} {d : ℕ}
    (lam : ℝ) (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    regularizedDesignMatrix d lam A (t + 1) ω =
      regularizedDesignMatrix d lam A t ω +
        vecMulVec (A (t + 1) ω) (A (t + 1) ω) := by
  simp only [regularizedDesignMatrix, Finset.sum_range_succ]
  abel

private lemma dot_vecMulVec_scratch {d : ℕ} (x a : Fin d → ℝ) :
    x ⬝ᵥ vecMulVec a a *ᵥ x = (x ⬝ᵥ a) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, vecMulVec_apply]
  calc
    ∑ i, x i * ∑ j, a i * a j * x j =
        ∑ i, (x i * a i) * ∑ j, a j * x j := by
          apply Finset.sum_congr rfl
          intro i _
          have hi : (∑ j, a i * a j * x j) = a i * ∑ j, a j * x j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [hi]
          ring
    _ = (∑ i, x i * a i) * (∑ j, a j * x j) := by
          rw [Finset.sum_mul]
    _ = (∑ i, x i * a i) ^ 2 := by
          rw [pow_two]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring

private lemma dot_smul_one_mulVec_scratch {d : ℕ} (lam : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x = lam * (x ⬝ᵥ x) := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  ring

private lemma selfNormalizedProcess_succ_scratch {Ω : Type} {d : ℕ}
    (lam : ℝ) (η : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (x : Fin d → ℝ) (t : ℕ) (ω : Ω) :
    selfNormalizedProcess d lam η A x (t + 1) ω =
      selfNormalizedProcess d lam η A x t ω *
        Real.exp ((x ⬝ᵥ A (t + 1) ω) * η (t + 1) ω -
          1 / 2 * (x ⬝ᵥ A (t + 1) ω) ^ 2) := by
  rw [selfNormalizedProcess, selfNormalizedProcess,
    selfNormalizedSum_succ_scratch, regularizedDesignMatrix_succ_scratch]
  have hexp :
      x ⬝ᵥ (selfNormalizedSum d η A t ω + η (t + 1) ω • A (t + 1) ω) -
          1 / 2 * (x ⬝ᵥ
            (regularizedDesignMatrix d lam A t ω +
              vecMulVec (A (t + 1) ω) (A (t + 1) ω)) *ᵥ x) =
        (x ⬝ᵥ selfNormalizedSum d η A t ω -
          1 / 2 * (x ⬝ᵥ regularizedDesignMatrix d lam A t ω *ᵥ x)) +
        ((x ⬝ᵥ A (t + 1) ω) * η (t + 1) ω -
          1 / 2 * (x ⬝ᵥ A (t + 1) ω) ^ 2) := by
    rw [dotProduct_add, Matrix.add_mulVec, dotProduct_add, dot_vecMulVec_scratch]
    simp only [dotProduct_smul]
    ring
  rw [hexp, Real.exp_add]

private lemma selfNormalizedProcess_measurable_scratch
    {Ω : Type} {mΩ : MeasurableSpace Ω} {d : ℕ}
    (ℱ : Filtration ℕ mΩ) (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (lam : ℝ) (x : Fin d → ℝ) :
    ∀ t : ℕ, Measurable[ℱ t] (selfNormalizedProcess d lam η A x t) := by
  intro t
  induction t with
  | zero =>
      have hzero :
          selfNormalizedProcess d lam η A x 0 =
            fun _ => Real.exp (-1 / 2 * (x ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x)) := by
        funext ω
        simp [selfNormalizedProcess, selfNormalizedSum, regularizedDesignMatrix]
        ring
      rw [hzero]
      exact measurable_const
  | succ t ih =>
      have hsucc :
          selfNormalizedProcess d lam η A x t.succ =
            fun ω => selfNormalizedProcess d lam η A x t ω *
              Real.exp ((x ⬝ᵥ A (t + 1) ω) * η (t + 1) ω -
                1 / 2 * (x ⬝ᵥ A (t + 1) ω) ^ 2) := by
        funext ω
        simpa only [Nat.succ_eq_add_one] using
          selfNormalizedProcess_succ_scratch lam η A x t ω
      rw [hsucc]
      have hc : Measurable[ℱ t] (fun ω => x ⬝ᵥ A (t + 1) ω) := by
        fun_prop
      have hc' : Measurable[ℱ (t + 1)] (fun ω => x ⬝ᵥ A (t + 1) ω) :=
        hc.mono (ℱ.mono t.le_succ) le_rfl
      have hi' : Measurable[ℱ (t + 1)] (selfNormalizedProcess d lam η A x t) :=
        ih.mono (ℱ.mono t.le_succ) le_rfl
      exact hi'.mul <| Real.measurable_exp.comp <|
        (hc'.mul (hη t)).sub <| measurable_const.mul (hc'.pow_const 2)

private lemma ae_condExpKernel_eq_of_measurable_scratch
    {Ω : Type} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (c : Ω → ℝ) (hc : Measurable[m] c) :
    ∀ᵐ ω ∂(P.trim hm), c =ᵐ[condExpKernel P m ω] fun _ => c ω := by
  letI : MeasurableSpace (Ω × Ω) := m.prod mΩ
  have hpair :
      ∀ᵐ z ∂((P.trim hm) ⊗ₘ condExpKernel P m), c z.2 = c z.1 := by
    rw [compProd_trim_condExpKernel hm]
    have hdiag : AEMeasurable (fun ω : Ω => (ω, ω)) P :=
      ((measurable_id'' hm).prod measurable_id).aemeasurable
    have hp : MeasurableSet {z : Ω × Ω | c z.2 = c z.1} :=
      measurableSet_eq_fun
        ((hc.mono hm le_rfl).comp measurable_snd)
        (hc.comp measurable_fst)
    apply (ae_map_iff hdiag hp).2
    exact Filter.Eventually.of_forall fun ω => rfl
  exact (Measure.ae_ae_of_ae_compProd hpair).mono fun ω hω =>
    hω.mono fun y hy => hy

private lemma condKernel_integral_predictable_exp_le_one_scratch
    {Ω : Type} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (X c : Ω → ℝ) (hc : Measurable[m] c)
    (hsg : HasCondSubgaussianMGF m hm X 1 P) :
    ∀ᵐ ω ∂(P.trim hm),
      Integrable (fun y => Real.exp (c y * X y - 1 / 2 * (c y) ^ 2))
          (condExpKernel P m ω) ∧
        (∫ y, Real.exp (c y * X y - 1 / 2 * (c y) ^ 2) ∂condExpKernel P m ω) ≤ 1 := by
  have hcdiag :=
    ae_condExpKernel_eq_of_measurable_scratch
      (P := P) (m := m) (mΩ := mΩ) hm c hc
  filter_upwards [hcdiag, hsg.mgf_le, hsg.ae_forall_integrable_exp_mul] with
      ω hcω hmgf hint
  have heq :
      (fun y => Real.exp (c y * X y - 1 / 2 * (c y) ^ 2)) =ᵐ[condExpKernel P m ω]
        fun y => Real.exp (-1 / 2 * (c ω) ^ 2) * Real.exp (c ω * X y) := by
    filter_upwards [hcω] with y hy
    rw [hy, ← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae heq]
  rw [integral_const_mul]
  constructor
  · exact (integrable_congr heq).2 ((hint (c ω)).const_mul _)
  · change Real.exp (-1 / 2 * (c ω) ^ 2) * mgf X (condExpKernel P m ω) (c ω) ≤ 1
    calc
      _ ≤ Real.exp (-1 / 2 * (c ω) ^ 2) * Real.exp (1 * (c ω) ^ 2 / 2) := by
        gcongr
        exact hmgf (c ω)
      _ = 1 := by
        rw [← Real.exp_add]
        rw [show -1 / 2 * (c ω) ^ 2 + 1 * (c ω) ^ 2 / 2 = 0 by ring]
        exact Real.exp_zero

private lemma predictable_exp_integrable_condExp_le_one_scratch
    {Ω : Type} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (X c : Ω → ℝ) (hX : Measurable X) (hc : Measurable[m] c)
    (hsg : HasCondSubgaussianMGF m hm X 1 P) :
    let g := fun ω => Real.exp (c ω * X ω - 1 / 2 * (c ω) ^ 2)
    Integrable g P ∧ P[g | m] ≤ᵐ[P] 1 := by
  let g := fun ω => Real.exp (c ω * X ω - 1 / 2 * (c ω) ^ 2)
  have hc' : Measurable c := hc.mono hm le_rfl
  have hg : Measurable g :=
    Real.measurable_exp.comp <|
      (hc'.mul hX).sub (measurable_const.mul (hc'.pow_const 2))
  have hinner :=
    condKernel_integral_predictable_exp_le_one_scratch
      (P := P) (m := m) (mΩ := mΩ) hm X c hc hsg
  have hgint : Integrable g P := by
    have hgaes :
        AEStronglyMeasurable g (condExpKernel P m ∘ₘ P.trim hm) := by
      rw [condExpKernel_comp_trim (μ := P) hm]
      exact hg.aestronglyMeasurable
    rw [← condExpKernel_comp_trim (μ := P) hm]
    refine (Measure.integrable_comp_iff hgaes).2 ⟨?_, ?_⟩
    · exact hinner.mono fun _ hω => hω.1
    · have hqsm :
          StronglyMeasurable[m]
            (fun ω => ∫ y, ‖g y‖ ∂condExpKernel P m ω) :=
          hg.stronglyMeasurable.norm.integral_condExpKernel
      refine Integrable.mono (integrable_const (1 : ℝ)) hqsm.aestronglyMeasurable ?_
      filter_upwards [hinner] with ω hω
      have hnormeq :
          (∫ y, ‖g y‖ ∂condExpKernel P m ω) =
            ∫ y, g y ∂condExpKernel P m ω := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change |g y| = g y
          exact abs_of_pos (by exact Real.exp_pos _)
      rw [hnormeq, Real.norm_eq_abs, abs_of_nonneg]
      · simpa [g] using hω.2
      · exact integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨hgint, ?_⟩
  have hceq := condExp_ae_eq_trim_integral_condExpKernel (μ := P) hm hgint
  apply ae_of_ae_trim hm
  filter_upwards [hceq, hinner] with ω heq hω
  rw [heq]
  exact hω.2

private lemma predictable_mul_exp_integrable_condExp_le_scratch
    {Ω : Type} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) (X c u : Ω → ℝ)
    (hX : Measurable X) (hc : Measurable[m] c) (hu : Measurable[m] u)
    (huint : Integrable u P) (hunonneg : ∀ ω, 0 ≤ u ω)
    (hsg : HasCondSubgaussianMGF m hm X 1 P) :
    let g := fun ω => Real.exp (c ω * X ω - 1 / 2 * (c ω) ^ 2)
    Integrable (u * g) P ∧ P[u * g | m] ≤ᵐ[P] u := by
  let g := fun ω => Real.exp (c ω * X ω - 1 / 2 * (c ω) ^ 2)
  have hgdata :=
    predictable_exp_integrable_condExp_le_one_scratch
      (P := P) (m := m) (mΩ := mΩ) hm X c hX hc hsg
  have hg : Measurable g :=
    Real.measurable_exp.comp <|
      ((hc.mono hm le_rfl).mul hX).sub
        (measurable_const.mul ((hc.mono hm le_rfl).pow_const 2))
  have hprodmeas : Measurable (u * g) :=
    (hu.mono hm le_rfl).mul hg
  have hinner :=
    condKernel_integral_predictable_exp_le_one_scratch
      (P := P) (m := m) (mΩ := mΩ) hm X c hc hsg
  have hudiag :=
    ae_condExpKernel_eq_of_measurable_scratch
      (P := P) (m := m) (mΩ := mΩ) hm u hu
  have hprodint : Integrable (u * g) P := by
    have hpaes :
        AEStronglyMeasurable (u * g) (condExpKernel P m ∘ₘ P.trim hm) := by
      rw [condExpKernel_comp_trim (μ := P) hm]
      exact hprodmeas.aestronglyMeasurable
    rw [← condExpKernel_comp_trim (μ := P) hm]
    refine (Measure.integrable_comp_iff hpaes).2 ⟨?_, ?_⟩
    · filter_upwards [hinner, hudiag] with ω hgω huω
      have heq : (u * g) =ᵐ[condExpKernel P m ω] fun y => u ω * g y := by
        filter_upwards [huω] with y hy
        simp only [Pi.mul_apply, hy]
      exact (integrable_congr heq).2 (hgω.1.const_mul _)
    · have hqsm :
          StronglyMeasurable[m]
            (fun ω => ∫ y, ‖(u * g) y‖ ∂condExpKernel P m ω) :=
          hprodmeas.stronglyMeasurable.norm.integral_condExpKernel
      have huitrim : Integrable u (P.trim hm) :=
        huint.trim hm hu.stronglyMeasurable
      refine Integrable.mono huitrim hqsm.aestronglyMeasurable ?_
      filter_upwards [hinner, hudiag] with ω hgω huω
      have hnormeq :
          (∫ y, ‖(u * g) y‖ ∂condExpKernel P m ω) =
            u ω * ∫ y, g y ∂condExpKernel P m ω := by
        calc
          _ = ∫ y, u ω * g y ∂condExpKernel P m ω := by
            apply integral_congr_ae
            filter_upwards [huω] with y hy
            simp only [Pi.mul_apply, hy]
            change |u ω * g y| = u ω * g y
            exact abs_of_nonneg (mul_nonneg (hunonneg ω) (Real.exp_pos _).le)
          _ = _ := integral_const_mul (μ := condExpKernel P m ω) (u ω) g
      rw [hnormeq]
      change |u ω * ∫ y, g y ∂condExpKernel P m ω| ≤ |u ω|
      have hgint_nonneg : 0 ≤ ∫ y, g y ∂condExpKernel P m ω :=
        integral_nonneg fun _ => (Real.exp_pos _).le
      rw [abs_of_nonneg (mul_nonneg (hunonneg ω) hgint_nonneg),
        abs_of_nonneg (hunonneg ω)]
      exact mul_le_of_le_one_right (hunonneg ω) (by simpa [g] using hgω.2)
  refine ⟨hprodint, ?_⟩
  have hpull :=
    condExp_mul_of_stronglyMeasurable_left hu.stronglyMeasurable
      hprodint hgdata.1
  filter_upwards [hpull, hgdata.2] with ω hpullω hgow
  rw [hpullω]
  exact mul_le_of_le_one_right (hunonneg ω) hgow

private lemma selfNormalizedProcess_supermartingale_scratch
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 ≤ lam) (x : Fin d → ℝ) :
    Supermartingale (selfNormalizedProcess d lam η A x) ℱ P ∧
      ∀ ω : Ω, selfNormalizedProcess d lam η A x 0 ω ≤ 1 := by
  let M := selfNormalizedProcess d lam η A x
  have hMmeas : ∀ t : ℕ, Measurable[ℱ t] (M t) :=
    selfNormalizedProcess_measurable_scratch ℱ A η hA hη lam x
  have hMnonneg : ∀ t ω, 0 ≤ M t ω :=
    fun _ _ => (Real.exp_pos _).le
  have hMint : ∀ t : ℕ, Integrable (M t) P := by
    intro t
    induction t with
    | zero =>
        have hM0 :
            M 0 = fun _ => Real.exp (-1 / 2 * (lam * (x ⬝ᵥ x))) := by
          funext ω
          simp only [M, selfNormalizedProcess, selfNormalizedSum, Finset.range_zero,
            Finset.sum_empty, dotProduct_zero, regularizedDesignMatrix, zero_add]
          simp only [add_zero]
          rw [dot_smul_one_mulVec_scratch]
          ring
        rw [hM0]
        exact integrable_const _
    | succ t ih =>
        let c := fun ω => x ⬝ᵥ A (t + 1) ω
        let g := fun ω => Real.exp (c ω * η (t + 1) ω - 1 / 2 * (c ω) ^ 2)
        have hc : Measurable[ℱ t] c := by
          dsimp [c]
          fun_prop
        have hX : Measurable (η (t + 1)) :=
          (hη t).mono (ℱ.le (t + 1)) le_rfl
        have hprod :=
          predictable_mul_exp_integrable_condExp_le_scratch
            (P := P) (m := ℱ t) (mΩ := mΩ) (ℱ.le t)
            (η (t + 1)) c (M t) hX hc (hMmeas t) ih
            (hMnonneg t) (hsg t)
        have hsucc : M (t + 1) = M t * g := by
          funext ω
          exact selfNormalizedProcess_succ_scratch lam η A x t ω
        rw [hsucc]
        exact hprod.1
  have hcond : ∀ t : ℕ, P[M (t + 1) | ℱ t] ≤ᵐ[P] M t := by
    intro t
    let c := fun ω => x ⬝ᵥ A (t + 1) ω
    let g := fun ω => Real.exp (c ω * η (t + 1) ω - 1 / 2 * (c ω) ^ 2)
    have hc : Measurable[ℱ t] c := by
      dsimp [c]
      fun_prop
    have hX : Measurable (η (t + 1)) :=
      (hη t).mono (ℱ.le (t + 1)) le_rfl
    have hprod :=
      predictable_mul_exp_integrable_condExp_le_scratch
        (P := P) (m := ℱ t) (mΩ := mΩ) (ℱ.le t)
        (η (t + 1)) c (M t) hX hc (hMmeas t) (hMint t)
        (hMnonneg t) (hsg t)
    have hsucc : M (t + 1) = M t * g := by
      funext ω
      exact selfNormalizedProcess_succ_scratch lam η A x t ω
    rw [hsucc]
    exact hprod.2
  have hsuper : Supermartingale M ℱ P :=
    supermartingale_nat
      (fun t => (hMmeas t).stronglyMeasurable) hMint hcond
  refine ⟨hsuper, ?_⟩
  intro ω
  have hxx : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  change M 0 ω ≤ 1
  rw [show M 0 ω =
      Real.exp (-1 / 2 * (lam * (x ⬝ᵥ x))) by
    simp only [M, selfNormalizedProcess, selfNormalizedSum, Finset.range_zero,
      Finset.sum_empty, dotProduct_zero, regularizedDesignMatrix, zero_add]
    simp only [add_zero]
    rw [dot_smul_one_mulVec_scratch]
    ring]
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (mul_nonneg hlam hxx)

end BanditAlgorithm

theorem BanditAlgorithm.linear_bandit_fixed_direction_supermartingale
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 ≤ lam) (x : Fin d → ℝ) :
    Supermartingale (BanditAlgorithm.selfNormalizedProcess d lam η A x) ℱ P ∧
      ∀ ω : Ω, BanditAlgorithm.selfNormalizedProcess d lam η A x 0 ω ≤ 1 :=
  BanditAlgorithm.selfNormalizedProcess_supermartingale_scratch
    ℱ A η hA hη hsg hlam x


-- Accepted source: Harry_Xu, submission aee9c29b-ea26-4955-8af3-683e30c33304.

open MeasureTheory ProbabilityTheory Matrix

namespace BanditAlgorithm

private lemma selfNormalizedProcess_joint_measurable
    {Ω : Type} {mΩ : MeasurableSpace Ω} {d : ℕ}
    (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (lam : ℝ) (t : ℕ) :
    Measurable[MeasurableSpace.pi.prod (ℱ t)]
      (fun z : (Fin d → ℝ) × Ω =>
        selfNormalizedProcess d lam η A z.1 t z.2) := by
  letI : MeasurableSpace ((Fin d → ℝ) × Ω) :=
    MeasurableSpace.pi.prod (ℱ t)
  have hAp : ∀ s ∈ Finset.range t,
      Measurable[MeasurableSpace.pi.prod (ℱ t)]
        (fun z : (Fin d → ℝ) × Ω => A (s + 1) z.2) := by
    intro s hs
    have hst : s ≤ t := Nat.le_of_lt (Finset.mem_range.mp hs)
    exact ((hA s).mono (ℱ.mono hst) le_rfl).comp measurable_snd
  have hηp : ∀ s ∈ Finset.range t,
      Measurable[MeasurableSpace.pi.prod (ℱ t)]
        (fun z : (Fin d → ℝ) × Ω => η (s + 1) z.2) := by
    intro s hs
    have hst : s + 1 ≤ t := Finset.mem_range.mp hs
    exact ((hη s).mono (ℱ.mono hst) le_rfl).comp measurable_snd
  have hS (i : Fin d) :
      Measurable[MeasurableSpace.pi.prod (ℱ t)]
        (fun z : (Fin d → ℝ) × Ω =>
          (∑ s ∈ Finset.range t, η (s + 1) z.2 • A (s + 1) z.2) i) := by
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using
      Finset.measurable_sum (Finset.range t) (fun s hs =>
        (hηp s hs).mul ((measurable_pi_iff.mp (hAp s hs)) i))
  have hV (i j : Fin d) :
      Measurable[MeasurableSpace.pi.prod (ℱ t)]
        (fun z : (Fin d → ℝ) × Ω =>
          (lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
            ∑ s ∈ Finset.range t,
              vecMulVec (A (s + 1) z.2) (A (s + 1) z.2)) i j) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply]
    apply measurable_const.add
    exact Finset.measurable_sum _ fun s hs =>
      ((measurable_pi_iff.mp (hAp s hs)) i).mul
        ((measurable_pi_iff.mp (hAp s hs)) j)
  unfold selfNormalizedProcess selfNormalizedSum regularizedDesignMatrix
  apply Real.measurable_exp.comp
  apply Measurable.sub
  · simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_iff.mp measurable_fst) i).mul
        (hS i)
  · apply measurable_const.mul
    simp only [dotProduct, Matrix.mulVec]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_iff.mp measurable_fst) i).mul <|
        Finset.measurable_sum _ fun j _ =>
          ((hV i j).mul ((measurable_pi_iff.mp measurable_fst) j))

end BanditAlgorithm

theorem BanditAlgorithm.linear_bandit_mixture_supermartingale
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Measure (Fin d → ℝ)) [IsProbabilityMeasure h]
    (hInt : ∀ (t : ℕ) (ω : Ω),
      Integrable (fun x => BanditAlgorithm.selfNormalizedProcess d lam η A x t ω) h) :
    (∀ x : Fin d → ℝ,
      Supermartingale (BanditAlgorithm.selfNormalizedProcess d lam η A x) ℱ P ∧
        ∀ ω : Ω, BanditAlgorithm.selfNormalizedProcess d lam η A x 0 ω ≤ 1) ∧
    Supermartingale
      (fun (t : ℕ) (ω : Ω) =>
        ∫ x, BanditAlgorithm.selfNormalizedProcess d lam η A x t ω ∂h) ℱ P ∧
    (∀ ω : Ω,
      (∫ x, BanditAlgorithm.selfNormalizedProcess d lam η A x 0 ω ∂h) ≤ 1) ∧
    (lam = 0 → ∀ ω : Ω,
      (∫ x, BanditAlgorithm.selfNormalizedProcess d lam η A x 0 ω ∂h) = 1) := by
  let F := fun (t : ℕ) (x : Fin d → ℝ) (ω : Ω) =>
    BanditAlgorithm.selfNormalizedProcess d lam η A x t ω
  let Z := fun (t : ℕ) (ω : Ω) => ∫ x, F t x ω ∂h
  have hfixed : ∀ x : Fin d → ℝ,
      Supermartingale (F · x) ℱ P ∧ ∀ ω : Ω, F 0 x ω ≤ 1 := by
    intro x
    exact BanditAlgorithm.linear_bandit_fixed_direction_supermartingale
      ℱ A η hA hη hsg hlam x
  have hjointFil (t : ℕ) :
      Measurable[MeasurableSpace.pi.prod (ℱ t)]
        (Function.uncurry (F t)) :=
    BanditAlgorithm.selfNormalizedProcess_joint_measurable
      ℱ A η hA hη lam t
  have hjoint (t : ℕ) :
      Measurable (Function.uncurry (F t)) := by
    exact (hjointFil t).mono
      (sup_le_sup (MeasurableSpace.comap_mono le_rfl)
        (MeasurableSpace.comap_mono (ℱ.le t))) le_rfl
  have hmean_le_one (t : ℕ) (x : Fin d → ℝ) :
      (∫ ω, F t x ω ∂P) ≤ 1 := by
    calc
      (∫ ω, F t x ω ∂P) ≤ ∫ ω, F 0 x ω ∂P := by
        simpa only [Measure.restrict_univ] using
          (hfixed x).1.setIntegral_le (Nat.zero_le t)
            (MeasurableSet.univ : MeasurableSet[ℱ 0] (Set.univ : Set Ω))
      _ ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
        integral_mono ((hfixed x).1.integrable 0) (integrable_const 1) (hfixed x).2
      _ = 1 := by simp
  have hprodint (t : ℕ) :
      Integrable (Function.uncurry (F t)) (h.prod P) := by
    have hsm : AEStronglyMeasurable (Function.uncurry (F t)) (h.prod P) :=
      (hjoint t).aestronglyMeasurable
    rw [integrable_prod_iff hsm]
    constructor
    · exact Filter.Eventually.of_forall fun x => (hfixed x).1.integrable t
    · have houtsm :
          StronglyMeasurable (fun x => ∫ ω, ‖F t x ω‖ ∂P) :=
        (hjoint t).stronglyMeasurable.norm.integral_prod_right
      refine Integrable.mono (integrable_const (1 : ℝ))
        houtsm.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun x => by
        have hnorm :
            (∫ ω, ‖F t x ω‖ ∂P) = ∫ ω, F t x ω ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            change ‖F t x ω‖ = F t x ω
            rw [Real.norm_eq_abs, abs_of_nonneg]
            exact (Real.exp_pos _).le
        change ‖∫ ω, ‖F t x ω‖ ∂P‖ ≤ ‖(1 : ℝ)‖
        rw [hnorm, Real.norm_eq_abs, abs_of_nonneg]
        · simpa using hmean_le_one t x
        · exact integral_nonneg fun _ => (Real.exp_pos _).le
  have hZadapt : StronglyAdapted ℱ Z := by
    intro t
    letI : MeasurableSpace Ω := ℱ t
    letI : MeasurableSpace ((Fin d → ℝ) × Ω) :=
      MeasurableSpace.pi.prod (ℱ t)
    exact (hjointFil t).stronglyMeasurable.integral_prod_left
  have hZint : ∀ t, Integrable (Z t) P := by
    intro t
    exact (hprodint t).integral_prod_right
  have hZsuper : Supermartingale Z ℱ P := by
    refine supermartingale_of_setIntegral_succ_le hZadapt hZint ?_
    intro t s hs
    let G := fun (u : ℕ) (x : Fin d → ℝ) (ω : Ω) =>
      s.indicator (F u x) ω
    have hsfull : MeasurableSet s := (ℱ.le t) s hs
    have hsprod : MeasurableSet {z : (Fin d → ℝ) × Ω | z.2 ∈ s} :=
      measurable_snd hsfull
    have hGint (u : ℕ) :
        Integrable (Function.uncurry (G u)) (h.prod P) := by
      exact (hprodint u).indicator hsprod
    have hGxint (u : ℕ) :
        Integrable (fun x => ∫ ω, G u x ω ∂P) h :=
      (hGint u).integral_prod_left
    calc
      (∫ ω in s, Z (t + 1) ω ∂P) =
          ∫ ω, ∫ x, G (t + 1) x ω ∂h ∂P := by
            rw [← integral_indicator hsfull]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              by_cases hω : ω ∈ s
              · simp [Z, G, hω]
              · simp [Z, G, hω]
      _ = ∫ x, ∫ ω, G (t + 1) x ω ∂P ∂h :=
        (integral_integral_swap (hGint (t + 1))).symm
      _ ≤ ∫ x, ∫ ω, G t x ω ∂P ∂h := by
        apply integral_mono (hGxint (t + 1)) (hGxint t)
        intro x
        simpa only [G, integral_indicator hsfull, Nat.succ_eq_add_one] using
          (hfixed x).1.setIntegral_le (Nat.le_succ t) hs
      _ = ∫ ω, ∫ x, G t x ω ∂h ∂P :=
        integral_integral_swap (hGint t)
      _ = ∫ ω in s, Z t ω ∂P := by
        rw [← integral_indicator hsfull]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          by_cases hω : ω ∈ s
          · simp [Z, G, hω]
          · simp [Z, G, hω]
  refine ⟨hfixed, hZsuper, ?_, ?_⟩
  · intro ω
    exact (integral_mono (hInt 0 ω) (integrable_const 1)
      (fun x => (hfixed x).2 ω)).trans_eq (by simp)
  · intro hlam0 ω
    have hzero : ∀ x : Fin d → ℝ, F 0 x ω = 1 := by
      intro x
      simp [F, BanditAlgorithm.selfNormalizedProcess,
        BanditAlgorithm.selfNormalizedSum,
        BanditAlgorithm.regularizedDesignMatrix, hlam0]
    calc
      (∫ x, BanditAlgorithm.selfNormalizedProcess d lam η A x 0 ω ∂h) =
          ∫ _ : Fin d → ℝ, (1 : ℝ) ∂h :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hzero x)
      _ = 1 := by simp


-- Accepted source: Harry_Xu, submission 34cef495-9130-4b11-b329-bfb948d16314.

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.nonnegative_supermartingale_ville
    {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ)
    (hf : Supermartingale f ℱ P)
    (hnonneg : ∀ t : ℕ, 0 ≤ᵐ[P] f t)
    (h0 : ∀ᵐ ω ∂P, f 0 ω ≤ 1)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t : ℕ, 1 / δ ≤ f t ω} ≤ δ := by
  classical
  have hδpos : 0 < δ := hδ.1
  let ε : ℝ := 1 / δ
  have hεpos : 0 < ε := one_div_pos.mpr hδpos
  let E : ℕ → Set Ω := fun n => {ω | ∃ t ≤ n, ε ≤ f t ω}
  have hE_meas : ∀ n, MeasurableSet (E n) := by
    intro n
    change MeasurableSet {ω | ∃ t ≤ n, ε ≤ f t ω}
    rw [show {ω | ∃ t ≤ n, ε ≤ f t ω} =
        ⋃ t ∈ Finset.range (n + 1), {ω | ε ≤ f t ω} by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
      aesop]
    exact Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_le measurable_const
        ((hf.stronglyMeasurable t).measurable.le (ℱ.le t))
  have hE_mono : Monotone E := by
    intro n m hnm ω hω
    rcases hω with ⟨t, htn, ht⟩
    exact ⟨t, htn.trans hnm, ht⟩
  have hEn : ∀ n, P.real (E n) ≤ δ := by
    intro n
    let τ : Ω → ℕ∞ :=
      fun ω => (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)
    have hτ_stop : IsStoppingTime ℱ τ :=
      hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hτ_le : ∀ ω, τ ω ≤ n := fun ω => by
      change (↑(hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω) : ℕ∞) ≤ ↑n
      exact_mod_cast
        (hittingBtwn_le (u := f) (s := {y : ℝ | ε ≤ y}) (n := 0) (m := n) ω)
    have hzero_le_τ : (fun _ : Ω => (0 : ℕ∞)) ≤ τ := by
      intro ω
      exact bot_le
    have hτ_int : Integrable (stoppedValue f τ) P :=
      integrable_stoppedValue ℕ hτ_stop hf.integrable hτ_le
    have hτ_nonneg : 0 ≤ᵐ[P] stoppedValue f τ := by
      have hall : ∀ᵐ ω ∂P, ∀ t : ℕ, 0 ≤ f t ω := ae_all_iff.2 hnonneg
      filter_upwards [hall] with ω hω
      simpa only [Pi.zero_apply, stoppedValue] using hω (τ ω).untopA
    have hτ_expect_le : ∫ ω, stoppedValue f τ ω ∂P ≤ ∫ ω, f 0 ω ∂P := by
      have h :=
        hf.neg.expected_stoppedValue_mono
          (isStoppingTime_const ℱ (0 : ℕ)) hτ_stop hzero_le_τ hτ_le
      have hnegstop : stoppedValue (-f) τ = -stoppedValue f τ := by
        funext ω
        simp [stoppedValue]
      rw [stoppedValue_const, hnegstop] at h
      have hleft :
          (∫ x, (-f) 0 x ∂P) = -(∫ x, f 0 x ∂P) := by
        simpa only [Pi.neg_apply] using
          (integral_neg (μ := P) (f := fun x => f 0 x))
      have hright :
          (∫ x, (-stoppedValue f τ) x ∂P) =
            -(∫ x, stoppedValue f τ x ∂P) := by
        exact integral_neg (μ := P) (f := stoppedValue f τ)
      rw [hleft, hright] at h
      linarith
    have hf0_le_one : ∫ ω, f 0 ω ∂P ≤ 1 := by
      calc
        ∫ ω, f 0 ω ∂P ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono_ae (hf.integrable 0) (integrable_const 1) h0
        _ = 1 := by simp
    have hmarkov :
        ε * P.real {ω | ε ≤ stoppedValue f τ ω} ≤
          ∫ ω, stoppedValue f τ ω ∂P :=
      mul_meas_ge_le_integral_of_nonneg hτ_nonneg hτ_int ε
    have hset : {ω | ε ≤ stoppedValue f τ ω} = E n := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hhit
        by_contra hno
        simp only [E, Set.mem_setOf_eq, not_exists, not_and] at hno
        have hnone : ¬ ∃ t ∈ Set.Icc (0 : ℕ) n, f t ω ∈ {y : ℝ | ε ≤ y} := by
          push Not
          rintro t ⟨_, htn⟩ ht
          exact hno t htn ht
        have hτeq : τ ω = n := by
          change (↑(if ∃ j ∈ Set.Icc (0 : ℕ) n, f j ω ∈ {y : ℝ | ε ≤ y}
            then sInf (Set.Icc 0 n ∩ {i : ℕ | f i ω ∈ {y : ℝ | ε ≤ y}})
            else n) : ℕ∞) = ↑n
          rw [if_neg hnone]
        rw [show stoppedValue f τ ω = f n ω by simp [stoppedValue, hτeq]] at hhit
        exact (hno n le_rfl) hhit
      · rintro ⟨t, htn, ht⟩
        have hex : ∃ j ∈ Set.Icc (0 : ℕ) n, f j ω ∈ {y : ℝ | ε ≤ y} :=
          ⟨t, ⟨Nat.zero_le t, htn⟩, ht⟩
        have hmem := stoppedValue_hittingBtwn_mem hex
        exact hmem
    rw [hset] at hmarkov
    have hprod : ε * P.real (E n) ≤ 1 :=
      hmarkov.trans (hτ_expect_le.trans hf0_le_one)
    calc
      P.real (E n) ≤ 1 / ε := (le_div_iff₀ hεpos).2 (by simpa [mul_comm] using hprod)
      _ = δ := by simp [ε]
  have hUnion :
      {ω | ∃ t : ℕ, 1 / δ ≤ f t ω} = ⋃ n : ℕ, E n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, ε]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t, le_rfl, ht⟩
    · rintro ⟨n, t, _, ht⟩
      exact ⟨t, ht⟩
  rw [hUnion]
  rw [measureReal_def, hE_mono.measure_iUnion,
    ENNReal.toReal_iSup (fun n => measure_ne_top P (E n))]
  exact ciSup_le hEn


-- Accepted source: Harry_Xu, submission 166b3e3d-2ca5-4b2a-ade4-cdfad74ab4e7.

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal

namespace BanditAlgorithm

private lemma dot_mulVec_comm_of_isHermitian
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym : K j i = K i j := by
    have heq := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hK.eq
    simpa using heq
  rw [hsym]
  ring

private lemma quadratic_completion
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S x : Fin d → ℝ) :
    x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x) =
      1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S) -
        1 / 2 * ((x - K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (x - K⁻¹ *ᵥ S)) := by
  have hunit : IsUnit K := hK.isUnit
  have hdetunit : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp hunit
  have hKS : K *ᵥ (K⁻¹ *ᵥ S) = S := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdetunit]
    exact one_mulVec S
  have hcomm (u v : Fin d → ℝ) :
      u ⬝ᵥ K *ᵥ v = v ⬝ᵥ K *ᵥ u :=
    dot_mulVec_comm_of_isHermitian hK.isHermitian u v
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hKS, hcomm (K⁻¹ *ᵥ S) x, hKS,
    dotProduct_comm (K⁻¹ *ᵥ S) S]
  ring

private lemma sqrt_mulVec_sq
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (x : Fin d → ℝ) :
    x ⬝ᵥ K *ᵥ x =
      (CFC.sqrt K *ᵥ x) ⬝ᵥ (CFC.sqrt K *ᵥ x) := by
  let B := CFC.sqrt K
  have hBps : B.PosSemidef :=
    nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hBB : B * B = K :=
    CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  have hxvec : x ᵥ* B = B *ᵥ x := by
    have heq := vecMul_conjTranspose B x
    rw [hBps.isHermitian.eq] at heq
    simpa [B] using heq
  calc
    x ⬝ᵥ K *ᵥ x = x ⬝ᵥ (B * B) *ᵥ x := by rw [hBB]
    _ = x ⬝ᵥ B *ᵥ (B *ᵥ x) := by rw [mulVec_mulVec]
    _ = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by rw [dotProduct_mulVec, hxvec]

private lemma isotropic_b_integrable {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-b * r ^ 2)) :=
    fun _ => integrable_exp_neg_mul_sq hb
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma isotropic_b_integral (d : ℕ) (b : ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (-b * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / b)) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-b * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-b * r ^ 2))]
  rw [show (∫ r : ℝ, Real.exp (-b * r ^ 2)) =
      Real.sqrt (Real.pi / b) by exact integral_gaussian b,
    Finset.prod_const]
  simp

private lemma isotropic_integrable (d : ℕ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) := by
  have hcoord : ∀ i : Fin d,
      Integrable (fun r : ℝ => Real.exp (-1 / 2 * r ^ 2)) :=
    fun _ => by
      simpa only [neg_div] using
        integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
  have hprod := Integrable.fintype_prod hcoord
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, volume_pi]
  exact hprod

private lemma isotropic_integral (d : ℕ) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  have heq : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ x))) =
      fun x => ∏ i : Fin d, Real.exp (-1 / 2 * (x i) ^ 2) := by
    funext x
    simp only [dotProduct, ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, integral_fintype_prod_volume_eq_prod
    (f := fun (_ : Fin d) (r : ℝ) => Real.exp (-1 / 2 * r ^ 2))]
  have hscalar :
      (∫ r : ℝ, Real.exp (-1 / 2 * r ^ 2)) =
        Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
    simpa only [neg_div] using integral_gaussian (1 / 2 : ℝ)
  rw [hscalar, Finset.prod_const]
  simp

private lemma centered_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hmap :
      Measure.map (toLin' B) volume =
        ENNReal.ofReal (abs B.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet
  have hgsmul :
      Integrable (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    rw [hmap]
    exact (isotropic_integrable d).smul_measure (by finiteness)
  have hcomp := hgsmul.comp_measurable hBmeas
  have hfun : (fun x : Fin d → ℝ => Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) ∘ (toLin' B) := by
    funext x
    simp only [B, Function.comp_apply, toLin'_apply, sqrt_mulVec_sq hK]
  rw [hfun]
  exact hcomp

private lemma centered_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    (∫ x : Fin d → ℝ, Real.exp (-1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
      (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let B := CFC.sqrt K
  have hBdet : B.det ≠ 0 := by
    rw [hK.posSemidef.det_sqrt]
    simpa using (Real.sqrt_pos.2 hK.det_pos).ne'
  have hBmeas : Measurable (toLin' B) :=
    (LinearMap.continuous_on_pi (toLin' B)).measurable
  have hgsm :
      AEStronglyMeasurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y)))
        (Measure.map (toLin' B) volume) := by
    have hm : Measurable
        (fun y : Fin d → ℝ => Real.exp (-1 / 2 * (y ⬝ᵥ y))) := by
      simp only [dotProduct]
      fun_prop
    exact hm.aestronglyMeasurable
  have hi := integral_map hBmeas.aemeasurable hgsm
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hBdet,
    integral_smul_measure] at hi
  rw [isotropic_integral d] at hi
  simpa only [B, toLin'_apply, sqrt_mulVec_sq hK, smul_eq_mul] using hi.symm

private lemma shifted_quadratic_integrable
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ =>
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  rw [heq]
  exact ((centered_quadratic_integrable hK).comp_sub_right c).const_mul _

private lemma shifted_quadratic_integral
    {d : ℕ} {K : Matrix (Fin d) (Fin d) ℝ}
    (hK : K.PosDef) (S : Fin d → ℝ) :
    (∫ x : Fin d → ℝ,
      Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
        (ENNReal.ofReal (abs (CFC.sqrt K).det⁻¹)).toReal *
          (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d := by
  let c := K⁻¹ *ᵥ S
  have heq :
      (fun x : Fin d → ℝ =>
        Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x))) =
      fun x =>
        Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
          Real.exp (-1 / 2 * ((x - c) ⬝ᵥ K *ᵥ (x - c))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    convert quadratic_completion hK S x using 1 <;> simp only [c] <;> ring
  have htrans :
      (∫ a : Fin d → ℝ,
        Real.exp (-1 / 2 * ((a - c) ⬝ᵥ K *ᵥ (a - c)))) =
      ∫ a : Fin d → ℝ, Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a)) :=
    integral_sub_right_eq_self
      (fun a : Fin d → ℝ => Real.exp (-1 / 2 * (a ⬝ᵥ K *ᵥ a))) c
  rw [heq, integral_const_mul, htrans, centered_quadratic_integral hK]
  ring

private lemma gaussian_normalization
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {K : Matrix (Fin d) (Fin d) ℝ} (hK : K.PosDef) :
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d =
      Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
  let L : ℝ :=
    ((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
          |(CFC.sqrt K).det|⁻¹ *
        (Real.sqrt Real.pi * Real.sqrt 2) ^ d
  let R : ℝ := Real.exp (-1 / 2 * Real.log (K.det / lam ^ d))
  have hdet : 0 < K.det := hK.det_pos
  have hdetB :
      (CFC.sqrt K).det = Real.sqrt K.det := by
    simpa using hK.posSemidef.det_sqrt
  have hBpos : 0 < (CFC.sqrt K).det := by
    rw [hdetB]
    exact Real.sqrt_pos.2 hdet
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  apply (sq_eq_sq₀ hL hR).mp
  have hJ2 :
      ((Real.sqrt (Real.pi / (lam / 2))) ^ d) ^ 2 =
        (Real.pi / (lam / 2)) ^ d := by
    calc
      _ = (Real.sqrt (Real.pi / (lam / 2)) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        rw [Real.sq_sqrt]
        positivity
  have hB2 : |(CFC.sqrt K).det| ^ 2 = K.det := by
    rw [abs_of_pos hBpos, hdetB, Real.sq_sqrt hdet.le]
  have hC2 :
      ((Real.sqrt Real.pi * Real.sqrt 2) ^ d) ^ 2 =
        (Real.pi * 2) ^ d := by
    calc
      _ = ((Real.sqrt Real.pi * Real.sqrt 2) ^ 2) ^ d := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = _ := by
        congr 1
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hratio : 0 < K.det / lam ^ d := div_pos hdet (pow_pos hlam d)
  change L ^ 2 = R ^ 2
  have hR2 : R ^ 2 = (K.det / lam ^ d)⁻¹ := by
    dsimp [R]
    rw [← Real.exp_nat_mul]
    have hexpArg :
        (↑(2 : ℕ) : ℝ) * (-1 / 2 * Real.log (K.det / lam ^ d)) =
          -Real.log (K.det / lam ^ d) := by
      ring
    rw [hexpArg]
    rw [Real.exp_neg, Real.exp_log hratio]
  rw [hR2]
  dsimp [L]
  rw [mul_pow, mul_pow, inv_pow, inv_pow, hJ2, hB2, hC2]
  field_simp [hlam.ne', hdet.ne', Real.pi_ne_zero]
  rw [← mul_pow]
  congr 1
  field_simp [hlam.ne']

end BanditAlgorithm

theorem BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ∃ h : Measure (Fin d → ℝ),
      IsProbabilityMeasure h ∧
      ∀ (S : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ),
        V.PosSemidef →
        Integrable
            (fun x => Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) h ∧
          (∫ x, Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂h) =
            Real.exp
              (1 / 2 *
                (S ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                  Real.log
                    ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det / lam ^ d))) := by
  let b : ℝ := lam / 2
  let J : ℝ := (Real.sqrt (Real.pi / b)) ^ d
  let q : (Fin d → ℝ) → ℝ :=
    fun x => J⁻¹ * Real.exp (-b * (x ⬝ᵥ x))
  let ρ : (Fin d → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (q x)
  let h : Measure (Fin d → ℝ) := volume.withDensity ρ
  have hb : 0 < b := by dsimp [b]; positivity
  have hJ : 0 < J := by
    dsimp [J]
    positivity
  have hqnonneg : ∀ x, 0 ≤ q x := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hJ.le) (Real.exp_pos _).le
  have hqmeas : Measurable q := by
    dsimp [q]
    simp only [dotProduct]
    fun_prop
  have hρmeas : Measurable ρ :=
    hqmeas.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ρ x < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hqint : Integrable q := by
    dsimp [q]
    exact (BanditAlgorithm.isotropic_b_integrable hb).const_mul _
  have hqone : (∫ x, q x) = 1 := by
    dsimp [q]
    rw [integral_const_mul, BanditAlgorithm.isotropic_b_integral d b]
    dsimp [J]
    exact inv_mul_cancel₀ hJ.ne'
  have hhprob : IsProbabilityMeasure h := by
    change IsProbabilityMeasure (volume.withDensity ρ)
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hqint
      (Filter.Eventually.of_forall hqnonneg)]
    rw [hqone]
    simp
  refine ⟨h, hhprob, ?_⟩
  intro S V hV
  let K : Matrix (Fin d) (Fin d) ℝ :=
    lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V
  have hlamI : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hlam
  have hK : K.PosDef := hlamI.add_posSemidef hV
  have hquad (x : Fin d → ℝ) :
      x ⬝ᵥ K *ᵥ x = lam * (x ⬝ᵥ x) + x ⬝ᵥ V *ᵥ x := by
    simp only [K, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul]
    ring
  have hcombine (x : Fin d → ℝ) :
      (ρ x).toReal *
          Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) =
        J⁻¹ * Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
    rw [show ρ x = ENNReal.ofReal (q x) by rfl,
      ENNReal.toReal_ofReal (hqnonneg x)]
    dsimp [q]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    rw [hquad]
    dsimp [b]
    ring
  constructor
  · change Integrable
      (fun x => Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)))
      (volume.withDensity ρ)
    rw [integrable_withDensity_iff_integrable_smul' hρmeas hρtop]
    have hi :=
      (BanditAlgorithm.shifted_quadratic_integrable hK S).const_mul J⁻¹
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      simpa only [smul_eq_mul] using (hcombine x).symm
  · change (∫ x, Real.exp
        (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂volume.withDensity ρ) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
    have hint :
        (∫ x, (ρ x).toReal •
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) =
          J⁻¹ * ∫ x,
            Real.exp (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ K *ᵥ x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simpa only [smul_eq_mul] using hcombine x
    rw [hint, BanditAlgorithm.shifted_quadratic_integral hK S]
    have hnorm := BanditAlgorithm.gaussian_normalization hlam hK
    have hJdef :
        J = (Real.sqrt (Real.pi / (lam / 2))) ^ d := by
      rfl
    calc
      J⁻¹ *
          (Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
              (ENNReal.ofReal |(CFC.sqrt K).det⁻¹|).toReal *
            (Real.sqrt (Real.pi / (1 / 2 : ℝ))) ^ d) =
          Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            (((Real.sqrt (Real.pi / (lam / 2))) ^ d)⁻¹ *
              |(CFC.sqrt K).det|⁻¹ *
                (Real.sqrt Real.pi * Real.sqrt 2) ^ d) := by
            rw [hJdef]
            have hBpos : 0 < (CFC.sqrt K).det := by
              rw [hK.posSemidef.det_sqrt]
              simpa using Real.sqrt_pos.2 hK.det_pos
            rw [ENNReal.toReal_ofReal (abs_nonneg _),
              abs_inv, abs_of_pos hBpos]
            have hsqrt :
                Real.sqrt (Real.pi / (1 / 2 : ℝ)) =
                  Real.sqrt Real.pi * Real.sqrt 2 := by
              rw [show Real.pi / (1 / 2 : ℝ) = Real.pi * 2 by ring,
                Real.sqrt_mul Real.pi_pos.le]
            rw [hsqrt]
            ring
      _ = Real.exp (1 / 2 * (S ⬝ᵥ K⁻¹ *ᵥ S)) *
            Real.exp (-1 / 2 * Real.log (K.det / lam ^ d)) := by
          rw [hnorm]
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ K⁻¹ *ᵥ S - Real.log (K.det / lam ^ d))) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ = Real.exp
            (1 / 2 *
              (S ⬝ᵥ
                  (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                Real.log
                  ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det /
                    lam ^ d))) := by
          rfl


-- Accepted source: Harry_Xu, submission aca768b6-ad04-4a1b-b695-3997b5aba70d.

open MeasureTheory ProbabilityTheory Matrix

namespace BanditAlgorithm

private lemma sum_vecMulVec_posSemidef
    {Ω : Type} {d : ℕ} (A : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    (∑ s ∈ Finset.range t,
      vecMulVec (A (s + 1) ω) (A (s + 1) ω)).PosSemidef := by
  apply Finset.sum_induction _ _ (fun _ _ h₁ h₂ => h₁.add h₂) .zero
  intro s hs
  simpa using posSemidef_vecMulVec_self_star (A (s + 1) ω)

end BanditAlgorithm

theorem BanditAlgorithm.self_normalized_martingale_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t : ℕ,
        2 * Real.log (1 / δ)
            + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d)
          ≤ BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
              (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                BanditAlgorithm.selfNormalizedSum d η A t ω} ≤ δ := by
  rcases BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
      (d := d) hlam with ⟨h, hhprob, hgauss⟩
  letI : IsProbabilityMeasure h := hhprob
  let F := fun (t : ℕ) (x : Fin d → ℝ) (ω : Ω) =>
    BanditAlgorithm.selfNormalizedProcess d 0 η A x t ω
  let Z := fun (t : ℕ) (ω : Ω) => ∫ x, F t x ω ∂h
  have hformula (t : ℕ) (ω : Ω) :
      Integrable (fun x => F t x ω) h ∧
      Z t ω =
        Real.exp (1 / 2 *
          (BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
              (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                BanditAlgorithm.selfNormalizedSum d η A t ω -
            Real.log
              ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d))) := by
    let V : Matrix (Fin d) (Fin d) ℝ :=
      ∑ s ∈ Finset.range t,
        vecMulVec (A (s + 1) ω) (A (s + 1) ω)
    have hV : V.PosSemidef :=
      BanditAlgorithm.sum_vecMulVec_posSemidef A t ω
    have hg := hgauss (BanditAlgorithm.selfNormalizedSum d η A t ω) V hV
    simpa only [F, Z, BanditAlgorithm.selfNormalizedProcess,
      BanditAlgorithm.regularizedDesignMatrix, V, zero_smul, zero_add] using hg
  have hmix :=
    BanditAlgorithm.linear_bandit_mixture_supermartingale
      ℱ A η hA hη hsg (lam := 0) (by norm_num) h
        (fun t ω => (hformula t ω).1)
  have hZsuper : Supermartingale Z ℱ P := hmix.2.1
  have hZnonneg : ∀ t : ℕ, 0 ≤ᵐ[P] Z t := by
    intro t
    exact Filter.Eventually.of_forall fun ω => by
      rw [(hformula t ω).2]
      exact (Real.exp_pos _).le
  have hZzero : ∀ᵐ ω ∂P, Z 0 ω ≤ 1 :=
    Filter.Eventually.of_forall hmix.2.2.1
  have hville :=
    BanditAlgorithm.nonnegative_supermartingale_ville
      ℱ Z hZsuper hZnonneg hZzero hδ
  apply (measureReal_mono ?_).trans hville
  intro ω hω
  rcases hω with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  rw [(hformula t ω).2]
  apply (Real.log_le_iff_le_exp ?_).mp
  · have hlog :
        Real.log (1 / δ) ≤
          1 / 2 *
            (BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
                (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                  BanditAlgorithm.selfNormalizedSum d η A t ω -
              Real.log
                ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d)) := by
      linarith
    exact hlog
  · exact one_div_pos.mpr hδ.1



set_option autoImplicit false

open Matrix

namespace EllipsoidProof

lemma quadratic_symm {d : Nat} {K : Matrix (Fin d) (Fin d) Real}
    (hK : K.IsHermitian) (x y : Fin d → Real) :
    x ⬝ᵥ K *ᵥ y = y ⬝ᵥ K *ᵥ x := by
  have hxy : x ᵥ* K = K *ᵥ x := by
    have h := vecMul_conjTranspose K x
    rw [hK.eq] at h
    simpa using h
  rw [dotProduct_mulVec, hxy, dotProduct_comm]

lemma quadratic_triangle {d : Nat} {K : Matrix (Fin d) (Fin d) Real}
    (hK : K.PosSemidef) (x y : Fin d → Real) :
    Real.sqrt ((x + y) ⬝ᵥ K *ᵥ (x + y)) ≤
      Real.sqrt (x ⬝ᵥ K *ᵥ x) + Real.sqrt (y ⬝ᵥ K *ᵥ y) := by
  let c : PreInnerProductSpace.Core Real (Fin d → Real) :=
    { inner := fun x y => x ⬝ᵥ K *ᵥ y
      conj_inner_symm := fun x y => by
        simpa using quadratic_symm hK.isHermitian y x
      re_inner_nonneg := fun x => by
        simpa using hK.dotProduct_mulVec_nonneg x
      add_left := fun x y z => add_dotProduct x y (K *ᵥ z)
      smul_left := fun x y r => by simp [smul_dotProduct] }
  have hxy := InnerProductSpace.Core.norm_inner_le_norm (c := c) x y
  change |x ⬝ᵥ K *ᵥ y| ≤ Real.sqrt (x ⬝ᵥ K *ᵥ x) *
    Real.sqrt (y ⬝ᵥ K *ᵥ y) at hxy
  have hx : 0 ≤ x ⬝ᵥ K *ᵥ x := by simpa using hK.dotProduct_mulVec_nonneg x
  have hy : 0 ≤ y ⬝ᵥ K *ᵥ y := by simpa using hK.dotProduct_mulVec_nonneg y
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hxy' := (le_abs_self (x ⬝ᵥ K *ᵥ y)).trans hxy
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [quadratic_symm hK.isHermitian y x]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

lemma gram_posSemidef {d : Nat} (a : Nat → Fin d → Real) (t : Nat) :
    (∑ s ∈ Finset.range t, vecMulVec (a s) (a s)).PosSemidef := by
  apply Finset.sum_induction _ _ (fun _ _ hx hy => hx.add hy) .zero
  intro s hs
  simpa using Matrix.posSemidef_vecMulVec_self_star (a s)

lemma ridge_bound {d : Nat} {lam : Real} (hlam : 0 < lam)
    (G : Matrix (Fin d) (Fin d) Real) (hG : G.PosSemidef)
    (S θ : Fin d → Real) :
    let K := lam • (1 : Matrix (Fin d) (Fin d) Real) + G
    let e := K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ)
    Real.sqrt (e ⬝ᵥ K *ᵥ e) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) + Real.sqrt (S ⬝ᵥ K⁻¹ *ᵥ S) := by
  dsimp only
  let K := lam • (1 : Matrix (Fin d) (Fin d) Real) + G
  have hK : K.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hG
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hcancel (x : Fin d → Real) : K *ᵥ (K⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv K hdet, one_mulVec]
  have hfirst : (K⁻¹ *ᵥ S) ⬝ᵥ K *ᵥ (K⁻¹ *ᵥ S) = S ⬝ᵥ K⁻¹ *ᵥ S := by
    rw [hcancel, dotProduct_comm]
  have hsecond : (-(lam • (K⁻¹ *ᵥ θ))) ⬝ᵥ K *ᵥ (-(lam • (K⁻¹ *ᵥ θ))) =
      lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ) := by
    simp only [mulVec_neg, mulVec_smul, neg_dotProduct, dotProduct_neg,
      smul_dotProduct, dotProduct_smul, hcancel, smul_eq_mul]
    rw [dotProduct_comm (K⁻¹ *ᵥ θ) θ]
    ring
  have hbias : lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ) ≤ lam * (θ ⬝ᵥ θ) := by
    let u := K⁻¹ *ᵥ θ
    have hu : K *ᵥ u = θ := hcancel θ
    have hquad : lam * (u ⬝ᵥ u) ≤ θ ⬝ᵥ u := by
      have hnonneg := hG.dotProduct_mulVec_nonneg u
      have hidentity : u ⬝ᵥ K *ᵥ u = lam * (u ⬝ᵥ u) + u ⬝ᵥ G *ᵥ u := by
        simp [K, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]
      rw [hu, dotProduct_comm u θ] at hidentity
      simp only [star_trivial] at hnonneg
      linarith
    have hnorm : 0 ≤ (θ - lam • u) ⬝ᵥ (θ - lam • u) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hexpand : (θ - lam • u) ⬝ᵥ (θ - lam • u) =
        θ ⬝ᵥ θ - 2 * lam * (θ ⬝ᵥ u) + lam ^ 2 * (u ⬝ᵥ u) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [dotProduct_comm u θ]
      ring
    rw [hexpand] at hnorm
    have hscaled := mul_le_mul_of_nonneg_left hquad hlam.le
    have hbound : lam * (θ ⬝ᵥ u) ≤ θ ⬝ᵥ θ := by nlinarith
    have hscaled2 := mul_le_mul_of_nonneg_left hbound hlam.le
    change lam ^ 2 * (θ ⬝ᵥ u) ≤ lam * (θ ⬝ᵥ θ)
    nlinarith
  have hsqrt : Real.sqrt (lam ^ 2 * (θ ⬝ᵥ K⁻¹ *ᵥ θ)) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) := by
    calc
      _ ≤ Real.sqrt (lam * (θ ⬝ᵥ θ)) := Real.sqrt_le_sqrt hbias
      _ = _ := Real.sqrt_mul hlam.le _
  have htriangle := quadratic_triangle hK.posSemidef (K⁻¹ *ᵥ S)
    (-(lam • (K⁻¹ *ᵥ θ)))
  rw [hfirst, hsecond] at htriangle
  change Real.sqrt ((K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ)) ⬝ᵥ
    K *ᵥ (K⁻¹ *ᵥ S - lam • (K⁻¹ *ᵥ θ))) ≤
      Real.sqrt lam * Real.sqrt (θ ⬝ᵥ θ) + Real.sqrt (S ⬝ᵥ K⁻¹ *ᵥ S)
  simp only [← sub_eq_add_neg] at htriangle
  linarith

lemma estimator_error {Ω : Type} {d : Nat} {lam : Real} (hlam : 0 < lam)
    (A : Nat → Ω → Fin d → Real) (η X : Nat → Ω → Real) (θ : Fin d → Real)
    (hX : ∀ t ω, X (t + 1) ω = θ ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    (t : Nat) (ω : Ω) :
    let K := BanditAlgorithm.regularizedDesignMatrix d lam A t ω
    BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θ =
      K⁻¹ *ᵥ BanditAlgorithm.selfNormalizedSum d η A t ω - lam • (K⁻¹ *ᵥ θ) := by
  let G := ∑ s ∈ Finset.range t, vecMulVec (A (s + 1) ω) (A (s + 1) ω)
  let K := BanditAlgorithm.regularizedDesignMatrix d lam A t ω
  have hG : G.PosSemidef := gram_posSemidef (fun s => A (s + 1) ω) t
  have hK : K.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hG
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hcancel : K⁻¹ *ᵥ (K *ᵥ θ) = θ := by
    rw [mulVec_mulVec, nonsing_inv_mul K hdet, one_mulVec]
  have hsum : (∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω) =
      G *ᵥ θ + BanditAlgorithm.selfNormalizedSum d η A t ω := by
    simp only [G, sum_mulVec, vecMulVec_mulVec, BanditAlgorithm.selfNormalizedSum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hX, add_smul, dotProduct_comm θ (A (s + 1) ω)]
    simp only [op_smul_eq_smul]
  have hGθ : G *ᵥ θ = K *ᵥ θ - lam • θ := by
    simp [K, BanditAlgorithm.regularizedDesignMatrix, G, add_mulVec, smul_mulVec]
  change K⁻¹ *ᵥ (∑ s ∈ Finset.range t, X (s + 1) ω • A (s + 1) ω) - θ = _
  rw [hsum, hGθ, mulVec_add, mulVec_sub, mulVec_smul, hcancel]
  abel

end EllipsoidProof



open MeasureTheory ProbabilityTheory Matrix

set_option autoImplicit false

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : Nat} (ℱ : Filtration Nat mΩ)
    (A : Nat → Ω → Fin d → Real) (η : Nat → Ω → Real)
    (X : Nat → Ω → Real) (θs : Fin d → Real)
    (hA : ∀ t : Nat, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : Nat, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : Nat, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    (hX : ∀ t ω, X (t + 1) ω = θs ⬝ᵥ A (t + 1) ω + η (t + 1) ω)
    {lam : Real} (hlam : 0 < lam) {δ : Real} (hδ : δ ∈ Set.Ioo (0 : Real) 1) :
    1 - δ ≤ P.real {ω | ∀ t : Nat,
      Real.sqrt
          ((BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
            BanditAlgorithm.regularizedDesignMatrix d lam A t ω *ᵥ
              (BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs))
        < Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs)
            + Real.sqrt
                (2 * Real.log (1 / δ)
                  + Real.log
                      ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d))} := by
  let bad : Set Ω := {ω | ∃ t : Nat,
    2 * Real.log (1 / δ) +
      Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d) ≤
      BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
          BanditAlgorithm.selfNormalizedSum d η A t ω}
  let good : Set Ω := {ω | ∀ t : Nat,
      Real.sqrt
          ((BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
            BanditAlgorithm.regularizedDesignMatrix d lam A t ω *ᵥ
              (BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs))
        < Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs)
            + Real.sqrt
                (2 * Real.log (1 / δ)
                  + Real.log
                      ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d))}
  have hbad : P.real bad ≤ δ :=
    BanditAlgorithm.self_normalized_martingale_bound ℱ A η hA hη hsg hlam hδ
  have hcover : Set.univ ⊆ bad ∪ good := by
    intro ω _
    by_cases hω : ω ∈ bad
    · exact Or.inl hω
    right
    intro t
    let G := ∑ s ∈ Finset.range t, vecMulVec (A (s + 1) ω) (A (s + 1) ω)
    let K := BanditAlgorithm.regularizedDesignMatrix d lam A t ω
    let S := BanditAlgorithm.selfNormalizedSum d η A t ω
    have hG : G.PosSemidef := EllipsoidProof.gram_posSemidef (fun s => A (s + 1) ω) t
    have hK : K.PosDef := (Matrix.PosDef.one.smul hlam).add_posSemidef hG
    have hnonneg : 0 ≤ S ⬝ᵥ K⁻¹ *ᵥ S := by
      simpa using hK.inv.posSemidef.dotProduct_mulVec_nonneg S
    have hsmall : S ⬝ᵥ K⁻¹ *ᵥ S <
        2 * Real.log (1 / δ) + Real.log (K.det / lam ^ d) := by
      exact lt_of_not_ge fun ht => hω ⟨t, ht⟩
    have hbound := EllipsoidProof.ridge_bound hlam G hG S θs
    have herr := EllipsoidProof.estimator_error hlam A η X θs hX t ω
    change Real.sqrt
      ((BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs) ⬝ᵥ
        K *ᵥ (BanditAlgorithm.regularizedLeastSquares d lam A X t ω - θs)) < _
    rw [herr]
    apply hbound.trans_lt
    change Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs) + Real.sqrt (S ⬝ᵥ K⁻¹ *ᵥ S) <
      Real.sqrt lam * Real.sqrt (θs ⬝ᵥ θs) +
        Real.sqrt (2 * Real.log (1 / δ) + Real.log (K.det / lam ^ d))
    linarith [Real.sqrt_lt_sqrt hnonneg hsmall]
  have hmass : (1 : Real) ≤ P.real bad + P.real good := by
    calc
      1 = P.real Set.univ := by simp
      _ ≤ P.real (bad ∪ good) := measureReal_mono hcover
      _ ≤ _ := measureReal_union_le bad good
  change 1 - δ ≤ P.real good
  linarith

#print axioms solution
