-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_fixed_direction_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T14:46:56.47958+00:00
-- url     : https://prove2.me/submissions/e9d7d334-6d28-446e-ac3e-ab5633b62021

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Definitions.Def_SelfNormalizedProcess

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

theorem solution
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
