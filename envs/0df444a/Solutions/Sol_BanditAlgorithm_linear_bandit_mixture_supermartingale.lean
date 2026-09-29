-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_mixture_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T14:58:02.981284+00:00
-- url     : https://prove2.me/submissions/aee9c29b-ea26-4955-8af3-683e30c33304

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_SelfNormalizedProcess
import Theorems.Thm_BanditAlgorithm_linear_bandit_fixed_direction_supermartingale

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

theorem solution
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
