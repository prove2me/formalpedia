-- Prove2me | solution 1 for BanditAlgorithm.self_normalized_martingale_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T15:05:46.160705+00:00
-- url     : https://prove2.me/submissions/aca768b6-ad04-4a1b-b695-3997b5aba70d

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_SelfNormalizedProcess
import Theorems.Thm_BanditAlgorithm_linear_bandit_mixture_supermartingale
import Theorems.Thm_BanditAlgorithm_nonnegative_supermartingale_ville
import Theorems.Thm_BanditAlgorithm_isotropic_gaussian_unregularized_quadratic_mixture

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

theorem solution
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
