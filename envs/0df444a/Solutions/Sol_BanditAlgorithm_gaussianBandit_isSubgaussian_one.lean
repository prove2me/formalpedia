-- Prove2me | solution 1 for BanditAlgorithm.gaussianBandit_isSubgaussian_one
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T23:04:14.002802+00:00
-- url     : https://prove2.me/submissions/42002b26-0a06-400a-9d14-9facc1d95a98

import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Fernique

open MeasureTheory ProbabilityTheory NNReal

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ} (μvec : Fin k → ℝ) :
    IsSubgaussianBandit 1 (gaussianBandit μvec) := by
  constructor
  · intro i
    change Integrable id (gaussianReal (μvec i) 1)
    apply memLp_one_iff_integrable.mp
    simpa using
      (memLp_id_gaussianReal'
        (μ := μvec i) (v := (1 : NNReal)) (1 : ENNReal) (by simp))
  · intro i
    have hmean :
        banditArmMean (gaussianBandit μvec) i = μvec i := by
      simp [banditArmMean, gaussianBandit]
    rw [hmean]
    have hcenter :
        HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
      constructor
      · exact fun t ↦ integrable_exp_mul_gaussianReal t
      · intro t
        rw [mgf_id_gaussianReal]
        norm_num
    have hmap :
        (gaussianReal (μvec i) 1).map (fun x ↦ x - μvec i) =
          gaussianReal 0 1 := by
      simpa using
        (gaussianReal_map_sub_const (μ := μvec i) (v := (1 : NNReal)) (μvec i))
    have hmeas :
        AEMeasurable (fun x : ℝ ↦ x - μvec i)
          (gaussianReal (μvec i) 1) := by fun_prop
    have hleft :
        HasSubgaussianMGF id 1
          ((gaussianReal (μvec i) 1).map (fun x ↦ x - μvec i)) := by
      rwa [hmap]
    have hright :=
      (HasSubgaussianMGF.id_map_iff (c := (1 : NNReal)) hmeas).mp hleft
    simpa [gaussianBandit] using hright

end BanditAlgorithm
