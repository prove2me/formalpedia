-- Prove2me | solution 1 for Eden.norm_exteriorOperator_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:32.764675+00:00
-- url     : https://prove2.me/submissions/0e585f38-2185-4d02-aa57-b5150de09eda

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
import Theorems.Thm_Eden_isGreatest_exteriorFactor
import Theorems.Thm_Eden_norm_exteriorEvolution_initialBasis
import Theorems.Thm_Eden_norm_exteriorEvolution_le
import Theorems.Thm_Eden_exteriorFactor_pos
import Theorems.Thm_Eden_norm_initialExteriorBasisVector


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (p : PhaseSpace) :
    ‖exteriorOperator k (fderiv ℝ (evolution c t) p).toLinearMap‖ =
      singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
  obtain ⟨⟨s, hs⟩, hmax⟩ := isGreatest_exteriorFactor hk c ht p
  have hM : 0 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k := by
    rw [← hs]
    exact (exteriorFactor_pos k c ht p s).le
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ hM
    exact norm_exteriorEvolution_le hk c ht p
  · have h := (exteriorOperator k (fderiv ℝ (evolution c t) p).toLinearMap).le_opNorm
      (initialExteriorBasisVector k p s)
    change ‖exteriorEvolution k c t p (initialExteriorBasisVector k p s)‖ ≤ _ at h
    rwa [norm_exteriorEvolution_initialBasis k c ht p s, norm_initialExteriorBasisVector,
      mul_one, hs] at h
end Eden
