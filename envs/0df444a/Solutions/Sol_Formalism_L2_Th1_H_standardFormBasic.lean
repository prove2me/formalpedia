-- Prove2me | solution 1 for Formalism.L2.Th1.H.standardFormBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:42.170066+00:00
-- url     : https://prove2.me/submissions/e349499f-a1b0-457a-a49a-480e769ab7b4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_stdH_apply
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : StdHBasic := by
  intro L n _ _
  have harea := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos L
  refine ⟨stdH_apply L n, fun x y => ?_, fun x hx => ?_⟩
  · rw [stdH_apply, stdH_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have hi : ∀ i, Formalism.L2.Th1.F.herm L (x i) (x i) =
        ((Complex.normSq (x i) / Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
      intro i
      simp only [Formalism.L2.Th1.F.herm, Complex.mul_conj]
      push_cast
      ring
    rw [stdH_apply, Complex.re_sum]
    simp only [hi, Complex.ofReal_re]
    obtain ⟨i, hi0⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun j _ => div_nonneg (Complex.normSq_nonneg _) harea.le)
      ⟨i, Finset.mem_univ _, div_pos (Complex.normSq_pos.mpr hi0) harea⟩
end Formalism.L2.Th1.H
