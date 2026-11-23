-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.eLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:47.342807+00:00
-- url     : https://prove2.me/submissions/4afdee29-2e47-4729-b3b5-14870738a2b7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_ee_semb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
open NumberField.mixedEmbedding MeasureTheory
open scoped Classical
noncomputable section
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
attribute [local instance] Formalism.FourierDecayAlt.P.Jx2.isEmptyReal
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution (L : Submodule ℤ E) (c : ℝ) :
    eLat E L c = ZLattice.comap ℝ (S6.frameLat E L c) (ee E).toLinearMap := by
  ext v
  simp only [eLat, S6.frameLat, ZLattice.comap, Submodule.mem_map, Submodule.mem_comap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨mixedEmbedding E t, ⟨t, ht, rfl⟩, (ee_semb E c t).symm⟩
  · rintro ⟨u, ⟨t, ht, rfl⟩, h⟩
    refine ⟨t, ht, (ee E).injective ?_⟩
    exact (ee_semb E c t).trans h
end Formalism.FourierDecayAlt.P.Jx2
