-- Prove2me | solution 1 for CompanionTheory.Bmu.spanFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:01.37452+00:00
-- url     : https://prove2.me/submissions/8ff155a2-6132-4a7e-a3a5-31ab654ce2c9

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_NormPsiGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CompanionTheory.Bmu
theorem _root_.solution {n : ℕ} (S : Submodule ℝ (Mat n)) : ∃ (d : ℕ) (X : Fin d → Mat n), (∀ j, X j ∈ S) ∧
    ∀ Y ∈ S, ∃ a : Fin d → ℝ, Y = ∑ j, (a j : ℂ) • X j := by
  let b := Module.finBasis ℝ S
  refine ⟨_, fun j => (b j : Mat n), fun j => (b j).2, fun Y hY => ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩⟩
  have h := congrArg (Subtype.val) (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
  simp only [Complex.coe_smul]
  exact h.symm
end CompanionTheory.Bmu
