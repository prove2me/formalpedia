-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_range_sub_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:15.5998+00:00
-- url     : https://prove2.me/submissions/ebaf40b4-f16f-4670-8597-55564434ef6a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {n : ℕ} {a b : ℕ → ℝ} (hm : ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j) :
    Set.range (fun j : Fin n => -a (j.1 + 1)) ⊆ Set.range (fun j : Fin n => -b (j.1 + 1)) := by
  rintro x ⟨j, rfl⟩
  obtain ⟨l, hl, hab⟩ := hm (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)
  have hl1 := (Finset.mem_Icc.mp hl).1
  have hl2 := (Finset.mem_Icc.mp hl).2
  refine ⟨⟨l - 1, by omega⟩, ?_⟩
  show -b (l - 1 + 1) = -a (j.val + 1)
  rw [hab, Nat.sub_add_cancel hl1]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
