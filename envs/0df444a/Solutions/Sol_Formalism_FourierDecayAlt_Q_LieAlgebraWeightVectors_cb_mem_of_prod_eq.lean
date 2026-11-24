-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_mem_of_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:14.760929+00:00
-- url     : https://prove2.me/submissions/787fdc62-e5e5-447e-a7e6-133d18c7f42d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {n : ℕ} {a b : ℕ → ℝ}
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j := by
  intro i hi
  have h0 := h (-(a i : ℂ))
  have hl : ∏ l ∈ Icc 1 n, (-(a i : ℂ) + (a l : ℂ)) = 0 := Finset.prod_eq_zero hi (by ring)
  rw [hl] at h0
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp h0.symm
  refine ⟨j, hj, ?_⟩
  have e : ((b j : ℝ) : ℂ) = (a i : ℂ) := by linear_combination hz
  exact_mod_cast e.symm
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
