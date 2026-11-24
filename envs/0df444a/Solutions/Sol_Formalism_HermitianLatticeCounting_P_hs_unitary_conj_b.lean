-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hs_unitary_conj_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:45.799796+00:00
-- url     : https://prove2.me/submissions/1dcc80ba-3efb-41f0-8487-c0ceddecfa55

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_sq_trace_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℂ) (hk : kᴴ * k = 1) :
    hs (k * X * kᴴ) = hs X := by
  unfold hs
  congr 1
  have : ((∑ a, ∑ b, ‖(k * X * kᴴ) a b‖ ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs_sq_trace_b, hs_sq_trace_b]
    have e : (k * X * kᴴ)ᴴ * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
    rw [e, trace_mul_cycle, hk, Matrix.one_mul]
  exact_mod_cast this
end Formalism.HermitianLatticeCounting.P
