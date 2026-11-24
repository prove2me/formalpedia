-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx4.lev_uw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:07.948217+00:00
-- url     : https://prove2.me/submissions/4e9f4d91-e948-4449-9380-29de83dc830c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lv_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lv_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx4_lift_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_bvec_lv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v
variable {l : Fin r}
local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)
variable {r' : ℕ}
open Formalism.FourierDecayAlt.B2 (a0)
open B2x6 (lv blk)
namespace Formalism.FourierDecayAlt.P.Qx4
theorem _root_.solution {z : Fin (2 * r' + k + 1) → ℂ} {g : Mx k r'} (hg : g ∈ UH (Hpk k r'))
    (h : ιLev k 1 r' g ∈ UWset k (1 + r') (liftVec k 1 r' z)) : g ∈ UWset k r' z := by
  refine ⟨hg, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h2 := (h.2.1 ⟨a.val + 1, by omega⟩).1
    rw [← lv_eI, B2x6.bvec_lv, B2x5.lev_lift] at h2
    exact lift_inj h2
  · have h2 := (h.2.1 ⟨a.val + 1, by omega⟩).2
    rw [← lv_esI, B2x6.bvec_lv, B2x5.lev_lift] at h2
    exact lift_inj h2
  · have h2 := h.2.2
    rw [B2x5.lev_lift] at h2
    exact lift_inj h2
end Formalism.FourierDecayAlt.P.Qx4
