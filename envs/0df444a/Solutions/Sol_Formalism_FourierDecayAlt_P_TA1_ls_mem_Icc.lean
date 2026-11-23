-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.ls_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:21.804914+00:00
-- url     : https://prove2.me/submissions/2f84609a-9ca3-40fa-9236-cd22fa786f17

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_ls_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_mem_PT_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution (Sg : ℕ → ℕ → Finset E) (i : ℕ) (hi : 1 ≤ i) (p : Pt E) (hp : p ∈ PT Sg i) :
    ls p ∈ Icc 1 i := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, hm, h, _, t, _, rfl⟩ := (mem_PT_succ Sg n p).1 hp
  rw [ls_ext, mem_Icc]; omega
end Formalism.FourierDecayAlt.P.TA1
