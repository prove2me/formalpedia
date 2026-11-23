-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.coset_eq_of_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:12.414105+00:00
-- url     : https://prove2.me/submissions/ffb85507-b35a-4646-a9fb-97b18c4b6ca8

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_piece_sub_mul_cong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {J' : Subgroup (GL (Fin a) F)} (hJ : J' ≤ GLint O a)
    (u v : J')
    (h : ((v : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ ((u : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)) :
    (u : J' ⧸ (congSub O ϖ a).subgroupOf J') = (v : J' ⧸ (congSub O ϖ a).subgroupOf J') := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  obtain ⟨k, hk, hkv⟩ := piece_sub_mul_cong O ϖ hϖ hϖ0 hloc (hJ u.2) h
  have h1 : (u : GL (Fin a) F) * k = v := Units.ext hkv
  have hk' : k = (u : GL (Fin a) F)⁻¹ * v := by rw [← h1, inv_mul_cancel_left]
  rw [hk'] at hk
  simpa using hk
end Formalism.DoubleCosetMeasures.P.Vol
