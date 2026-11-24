-- Prove2me | solution 1 for Formalism.CountingSumsFrames.phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:12.74377+00:00
-- url     : https://prove2.me/submissions/0a2362e6-de6c-4875-a700-61d741fc3602

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_GM_FockB_ops_mono
import Theorems.Thm_Formalism_GM_FockB_tiePhi_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p LL j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (FockB.tiePhi_mem (zv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r)))
    (sv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r))) _ _ _)
  intro v hv
  simp only [FockB.V, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  simp only [Set.mem_ofPred_eq]
  rcases hv with (⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl
  · left; rfl
  · right; rfl
  · left; rfl
  · left; rfl
end Formalism.CountingSumsFrames
