-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.filter_PT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:59.936265+00:00
-- url     : https://prove2.me/submissions/94acf26b-1ea5-4fed-b24e-c4dfcbfa3084

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
theorem _root_.solution (Sg : ℕ → ℕ → Finset E) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) :
    (PT Sg i).filter (fun p => ls p = s) =
      ((PT Sg (i - s)) ×ˢ (Sg i s)).image (fun x => Formalism.FourierDecayAlt.TA.ext x.1 s x.2) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  ext p
  simp only [mem_filter, mem_PT_succ, mem_image, mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨m, hm, h, hh, t, ht, rfl⟩, hls⟩
    rw [ls_ext] at hls
    subst hls
    have e : n + 1 - (n + 1 - m) = m := by omega
    exact ⟨h, t, ⟨by rwa [e], ht⟩, rfl⟩
  · rintro ⟨h, t, ⟨hh, ht⟩, rfl⟩
    have e : n + 1 - (n + 1 - s) = s := by omega
    exact ⟨⟨n + 1 - s, by omega, h, hh, t, by rwa [e], by rw [e]⟩, ls_ext _ _ _⟩
end Formalism.FourierDecayAlt.P.TA1
