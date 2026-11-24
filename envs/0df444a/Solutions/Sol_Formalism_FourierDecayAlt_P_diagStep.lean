-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.diagStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.890133+00:00
-- url     : https://prove2.me/submissions/e1eb7065-92e7-4c40-96d4-1e9601ed042c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_Nst_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_Nst_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TB.DiagStep := by
  intro E W _ D hG hK hW hA T ε hε i s hs hsi hir w R hR
  obtain ⟨_, hdom, hper, _⟩ := hA i s hs hsi hir
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ h).1 hh).1
  have hnn : ∀ t₀ t : E, 0 ≤ (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re :=
    fun t₀ t => Nst_nonneg D hG hW hε i s w _ (hK.2 i s t₀ _) t
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold Data.Dg
  refine Finset.sum_le_sum fun t ht => ?_
  have ht0 : t ≠ 0 := fun h => T.zero_not_mem _ _ (h ▸ ht)
  obtain ⟨t₀, ht₀, hmem⟩ := hR t ht
  have h1 := Nst_mono D hG hW hε i s w (T.X (i - s)) (hdom t ht0 _ hY) t
  rw [hper t t₀ hmem] at h1
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun t₀ => if t - t₀ ∈ D.La (i - s + 1) s then
      (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re else 0)
    (fun x _ => by
      split_ifs
      · exact hnn x t
      · exact le_refl 0) ht₀
  simpa only [if_pos hmem] using h2
end Formalism.FourierDecayAlt.P
