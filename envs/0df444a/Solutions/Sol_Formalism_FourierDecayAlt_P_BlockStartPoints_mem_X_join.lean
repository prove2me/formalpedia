-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.mem_X_join
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:14.822238+00:00
-- url     : https://prove2.me/submissions/04bdfcdb-1f9f-495e-91a0-4fd15a6f0543

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_level_join
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_blockStart_join
import Theorems.Thm_Formalism_FourierDecayAlt_P_BlockStartPoints_blockStart_length

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution (T : Tower E) (h : Pt E) (s : ℕ) (t : E) (i : ℕ) :
    join h s t ∈ T.X i ↔
      level h + s = i ∧ h ∈ T.X (level h) ∧ 1 ≤ s ∧ t ∈ T.Sg (level h + 1) s := by
  rw [T.isTower, T.isTower, level_join]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ⟨rfl, fun k hk => ?_⟩, ?_⟩
    · have hk' : k < (join h s t).length := by simp [join]; omega
      have h3 := h2 k hk'
      rw [blockStart_join _ _ _ _ hk.le] at h3
      have e : (join h s t)[k]'hk' = h[k]'hk := by simp [join, List.getElem_append_left hk]
      rwa [e] at h3
    · have hk' : h.length < (join h s t).length := by simp [join]
      have h3 := h2 h.length hk'
      rw [blockStart_join _ _ _ _ le_rfl, blockStart_length] at h3
      have e : (join h s t)[h.length]'hk' = (s, t) := by simp [join]
      rwa [e] at h3
  · rintro ⟨h1, ⟨_, h2⟩, h3, h4⟩
    refine ⟨h1, fun k hk => ?_⟩
    have hk' : k < h.length + 1 := by simpa [join] using hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | heq
    · rw [blockStart_join _ _ _ _ hlt.le]
      have e : (join h s t)[k]'hk = h[k]'hlt := by simp [join, List.getElem_append_left hlt]
      rw [e]
      exact h2 k hlt
    · subst heq
      rw [blockStart_join _ _ _ _ le_rfl, blockStart_length]
      have e : (join h s t)[h.length]'hk = (s, t) := by simp [join]
      rw [e]
      exact ⟨h3, h4⟩
end Formalism.FourierDecayAlt.P.BlockStartPoints
