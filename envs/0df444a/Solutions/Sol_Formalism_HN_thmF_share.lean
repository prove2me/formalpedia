-- Prove2me | solution 1 for Formalism.HN.thmF_share
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:30.024799+00:00
-- url     : https://prove2.me/submissions/e57faa65-db36-4696-ac45-5acd6db779f8

import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameHermSharpB
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TheoremFSharp
import Theorems.Thm_Formalism_HN_frameB_share


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {I : Type} [Fintype I] (m : I → ℕ) (x : ∀ i, Fin (m i) → ℝ) (s u τ : ℝ)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hsum : (∑ i, (m i : ℝ)) * s ≤ ∑ i, ∑ j, x i j)
    (hle : ∀ i j, x i j ≤ s + u) :
    (∑ i, ((univ.filter (fun j => x i j < s - τ)).card : ℝ)) ≤
      (∑ i, (m i : ℝ)) * (u / (u + τ)) := by
  rcases lt_or_eq_of_le hu with hu' | hu'
  · exact frameB_share m x s u τ hu' hτ hsum hle
  · subst hu'
    have hempty : ∀ i, univ.filter (fun j => x i j < s - τ) = ∅ := by
      intro i
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hj' := (Finset.mem_filter.1 hj).2
      have hlt : ∑ i, ∑ j, x i j < ∑ i, ∑ _j : Fin (m i), s := by
        apply Finset.sum_lt_sum
        · intro i' _
          exact Finset.sum_le_sum fun j' _ => by linarith [hle i' j']
        · exact ⟨i, mem_univ _, Finset.sum_lt_sum (fun j' _ => by linarith [hle i j'])
            ⟨j, mem_univ _, by linarith⟩⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      rw [Finset.sum_mul] at hsum
      linarith
    simp [hempty]
end Formalism.HN
