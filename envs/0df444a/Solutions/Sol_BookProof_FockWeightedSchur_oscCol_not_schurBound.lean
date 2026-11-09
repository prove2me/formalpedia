-- Prove2me | solution 1 for BookProof.FockWeightedSchur.oscCol_not_schurBound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T11:42:33.907667+00:00
-- url     : https://prove2.me/submissions/29d5c06f-6446-4c17-a199-ab871bc9b60f

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.oscCol_not_schurBound
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscCol_entries_unbounded
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (K : ℝ) : ¬ SchurBound oscCol K := by

  classical
  intro hK
  obtain ⟨k, hk⟩ := oscCol_entries_unbounded (K + 1)
  have hmem : k + 1 ∈ (oscCol k).support := by
    refine Finsupp.mem_support_iff.mpr fun hc => ?_
    rw [show ‖(oscCol k) (k+1)‖ = 0 from by rw [hc]; simp] at hk
    have h0 : (0:ℝ) ≤ K := by
      have := hK k
      have hnn : (0:ℝ) ≤ ∑ j ∈ (oscCol k).support, ‖(oscCol k) j‖ :=
        Finset.sum_nonneg fun j _ => norm_nonneg _
      linarith
    linarith
  have hsingle : ‖(oscCol k) (k + 1)‖ ≤ ∑ j ∈ (oscCol k).support, ‖(oscCol k) j‖ :=
    Finset.single_le_sum (f := fun j => ‖(oscCol k) j‖) (fun j _ => norm_nonneg _) hmem
  have := hK k
  linarith
