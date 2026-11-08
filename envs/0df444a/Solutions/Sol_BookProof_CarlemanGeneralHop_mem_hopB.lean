-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.mem_hopB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T22:57:15.411799+00:00
-- url     : https://prove2.me/submissions/3df604d2-97d7-49c1-8c53-4045b2ebb630

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.mem_hopB
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_le
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {A : Finset (Fin d →₀ ℕ)} {p m b : Fin d →₀ ℕ} :
    b ∈ hopB A p m ↔ (∀ k, m k ≤ b k) ∧ hshift p m b ∈ A := by

  classical
  constructor
  · intro hb
    rw [hopB, Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rw [Finset.mem_filter] at ha
    refine ⟨fun k => hshift_le ha.2 k, ?_⟩
    rw [hshift_hshift ha.2]
    exact ha.1
  · rintro ⟨hm, hA⟩
    rw [hopB, Finset.mem_image]
    refine ⟨hshift p m b, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hA, fun k => hshift_le hm k⟩
    · rw [hshift_hshift hm]
