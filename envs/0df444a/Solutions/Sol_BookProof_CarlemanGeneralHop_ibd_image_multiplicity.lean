-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.ibd_image_multiplicity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:00:40.817678+00:00
-- url     : https://prove2.me/submissions/2d61bf5b-83d2-48a2-befb-cdc4ce1bdd17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.ibd_image_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_ibd
import Theorems.Thm_BookProof_CarlemanGeneralHop_ibd_multiplicity
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
theorem solution (p m : Fin d →₀ ℕ) (y : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => y ∈ (ibd d N m).image (hshift p m))).card) ≤ 1 := by

  classical
  refine le_trans (Finset.card_le_card ?_) (ibd_multiplicity m (hshift m p y) M)
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_image] at hN ⊢
  obtain ⟨hNr, b, hb, hby⟩ := hN
  have hbi := hb
  rw [mem_ibd] at hbi
  have hyb : hshift m p y = b := by rw [← hby, hshift_hshift hbi.2.1]
  exact ⟨hNr, by rw [hyb]; exact hb⟩
