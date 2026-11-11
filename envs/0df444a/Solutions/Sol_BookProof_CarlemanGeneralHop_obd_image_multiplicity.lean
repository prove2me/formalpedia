-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.obd_image_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T23:00:16.919646+00:00
-- url     : https://prove2.me/submissions/ff31d643-63d1-4ba2-9d72-695691c85c47

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.obd_image_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_hshift
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_obd
import Theorems.Thm_BookProof_CarlemanGeneralHop_obd_multiplicity
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
theorem solution (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (y : Fin d →₀ ℕ)
    (M : ℕ) :
    (((Finset.range M).filter
      (fun N => y ∈ (obd d N p m).image (hshift p m))).card) ≤ 2 := by

  classical
  refine le_trans (Finset.card_le_card ?_) (obd_multiplicity p m hp (hshift m p y) M)
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_image] at hN ⊢
  obtain ⟨hNr, a, ha, hay⟩ := hN
  have hao := ha
  rw [mem_obd] at hao
  have hya : hshift m p y = a := by rw [← hay, hshift_hshift hao.2.1]
  exact ⟨hNr, by rw [hya]; exact ha⟩
