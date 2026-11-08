-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T22:57:16.631973+00:00
-- url     : https://prove2.me/submissions/14fad4ee-e8e0-4aa6-96f4-8c2407936c8d

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG
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
theorem solution {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m a : Fin d →₀ ℕ}
    (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c b)
    (ha : ∀ k, p k ≤ a k) :
    ltG u w c' p m a = (starRingEnd ℂ) (rtG u w c p m (hshift m p a)) := by

  have hb : ∀ k, m k ≤ hshift m p a k := fun k => hshift_le ha k
  have hba : hshift p m (hshift m p a) = a := hshift_hshift ha
  rw [ltG, rtG, hba]
  rw [show c' a = c (hshift m p a) from by
    conv_lhs => rw [← hba]
    exact hcomp _ hb]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring
