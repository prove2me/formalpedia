-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.obd_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T22:59:43.866315+00:00
-- url     : https://prove2.me/submissions/155bb3b5-8f24-4c5b-a669-78abd4d35fb8

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.obd_multiplicity
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_mem_obd
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
theorem solution (p m : Fin d →₀ ℕ) (hp : ∀ k, p k ≤ 2) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ obd d N p m)).card) ≤ 2 := by

  classical
  set S := Finset.univ.sup (fun k : Fin d => a k) with hS
  set T := Finset.univ.sup (fun k : Fin d => a k + p k) with hT
  have hTS : T ≤ S + 2 := by
    refine Finset.sup_le fun k _ => ?_
    have h1 : a k ≤ S := Finset.le_sup (f := fun k : Fin d => a k) (Finset.mem_univ k)
    have := hp k
    omega
  have hsub : ((Finset.range M).filter (fun N => a ∈ obd d N p m)) ⊆ Finset.Ico S T := by
    intro N hN
    simp only [Finset.mem_filter] at hN
    rw [mem_obd] at hN
    obtain ⟨hle, -, k, hk⟩ := hN.2
    refine Finset.mem_Ico.mpr ⟨Finset.sup_le fun j _ => hle j, ?_⟩
    exact lt_of_lt_of_le hk
      (Finset.le_sup (f := fun k : Fin d => a k + p k) (Finset.mem_univ k))
  calc (((Finset.range M).filter (fun N => a ∈ obd d N p m)).card)
      ≤ (Finset.Ico S T).card := Finset.card_le_card hsub
    _ = T - S := Nat.card_Ico _ _
    _ ≤ 2 := by omega
