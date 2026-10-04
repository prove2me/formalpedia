-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.commForm_testState_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:21:45.979609+00:00
-- url     : https://prove2.me/submissions/7628cfd6-ad55-4e02-a6d1-986cdd1718b4

import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem p2m_2bebcbb7_testState_apply (i₀ i : Fin d) (hne : i ≠ i₀) (β : Occ d)
    (hβ : β i ≠ 0) :
    (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) : Occ d → ℂ) β = 0 := by
  have h1 : β ≠ 0 := fun h => hβ (by simp [h])
  have h2 : β ≠ modeShift i₀ 0 := fun h => hβ (by
    rw [h]; simp [modeShift, Function.update_of_ne hne])
  show ((lp.single 2 (0 : Occ d) (1 : ℂ) + lp.single 2 (modeShift i₀ (0 : Occ d)) (1 : ℂ)
      : L2I (Occ d)) : Occ d → ℂ) β = 0
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply_ne _ _ _ h1, lp.single_apply_ne _ _ _ h2,
    add_zero]

theorem p2m_2bebcbb7_shiftH_apply (hκ : ∀ i, 0 ≤ κ i) {i i₀ : Fin d} (hne : i ≠ i₀)
    (β : Occ d) (hβ : β i = 0) :
    ((ShiftData.shiftH (modeData hκ i) (testState κ i₀) : L2I (Occ d)) : Occ d → ℂ) β = 0 := by
  change ShiftData.hFun (modeData hκ i)
    (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) : Occ d → ℂ) β = 0
  have hs : (((testState κ i₀ : maxDom (fockSym κ)) : L2I (Occ d)) : Occ d → ℂ)
      ((modeData hκ i).shift β) = 0 := by
    apply p2m_2bebcbb7_testState_apply i₀ i hne
    show modeShift i β i ≠ 0
    simp
  have hn : ¬ ∃ α, (modeData hκ i).shift α = β := by
    rintro ⟨α, hα⟩
    have h := congrFun hα i
    change modeShift i α i = β i at h
    simp at h
    omega
  simp only [ShiftData.hFun, ShiftData.hop_eq_zero _ _ hn, hs, mul_zero, sub_zero]

open BookProof.NavierStokesFlow.HermiteFarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData BookProof.NavierStokesFlow.FockManyMode LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian in
theorem solution {d : ℕ} {κ : Fin d → ℝ} (hκ : ∀ i, 0 ≤ κ i) {i i₀ : Fin d} (hne : i ≠ i₀) :
    commForm (ShiftData.shiftH (modeData hκ i)) (diagMax (fockSym κ)) (testState κ i₀) = 0 := by
  have key : ∀ β : Occ d,
      ((ShiftData.shiftH (modeData hκ i) (testState κ i₀) : L2I (Occ d)) : Occ d → ℂ) β = 0 ∨
      ((diagMax (fockSym κ) (testState κ i₀) : L2I (Occ d)) : Occ d → ℂ) β = 0 := by
    intro β
    by_cases hβ : β i = 0
    · exact Or.inl (p2m_2bebcbb7_shiftH_apply hκ hne β hβ)
    · right
      rw [diagMax_coe, p2m_2bebcbb7_testState_apply i₀ i hne β hβ, mul_zero]
  have h1 : (inner ℂ (ShiftData.shiftH (modeData hκ i) (testState κ i₀))
      (diagMax (fockSym κ) (testState κ i₀)) : ℂ) = 0 := by
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun β => ?_).trans tsum_zero
    rcases key β with h | h
    · rw [h, inner_zero_left]
    · rw [h, inner_zero_right]
  have h2 : (inner ℂ (diagMax (fockSym κ) (testState κ i₀))
      (ShiftData.shiftH (modeData hκ i) (testState κ i₀)) : ℂ) = 0 := by
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun β => ?_).trans tsum_zero
    rcases key β with h | h
    · rw [h, inner_zero_right]
    · rw [h, inner_zero_left]
  have hz : ∀ a b : ℂ, a = 0 → b = 0 → (Complex.I * (a - b)).re = 0 := by
    intro a b ha hb
    rw [ha, hb, sub_self, mul_zero, Complex.zero_re]
  exact hz _ _ h1 h2
