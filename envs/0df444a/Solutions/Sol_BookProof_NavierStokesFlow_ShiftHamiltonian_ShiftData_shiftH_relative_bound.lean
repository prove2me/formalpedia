-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.shiftH_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:56:56.067683+00:00
-- url     : https://prove2.me/submissions/d54c2e0f-c924-45ad-9fa8-95f12619ea70

import Mathlib
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData BookProof.NavierStokesFlow.IkebeKato in
theorem solution {ι : Type*} (S : ShiftData ι) (x : maxDom S.sym) :
    ‖(shiftH S x : L2I ι)‖ ^ 2
      ≤ (1 / 2) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2 + (8 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by
  set X : ι → ℂ := ((x : L2I ι) : ι → ℂ) with hX
  set a : ι → ℝ := fun β => (S.ampSeq X β) ^ 2 with ha
  have hS : Summable a := summable_ampSeq_sq S x
  have ha0 : ∀ β, 0 ≤ a β := fun β => sq_nonneg _
  have hB := hasSum_ampBound S x
  have hle : ∑' β, a β ≤ (1 / 8) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2
      + (2 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 :=
    hasSum_le (fun β => ampSeq_sq_le S x β) hS.hasSum hB
  have hhop : HasSum (S.hop a) (∑' β, a β) := (hasSum_hop_iff S).mpr hS.hasSum
  have hcomp : Summable (fun β => a (S.shift β)) := summable_comp_shift S hS
  have hcle : ∑' β, a (S.shift β) ≤ ∑' β, a β :=
    tsum_comp_le_tsum_of_inj hS ha0 S.shift_injective
  have hH := BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData.hasSum_normSq (shiftH S x)
  have hcoe : ((shiftH S x : L2I ι) : ι → ℂ) = S.hFun X := rfl
  rw [hcoe] at hH
  have hR : HasSum (fun β => 2 * S.hop a β + 2 * a (S.shift β))
      (2 * ∑' β, a β + 2 * ∑' β, a (S.shift β)) :=
    (hhop.mul_left 2).add (hcomp.hasSum.mul_left 2)
  have hpt : ∀ β, ‖S.hFun X β‖ ^ 2 ≤ 2 * S.hop a β + 2 * a (S.shift β) := by
    intro β
    have h1 := norm_hFun_le S X β
    have h2 : 0 ≤ S.hop (S.ampSeq X) β := hop_nonneg S (ampSeq_nonneg S _) β
    have h4 := mul_self_le_mul_self (norm_nonneg (S.hFun X β)) h1
    have h5 : S.hop a β = (S.hop (S.ampSeq X) β) ^ 2 := hop_sq S (S.ampSeq X) β
    rw [h5]
    simp only [ha]
    nlinarith [h4, sq_nonneg (S.hop (S.ampSeq X) β - S.ampSeq X (S.shift β))]
  have hmain := hasSum_le hpt hH hR
  nlinarith [hmain, hle, hcle]
