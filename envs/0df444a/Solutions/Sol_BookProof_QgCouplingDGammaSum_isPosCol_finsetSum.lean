-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.isPosCol_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:26.668019+00:00
-- url     : https://prove2.me/submissions/de126151-9998-45db-a055-fac1a790fe92

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.isPosCol_finsetSum
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)}
    (h : ∀ i ∈ s, IsPosCol (cols i)) : IsPosCol (fun k => ∑ i ∈ s, cols i k) := by

  intro S c
  have hterm : ∀ j ∈ S, ∀ k ∈ S,
      (starRingEnd ℂ) (c j) * ((fun k => ∑ i ∈ s, cols i k) k) j * c k
        = ∑ i ∈ s, (starRingEnd ℂ) (c j) * (cols i k) j * c k := by
    intro j _ k _
    simp only [Finsupp.finset_sum_apply]
    rw [Finset.mul_sum, Finset.sum_mul]
  have hexp : (∑ j ∈ S, ∑ k ∈ S,
        (starRingEnd ℂ) (c j) * ((fun k => ∑ i ∈ s, cols i k) k) j * c k)
      = ∑ i ∈ s, ∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (cols i k) j * c k :=
    calc (∑ j ∈ S, ∑ k ∈ S,
            (starRingEnd ℂ) (c j) * ((fun k => ∑ i ∈ s, cols i k) k) j * c k)
        = ∑ j ∈ S, ∑ k ∈ S, ∑ i ∈ s, (starRingEnd ℂ) (c j) * (cols i k) j * c k :=
          Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hterm j hj k hk
      _ = ∑ j ∈ S, ∑ i ∈ s, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (cols i k) j * c k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i ∈ s, ∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (cols i k) j * c k :=
          Finset.sum_comm
  rw [hexp, Complex.re_sum]
  exact Finset.sum_nonneg fun i hi => h i hi S c
