-- Prove2me | solution 2 for BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:48:31.888783+00:00
-- url     : https://prove2.me/submissions/97681061-c9da-4f3f-8429-1a7ff9a26a5f

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}
open BookProof.QgCouplingDGammaSum

theorem solution(s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) :
    dGammaOp (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGammaOp (cols i) := by
  have hcre_add : ∀ v w : ℕ →₀ ℂ, creVec (v + w) = creVec v + creVec w := by
    intro v w
    show (v + w).sum (fun j c => c • creA j) = v.sum (fun j c => c • creA j) + w.sum (fun j c => c • creA j)
    exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hcre0 : creVec (0 : ℕ →₀ ℂ) = 0 := by simp [creVec]
  have hd_add : ∀ c1 c2 : ℕ → (ℕ →₀ ℂ), dGamma (fun k => c1 k + c2 k) = dGamma c1 + dGamma c2 := by
    intro c1 c2
    apply Finsupp.lhom_ext
    intro β a
    simp [dGamma, hcre_add, Finset.sum_add_distrib]
  have hd0 : dGamma (fun _ => (0 : ℕ →₀ ℂ)) = 0 := by
    apply Finsupp.lhom_ext
    intro β a
    simp [dGamma, hcre0]
  have hsum : dGamma (fun k => ∑ i ∈ s, cols i k) = ∑ i ∈ s, dGamma (cols i) := by
    classical
    refine Finset.induction_on s ?_ ?_
    · simpa using hd0
    · intro i t hi ih
      simp only [Finset.sum_insert hi]
      rw [hd_add, ih]
  unfold dGammaOp
  rw [hsum, map_sum]
  ext x
  simp
