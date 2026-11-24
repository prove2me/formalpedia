-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.exists_nat_ne_zero_smul_mem_span_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:06.398379+00:00
-- url     : https://prove2.me/submissions/fcd75a24-7fba-46be-bf71-e4f685252ce3

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {K ι : Type} [Field K] [NumberField K] [Fintype ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → K) (x : ι → K)
    (hx : x ∈ Submodule.span K (Set.range e)) :
    ∃ m : ℕ, m ≠ 0 ∧ m • x ∈ Submodule.span (𝓞 K) (Set.range e) := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  have key : y • ∑ a, c a • e a ∈ Submodule.span (𝓞 K) (Set.range e) := by
    rw [Finset.smul_sum]
    apply Submodule.sum_mem
    intro a _
    have hi : IsIntegral ℤ (y • c a) := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    let r : 𝓞 K := ⟨y • c a, hi⟩
    have hr : y • (c a • e a) = r • e a := by
      rw [← algebraMap_smul K r, ← smul_assoc]
      rfl
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [← natCast_zsmul, ← h]; exact key
  · have : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [← natCast_zsmul, this, neg_smul]; exact Submodule.neg_mem _ key
end Formalism.HermiteSiegelSlopes
