-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.filtered_iterate_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:35.692507+00:00
-- url     : https://prove2.me/submissions/6e0c0180-e969-40dc-bcb6-65b8a9272e4f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_fin_succ_cons
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_foldr_ofFn_cons
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_foldr_mem_filtration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Nw : W → R) (Fil : ℕ → Set W) (c : ℕ → R) (hc : ∀ j, 0 ≤ c j)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2))
    (hN : ∀ j w, w ∈ Fil j → ∑ i, Nw (Eop i w) ≤ c j * Nw w) (q j : ℕ) (w : W) (hw : w ∈ Fil j) :
    ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_fin_succ_cons]
    calc ∑ τ : Fin q → ι, ∑ i, Nw ((List.ofFn (Fin.cons i τ : Fin (q + 1) → ι)).foldr Eop w)
        = ∑ τ : Fin q → ι, ∑ i, Nw (Eop i ((List.ofFn τ).foldr Eop w)) := by simp only [foldr_ofFn_cons]
      _ ≤ ∑ τ : Fin q → ι, c (j + 2 * q) * Nw ((List.ofFn τ).foldr Eop w) := by
          refine Finset.sum_le_sum fun τ _ => hN _ _ ?_
          have := foldr_mem_filtration Eop Fil hF j w hw (List.ofFn τ)
          simpa using this
      _ = c (j + 2 * q) * ∑ τ : Fin q → ι, Nw ((List.ofFn τ).foldr Eop w) := (Finset.mul_sum _ _ _).symm
      _ ≤ c (j + 2 * q) * ((∏ i ∈ range q, c (j + 2 * i)) * Nw w) := mul_le_mul_of_nonneg_left ih (hc _)
      _ = (∏ i ∈ range (q + 1), c (j + 2 * i)) * Nw w := by rw [Finset.prod_range_succ]; ring
end Formalism.HermitianLatticeCounting.P
