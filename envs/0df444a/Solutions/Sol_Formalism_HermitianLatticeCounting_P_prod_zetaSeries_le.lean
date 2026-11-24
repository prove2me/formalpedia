-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_zetaSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:22.713437+00:00
-- url     : https://prove2.me/submissions/3fc04307-0ece-4a45-b4c0-dbf54e0d17f3

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_zetaSeries_sub_one_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_zetaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (S : Finset ℕ) (hS : ∀ j ∈ S, 3 ≤ j) : ∏ j ∈ S, zetaR j ≤ Real.exp 0.356 := by
  have hpos : ∀ j ∈ S, 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by have := hS j hj; omega))
  obtain ⟨M, hM⟩ : ∃ M, S ⊆ Finset.Icc 3 M :=
    ⟨S.sup id, fun j hj => Finset.mem_Icc.mpr ⟨hS j hj, Finset.le_sup (f := id) hj⟩⟩
  have hsub : ∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) ≤ ∑ j ∈ Finset.Icc 3 M, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hM (fun i hi _ => by
      have : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
      linarith [one_le_zetaSeries i this])
  calc ∏ j ∈ S, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j = Real.exp (∑ j ∈ S, Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j)) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl (fun j hj => (Real.exp_log (hpos j hj)).symm)
    _ ≤ Real.exp (∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) :=
        Real.exp_le_exp.mpr (Finset.sum_le_sum (fun j hj => Real.log_le_sub_one_of_pos (hpos j hj)))
    _ ≤ Real.exp 0.356 := Real.exp_le_exp.mpr (hsub.trans (sum_zetaSeries_sub_one_le M))
end Formalism.HermitianLatticeCounting.P
