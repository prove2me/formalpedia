-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_prod_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:54.354632+00:00
-- url     : https://prove2.me/submissions/4c6d201d-f4f7-47d3-a13c-81ca21668397

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by
  symm
  refine Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_
  · intro j _; have := j.2; simp only [mem_Ioc]; omega
  · intro i _ j _ h; ext; omega
  · intro c hc
    simp only [mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩
  · intro j _; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
