-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_prod_castLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:01.568987+00:00
-- url     : https://prove2.me/submissions/e72d2288-a454-4f86-adea-8ced8197ce76

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : Type*} [CommMonoid M] {s n : ℕ} (hs : s ≤ n) (F : Fin n → M)
    (h : ∀ a : Fin n, s ≤ a.val → F a = 1) : ∏ a' : Fin s, F (Fin.castLE hs a') = ∏ a, F a := by
  have h1 : ∏ a' : Fin s, F (Fin.castLE hs a') = ∏ a ∈ (univ : Finset (Fin s)).map (Fin.castLEEmb hs), F a := by
    rw [Finset.prod_map]; rfl
  rw [h1]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro a _ ha
  apply h
  by_contra hlt
  push Not at hlt
  exact ha (Finset.mem_map.2 ⟨⟨a.val, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
