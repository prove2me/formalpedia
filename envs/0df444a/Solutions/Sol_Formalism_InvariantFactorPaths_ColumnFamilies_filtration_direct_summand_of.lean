-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_direct_summand_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:12:11.923223+00:00
-- url     : https://prove2.me/submissions/dc5b1e25-d826-4a72-9acc-4f9e2cf34e94

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationDirectSummand
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_Mpi_eq_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → FiltrationDirectSummand := by
  intro hA n _ M CF pi hpi
  refine ⟨Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}ᶜ), ?_⟩
  rw [qb_Mpi_eq_image hA CF pi hpi]
  constructor
  · exact (qb_basis hA CF ℤ).linearIndependent.disjoint_span_image disjoint_compl_right
  · rw [codisjoint_iff, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self, Set.image_univ]
    exact (qb_basis hA CF ℤ).span_eq
end Formalism.InvariantFactorPaths.ColumnFamilies
