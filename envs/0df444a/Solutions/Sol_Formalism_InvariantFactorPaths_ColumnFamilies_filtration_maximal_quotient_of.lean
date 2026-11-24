-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.filtration_maximal_quotient_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:12:13.092988+00:00
-- url     : https://prove2.me/submissions/3107f636-fefa-4ca8-bfc9-4a09c1839964

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_bS_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_bM_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aT_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_aQuot
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_Mpi_eq_image
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_basis_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : LemmaA → SBasis → FiltrationMaximalQuotient := by
  intro hA hS n _ M CF pi hpi mu hmu hmax
  have hlow : DomLowerSet (pi \ {mu}) :=
    ⟨fun nu h => hpi.1 nu h.1, fun nu h la hla hle =>
      ⟨hpi.2 nu h.1 la hla hle, fun heq => h.2 (hmax nu h.1 (by rw [← (heq : la = mu)]; exact hle))⟩⟩
  obtain ⟨Phi, hPhi⟩ := qb_aQuot (qb_basis hA CF ℤ) (qb_sMu CF mu) {y | CF.mu y.1 ∈ pi}
    (fun y hy => by rw [Set.mem_setOf_eq, (hy : CF.mu y.1 = mu)]; exact hmu)
    ((qb_aT (fun j : {j : CF.J // CF.mu j = mu} => qb_bS hS (CF.dom j.1) j.2) (qb_bM hA CF mu)).reindex
      (qb_eqS CF mu))
    (CF.Mpi pi) (CF.Mpi (pi \ {mu})) (qb_Mpi_eq_image hA CF pi hpi) (qb_Mpi_eq_image hA CF (pi \ {mu}) hlow)
  refine ⟨Phi.toAddEquiv.toIntLinearEquiv, ?_⟩
  intro j I x y z hj hI hx hy hz
  have h1 := hPhi x ⟨j, I, hI⟩ hj (by rw [hx, qb_basis_apply, qb_vecF_int])
  rw [Basis.reindex_apply, qb_aT_apply] at h1
  refine Eq.trans h1 ?_
  congr 1
  · exact Subtype.ext ((qb_bS_coe hS _ _ _).trans hy.symm)
  · exact Subtype.ext ((qb_bM_coe hA CF mu _).trans hz.symm)
end Formalism.InvariantFactorPaths.ColumnFamilies
