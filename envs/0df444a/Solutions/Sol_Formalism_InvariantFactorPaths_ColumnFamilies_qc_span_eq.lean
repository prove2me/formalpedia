-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:43.509385+00:00
-- url     : https://prove2.me/submissions/e060f571-6fd7-46b9-bd71-52d0cbd098cb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_map_span_mem

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
theorem _root_.solution {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S T : Set A)
    (h : Submodule.span ℤ S = Submodule.span ℤ T) : Submodule.span F (φ '' S) = Submodule.span F (φ '' T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ T x (h ▸ Submodule.subset_span hx)
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact qc_map_span_mem φ S x (h.symm ▸ Submodule.subset_span hx)
end Formalism.InvariantFactorPaths.ColumnFamilies
