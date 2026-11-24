-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_map_span_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.42137+00:00
-- url     : https://prove2.me/submissions/bebec836-8b28-4cd1-bb4c-4f37954c4249

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt

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
theorem _root_.solution {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S : Set A)
    (y : A) (hy : y ∈ Submodule.span ℤ S) : φ y ∈ Submodule.span F (φ '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul m x _ hx => rw [map_zsmul]; exact zsmul_mem hx m
end Formalism.InvariantFactorPaths.ColumnFamilies
