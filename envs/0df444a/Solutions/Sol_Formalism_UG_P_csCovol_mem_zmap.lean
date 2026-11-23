-- Prove2me | solution 1 for Formalism.UG.P.csCovol_mem_zmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:16.519179+00:00
-- url     : https://prove2.me/submissions/91a2e3d7-6b90-4772-ba93-04c7999b528a

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {N : ℕ}
  (ι : V →+ EuclideanSpace ℝ (Fin N))
namespace Formalism.UG.P
theorem _root_.solution (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ Formalism.HermitianLatticesTheory.zmap ι M ↔ ∃ y ∈ M, ι y = v := by
  first
  | exact Iff.rfl
  | simp [Formalism.HermitianLatticesTheory.zmap, AddSubgroup.mem_map]
  | (unfold Formalism.HermitianLatticesTheory.zmap; rw [AddSubgroup.mem_toIntSubmodule, AddSubgroup.mem_map]; rfl)
end Formalism.UG.P
