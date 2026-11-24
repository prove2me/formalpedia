-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:45.776798+00:00
-- url     : https://prove2.me/submissions/cc7bff3e-f875-4d5e-b29d-c8f5168ff717

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩
end Formalism.HermitianLatticesTheory
