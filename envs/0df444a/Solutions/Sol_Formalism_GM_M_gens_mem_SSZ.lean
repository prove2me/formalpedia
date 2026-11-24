-- Prove2me | solution 1 for Formalism.GM.M.gens_mem_SSZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:02.207801+00:00
-- url     : https://prove2.me/submissions/5ffc0615-fa52-4cb0-8685-afe1e81f8f16

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)
namespace Formalism.GM.M
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ D.SSZ p (r := r) :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨jp, Set.mem_iUnion.mpr ⟨hL, hx⟩⟩⟩)
end Formalism.GM.M
