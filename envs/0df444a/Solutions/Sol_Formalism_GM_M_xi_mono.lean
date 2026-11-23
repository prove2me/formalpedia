-- Prove2me | solution 1 for Formalism.GM.M.xi_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:27.636564+00:00
-- url     : https://prove2.me/submissions/7143c210-726d-4172-aa7d-4a74c1054ab4

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
theorem _root_.solution {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m : BVar N r D.T.t →₀ ℕ} (hm : m ∈ g.support) :
    (∀ v ∈ m.support, ∃ c, v = xiVar N r D.T.t c) ∧ ∑ c, m (xiVar N r D.T.t c) = b := by
  have := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff] at this
  exact this hm
end Formalism.GM.M
