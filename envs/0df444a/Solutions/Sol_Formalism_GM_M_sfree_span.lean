-- Prove2me | solution 1 for Formalism.GM.M.sfree_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:43.280801+00:00
-- url     : https://prove2.me/submissions/0647d317-cfe4-4df4-86f7-f9c49852bf5a

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_sfree_B

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
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp)) : SFree (scalS N r D.T.t) Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx => exact sfree_B D j jp x hx
  | zero => simpa using SFree.C (K := ℚ_[p]) (scalS N r D.T.t) 0
  | add x y _ _ hx hy => exact hx.add _ hy
  | smul c x _ hx => exact fun m hm => hx m (support_smul hm)
end Formalism.GM.M
