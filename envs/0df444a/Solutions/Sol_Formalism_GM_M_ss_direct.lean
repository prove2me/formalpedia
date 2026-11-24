-- Prove2me | solution 1 for Formalism.GM.M.ss_direct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:40.113291+00:00
-- url     : https://prove2.me/submissions/603e5e7e-3f54-4513-805b-8cbd8478aab0

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_absDirect
import Theorems.Thm_Formalism_GM_M_lv_inj
import Theorems.Thm_Formalism_GM_M_topV
import Theorems.Thm_Formalism_GM_M_Q_of_top

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
theorem _root_.solution :
    iSupIndep (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) := by
  apply absDirect (scalS N r D.T.t) _ (fun ij => lv ij.1.1 ij.1.2)
  · intro a b h
    obtain ⟨h1, h2⟩ := lv_inj h
    exact Subtype.ext (Prod.ext h1 h2)
  · intro L v hv
    obtain ⟨_, _, _, _, _, h1, _⟩ := topV D _ _ v hv
    exact h1
  · intro L v hv htop
    obtain ⟨Q, _, rfl, hz⟩ := Q_of_top D _ _ v hv (fun c => c = 0) rfl htop
    have : Q = 0 := by ext n; simpa using hz n
    rw [this, mul_zero]
end Formalism.GM.M
