-- Prove2me | solution 1 for Formalism.GM.M.chainEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:02.190116+00:00
-- url     : https://prove2.me/submissions/6b294d55-0fc9-4a5d-a71f-fba318b34a39

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
theorem _root_.solution : Function.Injective (chainEmb N r D.T.t) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Fin.castSucc_inj] at h1
  rw [h1, h2]
end Formalism.GM.M
