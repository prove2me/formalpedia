-- Prove2me | solution 1 for Formalism.GM.FockB.supp_Y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:06.267802+00:00
-- url     : https://prove2.me/submissions/cc8fffad-fa19-407d-af7e-d4595cbb920e

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_chainEmb_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FockB
theorem _root_.solution {t : ℕ} (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) (g : MvPolynomial (BVar N r t) ℚ_[p])
    (m : BVar N r t →₀ ℕ) (hm : m ∈ (rename (chainEmb N r t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, m = Finsupp.mapDomain (chainEmb N r t) m1 + m2 := by
  classical
  have h := support_mul (rename (chainEmb N r t) y) g hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
  rw [support_rename_of_injective (chainEmb_inj t)] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩
end Formalism.GM.FockB
