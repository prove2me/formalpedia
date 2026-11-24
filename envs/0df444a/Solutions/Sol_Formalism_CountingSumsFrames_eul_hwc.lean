-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eul_hwc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:45.946681+00:00
-- url     : https://prove2.me/submissions/e6c5d830-bada-4418-a951-b380adb6c947

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_eul_keep_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (i0 : Fin N) (la : Fin r → ℤ) :
    ∀ x ∈ HWC p LL j univ la, ProjS.eulL (fun c : Fin r => (i0, c)) x ∈ HWC p LL j univ la := by
  intro x hx
  obtain ⟨hw, hk⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨eul_keep_supp _ _ x hw, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk ⊢
  intro c d hcd
  rw [← eul_glAct, hk c d hcd, map_zero]
end Formalism.CountingSumsFrames
