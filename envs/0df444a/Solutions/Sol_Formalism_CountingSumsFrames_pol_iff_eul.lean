-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pol_iff_eul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:31.511427+00:00
-- url     : https://prove2.me/submissions/0c1395cb-8d6a-4589-ac2c-dae16be7bd6f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_GM_ProjS_coeff_eulL
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support


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
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {N r : ℕ} (LL : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Pol p r LL ↔ ∀ i : Fin N, ProjS.eulL (fun c : Fin r => (i, c)) x = ((LL.deg i : ℕ) : ℚ_[p]) • x := by
  rw [Pol, mem_restrictSupport_iff]
  constructor
  · intro h i
    exact ProjS.eulL_of_support _ _ _ (fun m hm => h (Finset.mem_coe.mpr hm) i)
  · intro h m hm i
    have hc := congrArg (coeff m) (h i)
    rw [ProjS.coeff_eulL, coeff_smul, smul_eq_mul] at hc
    have hne : coeff m x ≠ 0 := mem_support_iff.mp hm
    have h2 : (∑ c, (m (i, c) : ℚ_[p])) = (LL.deg i : ℚ_[p]) :=
      mul_left_cancel₀ hne (hc.trans (mul_comm _ _))
    exact_mod_cast h2
end Formalism.CountingSumsFrames
