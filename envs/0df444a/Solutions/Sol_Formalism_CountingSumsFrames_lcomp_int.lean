-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:04.53418+00:00
-- url     : https://prove2.me/submissions/7cb7f599-3717-4fe9-884a-8838fb7d86e6

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_nil
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution {p : ℕ} [Fact p.Prime] {N r : ℕ} {ι : Type*} [LinearOrder ι] (LL : Letters N) (e1 : ℕ)
    (P : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL)
    (hint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin N × Fin r)) :
    ∀ l : List ι, ∀ u ∈ PolZ p r LL, ((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u ∈ PolZ p r LL
  | [], u, hu => by simpa [lcomp_nil] using hu
  | a :: l, u, hu => by
    have ih := solution LL e1 P hpol hint l u hu
    have e : ((p : ℚ_[p]) ^ (e1 * (a :: l).length)) • lcomp P (a :: l) u =
        ((p : ℚ_[p]) ^ e1) • P a (((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u) := by
      rw [lcomp_cons, LinearMap.comp_apply, map_smul, smul_smul, ← pow_add, List.length_cons]
      congr 2; ring
    rw [e]
    refine Submodule.mem_inf.mpr ⟨?_, hint a _ ih⟩
    exact (Pol p r LL).smul_mem _ (hpol a _ (Submodule.mem_inf.mp ih).1)
end Formalism.CountingSumsFrames
