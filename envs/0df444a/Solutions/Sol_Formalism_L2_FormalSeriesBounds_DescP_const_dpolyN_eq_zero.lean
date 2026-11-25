-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.DescP.const_dpolyN_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:26.039308+00:00
-- url     : https://prove2.me/submissions/e3acd8db-0a8e-4fb5-88a1-686af3abf8ee

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_HiOrd_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_HiOrd_dmonN
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.DescP
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) {g : PS k n d} (h : HiOrd (P.totalDegree + 1) g) :
    constantCoeff (DpolyN F cp u P g) = 0 := by
  unfold DpolyN
  rw [map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hd : Finsupp.degree m ≤ P.totalDegree := by
    have h1 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.degree_apply]
    exact h1
  have h1 : HiOrd 1 (DmonN F cp u m g) := HiOrd.dmonN F cp u m (h.mono (by omega))
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (DmonN F cp u m g), h1 0 (by simp), mul_zero]
end Formalism.L2.FormalSeriesBounds.DescP
