-- Prove2me | solution 1 for Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod.diff_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:02.679111+00:00
-- url     : https://prove2.me/submissions/ceb4bb35-546a-4e61-86c9-79c67b8c176f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ZetaQuasi
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isPreconnected_compl
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_add_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
namespace Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
theorem _root_.solution (hd : ZetaHasDeriv) (L : PeriodPair) {ω : ℂ} (hω : ω ∈ L.lattice) {x y : ℂ}
    (hx : x ∉ L.lattice) (hy : y ∉ L.lattice) :
    wZeta L (x + ω) - wZeta L x = wZeta L (y + ω) - wZeta L y := by
  have hD : ∀ z, z ∉ L.lattice → HasDerivAt (fun z => wZeta L (z + ω) - wZeta L z) 0 z := by
    intro z hz
    have h1 := (hd L (z + ω) (add_notMem hω hz)).comp_add_const z ω
    have h2 := h1.sub (hd L z hz)
    have h3 : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    have e : -L.weierstrassP (z + ω) - -L.weierstrassP z = 0 := by rw [h3]; ring
    rw [e] at h2
    exact h2
  exact (isOpen_compl L).is_const_of_deriv_eq_zero (f := fun z => wZeta L (z + ω) - wZeta L z)
    (isPreconnected_compl L)
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).deriv) hx hy
end Formalism.L2.Th1.F.WeierstrassZetaQuasiPeriod
