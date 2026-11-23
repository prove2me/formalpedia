-- Prove2me | solution 1 for Formalism.L2.Th1.F.IsogenyPAux.P_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:12.819888+00:00
-- url     : https://prove2.me/submissions/49d59da2-c96a-483e-9a82-5c7eb1305935

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Elliptic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenyP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.IsogenyPAux
namespace Formalism.L2.Th1.F.IsogenyPAux
theorem _root_.solution (L : PeriodPair) (ω : ℂ) (hω : ω ∈ L.lattice) (w : ℂ) :
    L.weierstrassP w = L.weierstrassPExcept 0 (w - ω) + 1 / (w - ω) ^ 2 := by
  have h1 := L.weierstrassPExcept_add (0 : L.lattice) (w - ω)
  have h2 := L.weierstrassP_sub_coe w ⟨ω, hω⟩
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h1 h2
  rw [← h2, ← h1]
end Formalism.L2.Th1.F.IsogenyPAux
