-- Prove2me | solution 1 for Formalism.L2.Th1.F.LatOnly.wEta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:31:20.797233+00:00
-- url     : https://prove2.me/submissions/d7238771-bb54-4c45-bb7f-a4b217fbfaf0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_LatticeOnly
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wEta_eq_on

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.LatOnly
variable {L L' : PeriodPair}
namespace Formalism.L2.Th1.F.LatOnly
theorem _root_.solution (h : L.lattice = L'.lattice) : wEta L = wEta L' := by
  have hb0 : L.basis 0 = L.ω₁ := by
    first
      | exact L.basis_zero
      | simp [PeriodPair.basis]
  have hb1 : L.basis 1 = L.ω₂ := by
    first
      | exact L.basis_one
      | simp [PeriodPair.basis]
  have hω₁ : L.ω₁ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨1, 0, by simp⟩
  have hω₂ : L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨0, 1, by simp⟩
  apply L.basis.ext
  intro i
  fin_cases i
  · show wEta L (L.basis 0) = wEta L' (L.basis 0)
    rw [hb0]
    exact wEta_eq_on h hω₁
  · show wEta L (L.basis 1) = wEta L' (L.basis 1)
    rw [hb1]
    exact wEta_eq_on h hω₂
end Formalism.L2.Th1.F.LatOnly
