-- Prove2me | solution 1 for Formalism.L2.Th1.F.PDeriv.notMem_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:04.77397+00:00
-- url     : https://prove2.me/submissions/6c6dec83-8a8a-49fc-9ed2-77f1063754fa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PDeriv
namespace Formalism.L2.Th1.F.PDeriv
theorem _root_.solution (L : PeriodPair) (α β : ℚ) {x : ℂ} (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬ (α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  intro hmem
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hmem
  rw [hx] at hmn
  have key := (LinearIndependent.pair_iff.mp L.indep) ((α : ℝ) - m) ((β : ℝ) - n) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination -hmn)
  have ha : α = m := by exact_mod_cast sub_eq_zero.mp key.1
  have hb : β = n := by exact_mod_cast sub_eq_zero.mp key.2
  exact h ⟨by rw [ha]; simp, by rw [hb]; simp⟩
end Formalism.L2.Th1.F.PDeriv
