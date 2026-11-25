-- Prove2me | solution 1 for CompanionTheory.L3H.inv_mem_Rl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:26:35.889186+00:00
-- url     : https://prove2.me/submissions/1420f3ff-e72c-454c-999f-13cedb2c2e17

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
namespace CompanionTheory.L3H
theorem _root_.solution {m : ℕ} (hm : ¬ l ∣ m) : ∃ r : Rl l, algebraMap (Rl l) ℂ r = (m : ℂ)⁻¹ := by
  have hS : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl := fun h =>
    hm (Int.natCast_dvd_natCast.1 (Ideal.mem_span_singleton.1 h))
  refine ⟨⟨(m : ℚ)⁻¹, 1, m, hS, by simp⟩, ?_⟩
  rw [IsScalarTower.algebraMap_apply (Rl l) ℚ ℂ]
  simp
end CompanionTheory.L3H
