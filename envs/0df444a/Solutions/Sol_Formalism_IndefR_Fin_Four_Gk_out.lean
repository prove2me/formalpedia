-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.Gk_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:34.238809+00:00
-- url     : https://prove2.me/submissions/3aee159e-9536-4354-a7fa-7e7d0315ef57

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_mk_out_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} (g : Gk L Y k) : (g : QY L Y).out ∈ Y ∧ k • (g : QY L Y).out ∈ L := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hg
  rw [AddSubgroup.mem_inf, AddSubgroup.mem_comap] at hy
  obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y
  change (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ Y ∧ k • (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ L
  rw [he]
  rw [AddSubgroup.mem_inf] at hl
  refine ⟨Y.add_mem hy.1 hl.2, ?_⟩
  rw [smul_add]
  exact L.add_mem hy.2 (nsmul_mem hl.1 k)
end Formalism.IndefR.Fin.Four
