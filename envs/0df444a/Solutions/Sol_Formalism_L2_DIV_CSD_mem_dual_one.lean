-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.mem_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:51.274966+00:00
-- url     : https://prove2.me/submissions/be8ea4eb-09c9-4eeb-97cc-9731433f545a

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Theorems.Thm_Formalism_L2_DIV_CSD_pairOne_apply
import Theorems.Thm_Formalism_L2_DIV_CSD_star_mem_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (pairOne K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, pairOne_apply]
  constructor
  · intro h
    simpa using h 1 (Submodule.one_le.mp le_rfl)
  · intro hy z hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (star_mem_one hz)
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp hy
    exact Submodule.mem_one.mpr ⟨a * b, by rw [map_mul, ha, hb]⟩
end Formalism.L2.DIV.CSD
