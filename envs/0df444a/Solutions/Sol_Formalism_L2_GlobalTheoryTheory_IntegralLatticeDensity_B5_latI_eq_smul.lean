-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latI_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:03.051104+00:00
-- url     : https://prove2.me/submissions/92e7746f-a335-4f24-b8ac-41daa0b1fd0b

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Homothety

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (δ : ℂ) : latI φ 𝔞 δ = δ • latI φ 𝔞 1 := by
  unfold latI
  rw [AddSubgroup.pointwise_smul_def]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    exact AddSubgroup.mem_map.2 ⟨φ c, AddSubgroup.subset_closure ⟨c, hc, (one_mul _).symm⟩, rfl⟩
  · refine AddSubgroup.map_le_iff_le_comap.2 ?_
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨c, hc, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, show δ * (1 * φ c) = δ * φ c by rw [one_mul]⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
