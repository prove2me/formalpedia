-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.ib_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:40:09.196765+00:00
-- url     : https://prove2.me/submissions/73a1b84e-f368-4283-804a-44fe36a413f5

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by
  rw [← h₀] at hw
  have hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range := by
    unfold latI
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, by simp⟩
  obtain ⟨c, hc⟩ := hle hw
  exact ⟨c, hc⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
