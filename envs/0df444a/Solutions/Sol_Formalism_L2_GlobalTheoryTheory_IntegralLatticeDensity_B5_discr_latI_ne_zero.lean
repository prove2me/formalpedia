-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discr_latI_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:55.138507+00:00
-- url     : https://prove2.me/submissions/6475da6e-4dec-427c-b1fa-fd117fd05bb8

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_UnitsEqOneOrNegOne
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_LatITopBasis
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_IdealBasis
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_NormArea
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Homothety
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_AreaLatIOfDiscr
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_exists_latI_basis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_discr_closure_pair_ne_zero


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
theorem _root_.solution (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    discr (latI φ 𝔞 1) ≠ 0 := by
  obtain ⟨a, b, h, hl, -⟩ := exists_latI_basis K d hd4 x hx hK φ 𝔞 h𝔞
  rw [hl]; exact discr_closure_pair_ne_zero a b h
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
