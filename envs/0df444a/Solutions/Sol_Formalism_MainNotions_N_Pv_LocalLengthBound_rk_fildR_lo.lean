-- Prove2me | solution 1 for Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:17.949803+00:00
-- url     : https://prove2.me/submissions/7180dccc-3356-4102-9169-a92d7c6b1379

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Window
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientImageDivisibility_RkMultVOfNotJump
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_anti
import Theorems.Thm_Formalism_MainNotions_N_Pv_LocalLengthBound_rk_filV_fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.Pv Formalism.MainNotions.N.Pv.LocalLengthBound
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
variable (ρ : Representation LL G V)
namespace Formalism.MainNotions.N.Pv.LocalLengthBound
theorem _root_.solution (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := rk_filV_fd PD (DdRE PD ρ τ)
  exact ⟨lo, fun a ha => inf_eq_left.2 (hlo.trans (rk_filV_anti PD ha))⟩
end Formalism.MainNotions.N.Pv.LocalLengthBound
