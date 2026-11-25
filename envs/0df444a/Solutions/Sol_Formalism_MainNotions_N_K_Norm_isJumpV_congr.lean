-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.isJumpV_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:25:54.112879+00:00
-- url     : https://prove2.me/submissions/7966d50b-098d-4241-8900-752b0c1b124b

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_MainNotions_N_K_Norm_fildR_eq_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution (τ : K →ₐ[Qp] LL) (a : ℤ) : IsJumpV PD ρ τ a ↔ IsJumpV PD ρ' τ a := by
  unfold IsJumpV
  rw [fildR_eq_comap PD e he, fildR_eq_comap PD e he]
  exact not_congr (Submodule.comap_injective_of_surjective
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).surjective).eq_iff
end Formalism.MainNotions.N.K.Norm
