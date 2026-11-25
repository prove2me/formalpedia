-- Prove2me | solution 1 for Formalism.IndefR.Arith.FormsL.Mj_le_Mall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:07:25.924485+00:00
-- url     : https://prove2.me/submissions/124a2207-fd99-4165-9945-866a6f600592

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open scoped InnerProductSpace Matrix
open Formalism Formalism.IndefR Formalism.IndefR.Arith
variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)
open Formalism.IndefR.Arith.FormsL
namespace Formalism.IndefR.Arith.FormsL
theorem _root_.solution (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    A.Mj J0 lam0 eC ≤ A.Mall J0 lam0 := inf_le_left
end Formalism.IndefR.Arith.FormsL
