-- Prove2me | solution 1 for Formalism.IndefR.Arith.FormsL.pet_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:23.200956+00:00
-- url     : https://prove2.me/submissions/4f5c4afc-ac7c-4211-8f95-3574f3132a1f

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
theorem _root_.solution (σ : LL →+* ℂ) (x : WL) : A.pet σ x x = ((A.nrmAt σ x : ℝ) : ℂ) ^ 2 := by
  simp [pet, nrmAt, inner_self_eq_norm_sq_to_K]
end Formalism.IndefR.Arith.FormsL
