-- Prove2me | solution 1 for Formalism.IndefR.Arith.FormsL.Mj_sub_Wgood
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:17.549056+00:00
-- url     : https://prove2.me/submissions/ee465b12-8b59-4c8c-8f74-a767930b439d

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
theorem _root_.solution (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {x : WL}
    (hx : x ∈ A.Mj J0 lam0 eC) : x ∈ A.Wgood J0 lam0 eC :=
  ⟨hx.1.2, hx.2⟩
end Formalism.IndefR.Arith.FormsL
