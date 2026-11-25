-- Prove2me | solution 1 for Formalism.IndefR.Arith.FormsL.mem_Mcoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:07.339577+00:00
-- url     : https://prove2.me/submissions/57a38cb5-2e32-4888-89a7-cea7de47c1ec

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
theorem _root_.solution (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {d : ℕ} (b : Fin d → WL)
    (c : Fin d → LL) : c ∈ A.Mcoord J0 lam0 eC b ↔ ∑ i, c i • b i ∈ A.Mj J0 lam0 eC := by
  simp [Mcoord, Fintype.linearCombination_apply]
end Formalism.IndefR.Arith.FormsL
