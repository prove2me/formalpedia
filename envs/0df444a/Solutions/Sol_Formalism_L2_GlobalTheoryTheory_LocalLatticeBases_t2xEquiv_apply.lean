-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.t2xEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:33.975027+00:00
-- url     : https://prove2.me/submissions/d56d751f-e5ff-45e7-a357-5ab5985e1ac3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_CoordMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Classical
variable {G : Type} [CommGroup G] [Fintype G] {Cl : Type} [Fintype Cl] [MulAction G Cl] {d : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) (φ : M) :
    orbitDecompositionLinearEquiv Φ ρ hmono hfree φ = t2xE Φ ρ φ := rfl
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
