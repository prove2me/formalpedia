-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.coordMap_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:19.666786+00:00
-- url     : https://prove2.me/submissions/1ca17ed9-4290-4435-b948-dff30a24952e

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
theorem _root_.solution (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) (g : G) (φ : M)
    (x : G × (MulAction.orbitRel.Quotient G Cl × Fin d)) :
    t2xE Φ ρ (ρ g φ) x = t2xE Φ ρ φ (g * x.1, x.2) := by
  show Φ (ρ x.1 (ρ g φ)) (Quotient.out x.2.1) x.2.2 = Φ (ρ (g * x.1) φ) (Quotient.out x.2.1) x.2.2
  rw [mul_comm g x.1, map_mul]
  rfl
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
