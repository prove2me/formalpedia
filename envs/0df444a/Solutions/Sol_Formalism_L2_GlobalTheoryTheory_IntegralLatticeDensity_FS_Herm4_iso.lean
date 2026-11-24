-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:11.949389+00:00
-- url     : https://prove2.me/submissions/fc5e4ae3-6b7d-4628-97a3-1bcaf65d180e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_ortho_basis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_iso_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace Herm4
theorem _root_.solution (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), ∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a) := by
  obtain ⟨b, hb⟩ := H.ortho_basis hn
  have hpos : ∀ i, ∃ P : K × K × K × K, c P.1 = P.1 ∧ c P.2.1 = P.2.1 ∧ c P.2.2.1 = P.2.2.1 ∧
      c P.2.2.2 = P.2.2.2 ∧ h (b i) (b i) = P.1 ^ 2 + P.2.1 ^ 2 + P.2.2.1 ^ 2 + P.2.2.2 ^ 2 := fun i => by
    obtain ⟨-, p, q, r, s, h1, h2, h3, h4, h5⟩ := H.pos (b i) (b.ne_zero i)
    exact ⟨(p, q, r, s), h1, h2, h3, h4, h5⟩
  choose P hP using hpos
  obtain ⟨g, hg, -⟩ := H.iso_of b hb (fun i => (P i).1) (fun i => (P i).2.1) (fun i => (P i).2.2.1)
    (fun i => (P i).2.2.2) (fun i => (hP i).1) (fun i => (hP i).2.1) (fun i => (hP i).2.2.1)
    (fun i => (hP i).2.2.2.1) (fun i => (hP i).2.2.2.2)
  exact ⟨g, hg⟩
end Herm4
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
