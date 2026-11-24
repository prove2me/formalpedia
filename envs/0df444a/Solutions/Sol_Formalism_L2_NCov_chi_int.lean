-- Prove2me | solution 1 for Formalism.L2.NCov.chi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:42:53.840637+00:00
-- url     : https://prove2.me/submissions/08bdeb23-5a49-453d-9414-3964d7534506

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_W_le
import Theorems.Thm_Formalism_L2_NCov_chi_add
import Theorems.Thm_Formalism_L2_NCov_chi_mul
import Theorems.Thm_Formalism_L2_NCov_chi_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}
namespace Formalism.L2.NCov
theorem _root_.solution (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (t : Algebra.adjoin O S) :
    χ t ∈ (algebraMap O K).range := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    exact hint x hx _ fun h => hW (eq_bot_iff.2 ((W_le _ χ ⟨x, Algebra.subset_adjoin hx⟩).trans h.le))
  | algebraMap r => exact ⟨r, (chi_alg hW r).symm⟩
  | add x y hx hy ihx ihy =>
    have e := chi_add hS hW ⟨x, hx⟩ ⟨y, hy⟩
    rw [show (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, e]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    have e := chi_mul hS hW ⟨x, hx⟩ ⟨y, hy⟩
    rw [show (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O S) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, e]
    exact mul_mem ihx ihy
end Formalism.L2.NCov
