-- Prove2me | solution 1 for Formalism.L2.NCov.exists_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:13.806809+00:00
-- url     : https://prove2.me/submissions/49d508b2-dd42-4a70-af1e-95b23b10998c

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_chi_add
import Theorems.Thm_Formalism_L2_NCov_chi_mul
import Theorems.Thm_Formalism_L2_NCov_chi_alg
import Theorems.Thm_Formalism_L2_NCov_chi_int

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
    (hinj : Function.Injective (algebraMap O K))
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, pt ψ = χ := by
  have h := fun t => RingHom.mem_range.1 (chi_int hS hint hW t)
  choose f hf using h
  have h1 : f 1 = 1 := hinj (by rw [hf, map_one]; simpa using chi_alg hW (1 : O))
  have hm : ∀ s t, f (s * t) = f s * f t := fun s t => hinj (by rw [hf, map_mul, hf, hf, chi_mul hS hW])
  have h0 : f 0 = 0 := hinj (by rw [hf, map_zero]; simpa using chi_alg hW (0 : O))
  have ha : ∀ s t, f (s + t) = f s + f t := fun s t => hinj (by rw [hf, map_add, hf, hf, chi_add hS hW])
  have hc : ∀ c, f (algebraMap O (Algebra.adjoin O S) c) = c := fun c => hinj (by rw [hf, chi_alg hW])
  exact ⟨{ toFun := f, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha, commutes' := hc },
    funext fun t => hf t⟩
end Formalism.L2.NCov
