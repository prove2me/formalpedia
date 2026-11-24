-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:31.751048+00:00
-- url     : https://prove2.me/submissions/2aabbb4b-2464-46ed-984a-f764eced54bf

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_imI_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ imI M σ J) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (imI M σ J).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  letI : Algebra E M := (σ.codRestrict M hσ).toAlgebra
  have hlift : ∀ a, algebraMap E M a = liftM M (σ a) := fun a =>
    Subtype.ext (by rw [show ((liftM M (σ a) : M) : ℂ) = σ a by simp [liftM, hσ a]]; rfl)
  have hI : imI M σ J = Submodule.span (𝓞 M) (algebraMap E M '' (J : Set E)) := by
    unfold imI
    congr 1
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
  rw [hI] at hs ⊢
  have h := index_imI_ext (E := E) (F := M) J s hs
  exact_mod_cast h
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
