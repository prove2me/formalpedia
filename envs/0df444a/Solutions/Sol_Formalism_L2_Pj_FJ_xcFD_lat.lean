-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.xcFD_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:59.858255+00:00
-- url     : https://prove2.me/submissions/9a7cfda8-87df-4e72-8bd7-e278493cc252

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_trBE_nondeg
import Theorems.Thm_Formalism_L2_Pj_FJ_exists_basis
import Theorems.Thm_Formalism_L2_Pj_FJ_xcFD_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.IsLattice E (XcFD 𝔄 cu) := by
  classical
  obtain ⟨ι, _, b, hb⟩ := exists_basis 𝔄 h𝔄 cu
  have hX : (XcFD 𝔄 cu).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((trBE ρ).dualBasis (trBE_nondeg ρ) b)) := by
    rw [xcFD_restrict, ← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ (trBE_nondeg ρ) b]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.FG.restrictScalars_iff (R := ℤ), hX]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff]
    have h1 : Submodule.span ℚ (Set.range ((trBE ρ).dualBasis (trBE_nondeg ρ) b)) = ⊤ :=
      Module.Basis.span_eq _
    have h2 : Set.range ((trBE ρ).dualBasis (trBE_nondeg ρ) b) ⊆ (XcFD 𝔄 cu : Set (Fin ρ → E)) := by
      have h3 : Set.range ((trBE ρ).dualBasis (trBE_nondeg ρ) b) ⊆
          ((XcFD 𝔄 cu).restrictScalars ℤ : Set (Fin ρ → E)) := by
        rw [hX]; exact Submodule.subset_span
      rwa [Submodule.coe_restrictScalars] at h3
    intro v _
    have hv : v ∈ Submodule.span ℚ (XcFD 𝔄 cu : Set (Fin ρ → E)) := by
      have h4 := Submodule.span_mono (R := ℚ) h2
      rw [h1] at h4
      exact h4 Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ E _ hv
end Formalism.L2.Pj.FJ
