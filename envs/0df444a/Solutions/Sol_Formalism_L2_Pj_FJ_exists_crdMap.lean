-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.exists_crdMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:29.929901+00:00
-- url     : https://prove2.me/submissions/17d2f730-e089-4538-a555-9b795aaf5a2e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem

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
theorem _root_.solution {X : Data E r} (cu : CuspFD X ρ) :
    ∃ Ψ : (Fin r → E) →ₗ[E] (Fin ρ → E), ∀ v : Fin ρ → E, Ψ (∑ i, v i • cu.e i) = v := by
  let b := Module.Basis.span cu.ind
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Submodule.span E (Set.range cu.e)).subtype (Submodule.ker_subtype _)
  refine ⟨b.equivFun.toLinearMap.comp g, fun v => ?_⟩
  have hmem : ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) :=
    sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hgv : g (∑ i, v i • cu.e i) = ⟨_, hmem⟩ := by
    have := LinearMap.congr_fun hg ⟨_, hmem⟩
    simpa using this
  have hb : (⟨_, hmem⟩ : Submodule.span E (Set.range cu.e)) = b.equivFun.symm v := by
    rw [Module.Basis.equivFun_symm_apply]
    ext
    simp [b, Module.Basis.span_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hgv, hb, LinearEquiv.apply_symm_apply]
end Formalism.L2.Pj.FJ
