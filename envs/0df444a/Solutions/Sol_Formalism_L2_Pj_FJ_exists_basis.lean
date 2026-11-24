-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:49:33.75649+00:00
-- url     : https://prove2.me/submissions/7d031479-c095-4b03-be25-1b9d2c573f13

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_crdI_lat

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
    (cu : CuspFD X ρ) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ (Fin ρ → E)),
      Submodule.span ℤ (Set.range b) = (crdI 𝔄 cu).restrictScalars ℤ := by
  have := crdI_lat 𝔄 h𝔄 cu
  set X0 := (crdI 𝔄 cu).restrictScalars ℤ
  let b := Module.Free.chooseBasis ℤ X0
  refine ⟨_, inferInstance, b.extendOfIsLattice ℚ, ?_⟩
  have hr : Set.range (b.extendOfIsLattice ℚ) = X0.subtype '' Set.range b := by
    ext v
    simp [Module.Basis.extendOfIsLattice_apply]
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
end Formalism.L2.Pj.FJ
