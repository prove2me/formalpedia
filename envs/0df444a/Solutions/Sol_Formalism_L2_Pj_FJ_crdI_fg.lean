-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.crdI_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:00.588333+00:00
-- url     : https://prove2.me/submissions/d83ec941-678c-413f-b5b8-f9326f9ba8c5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_exists_crdMap
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


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
theorem _root_.solution (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (crdI 𝔄 cu).FG := by
  obtain ⟨Ψ, hΨ⟩ := exists_crdMap cu
  obtain ⟨d, hd, hdA⟩ := 𝔄.isFractional
  have hI : cu.I.FG := Submodule.FG.of_le X.Λ_fg inf_le_left
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hd
      (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
  set Ψ' : (Fin r → E) →ₗ[E] (Fin ρ → E) := (algebraMap (𝓞 E) E d)⁻¹ • Ψ
  refine Submodule.FG.of_le (hI.map (Ψ'.restrictScalars (𝓞 E))) ?_
  rw [crdI, Submodule.span_le]
  rintro v ⟨a, ha, x, hx, hax⟩
  obtain ⟨o, ho⟩ := hdA a ha
  refine ⟨o • x, cu.I.smul_mem o hx, ?_⟩
  show Ψ' (o • x) = v
  have hcoef : (algebraMap (𝓞 E) E d)⁻¹ * algebraMap (𝓞 E) E o = a := by
    rw [ho, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  rw [← hΨ v, ← hax]
  show ((algebraMap (𝓞 E) E d)⁻¹ • Ψ) (o • x) = Ψ (a • x)
  rw [LinearMap.smul_apply, ← algebraMap_smul E o x, map_smul, smul_smul, hcoef, map_smul]
end Formalism.L2.Pj.FJ
