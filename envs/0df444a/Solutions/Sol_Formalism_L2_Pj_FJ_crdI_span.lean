-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.crdI_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:22:03.543624+00:00
-- url     : https://prove2.me/submissions/d5445b54-5fc0-45ff-ac9a-7cc29d839786

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_span_rat_smul_mem
import Theorems.Thm_Formalism_L2_Pj_FJ_exists_smul_mem
import Theorems.Thm_UpperTheory_Reformulated_B_LocalSituation_exists_smul_mem


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
    (cu : CuspFD X ρ) : Submodule.span ℚ (crdI 𝔄 cu : Set (Fin ρ → E)) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ (𝔄 : Submodule (𝓞 E) E), a ≠ 0 := by
    by_contra hne
    push Not at hne
    apply h𝔄
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨fun hx => hne x hx, fun hx => hx ▸ (𝔄 : Submodule (𝓞 E) E).zero_mem⟩
  classical
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ w]
  refine sum_mem fun i _ => span_rat_smul_mem _ (w i) ?_
  obtain ⟨c, hc, hcI⟩ := exists_smul_mem X (cu.e i)
  set cE : E := algebraMap (𝓞 E) E c
  have hcE : cE ≠ 0 := by
    intro h
    exact hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
  have hx : c • cu.e i ∈ cu.I :=
    ⟨hcI, Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩ :
      cu.e i ∈ (Submodule.span E (Set.range cu.e)).restrictScalars (𝓞 E))⟩
  have hv : (Pi.single i (a * cE) : Fin ρ → E) ∈ crdI 𝔄 cu := by
    refine Submodule.subset_span ⟨a, ha, c • cu.e i, hx, ?_⟩
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    rw [← algebraMap_smul E c, smul_smul]
    simp [cE]
  have hsp := span_rat_smul_mem _ (a * cE)⁻¹ (Submodule.subset_span hv)
  convert hsp using 1
  funext j
  by_cases h : i = j
  · subst h; simp; field_simp
  · simp [h, Ne.symm h]
end Formalism.L2.Pj.FJ
