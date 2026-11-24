-- Prove2me | solution 1 for GenFrameSpan.projZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:19.62812+00:00
-- url     : https://prove2.me/submissions/b9480d1e-498b-4863-8fb5-e03f15aaef69

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Theorems.Thm_GenFrameSpan_SatP_nablaX_eq
import Theorems.Thm_GenFrameSpan_SatP_Tmap_monomial
import Theorems.Thm_GenFrameSpan_SatP_Tmap_prod
import Theorems.Thm_GenFrameSpan_SatP_prod_mem_span

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
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open SatP
namespace GenFrameSpan
theorem _root_.solution : ProjZ := by
  intro hSB Lt _ _ N0 nu
  choose Cm hCm using fun s => hSB ℤ N0 (nu s)
  let π : Lt → (MvPolynomial (ℕ × Fin N0) ℤ →ₗ[ℤ] MvPolynomial (ℕ × Fin N0) ℤ) := fun s =>
    (nablaSpan ℤ N0 (nu s)).subtype ∘ₗ Submodule.projectionOnto _ _ (hCm s)
  have hπmem : ∀ s x, π s x ∈ nablaSpan ℤ N0 (nu s) := fun s x =>
    (Submodule.projectionOnto _ _ (hCm s) x).2
  have hπfix : ∀ s x, x ∈ nablaSpan ℤ N0 (nu s) → π s x = x := fun s x hx => by
    simp only [π, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [Submodule.projectionOnto_apply_left (hCm s) ⟨x, hx⟩]
  refine ⟨Tmap π, fun P => ?_, fun J => ?_⟩
  · rw [MvPolynomial.as_sum P, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : monomial m (coeff m P) = coeff m P • monomial m (1 : ℤ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, LinearMap.map_smul, Tmap_monomial]
    exact Submodule.smul_mem _ _ (prod_mem_span nu _ fun s => hπmem s _)
  · rw [nablaX_eq, Tmap_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hπfix]
    exact Submodule.subset_span ⟨J s, rfl⟩
end GenFrameSpan
