-- Prove2me | solution 1 for Formalism.LatticeIndexTer.log_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:35:31.89647+00:00
-- url     : https://prove2.me/submissions/1d4be1eb-07f0-48d0-9aef-5ab4b1d623a0

import Definitions.Def_Formalism_LogFactorialIndices_StatementNorm
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open scoped ComplexConjugate
open IsDedekindDomain NumberField
namespace Formalism.LatticeIndexTer
theorem _root_.solution : LogProductFormula := by
  intro L _ _ x hx
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L,
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) x := ⟨_, rfl⟩
  rw [← hIdef]
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hx
  have hfin : (Function.support fun v : HeightOneSpectrum (𝓞 L) => FractionalIdeal.count L v I).Finite :=
    by
      have hev := FractionalIdeal.finite_factors I
      exact Filter.eventually_cofinite.mp hev
  have hR : (∑ᶠ v : HeightOneSpectrum (𝓞 L), (FractionalIdeal.count L v I : ℝ) *
        Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      ∑ v ∈ hfin.toFinset, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hv
    intro h0
    exact hv (by simp [h0])
  have hsub2 : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 L) =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^ FractionalIdeal.count L v I) ⊆
      (hfin.toFinset : Set _) := by
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_mulSupport] at hv
    intro h0
    exact hv (by simp [h0])
  have hfac : ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^
      FractionalIdeal.count L v I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub2]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI
  have hN1 : FractionalIdeal.absNorm I =
      ∏ v ∈ hfin.toFinset, (Ideal.absNorm v.asIdeal : ℚ) ^ FractionalIdeal.count L v I := by
    conv_lhs => rw [← hfac]
    rw [map_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hN2 : FractionalIdeal.absNorm I = |Algebra.norm ℚ x| := by
    rw [hIdef]
    exact FractionalIdeal.absNorm_span_singleton (𝓞 L) x
  have hprod : ∏ σ : L →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun σ => rfl)
  have hne1 : ∀ σ ∈ (Finset.univ : Finset (L →+* ℂ)), ‖σ x‖ ≠ 0 := fun σ _ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero σ).mpr hx
  have hL : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Real.log_prod hne1, ← norm_prod, hprod]
    congr 1
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    simp
  have hne2 : ∀ v ∈ hfin.toFinset, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count L v I ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [hL, hR, ← Rat.cast_abs, ← hN2, hN1]
  push_cast
  rw [Real.log_prod hne2]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Real.log_zpow]
end Formalism.LatticeIndexTer
