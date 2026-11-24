-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:30:40.009802+00:00
-- url     : https://prove2.me/submissions/98742a38-7d13-4d10-922c-7a185b7868c1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_aeval_eig
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrTanAlg_exists_integral_primitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
section Eig
variable {S M : Type} [Field S] [AddCommGroup M] [Module S M]
end Eig
section Prim
variable (E : Type) [Field E] [NumberField E]
end Prim
section Decomp
variable {E : Type} [Field E] [NumberField E] {S M : Type} [Field S] [CharZero S] [AddCommGroup M] [Module S M]
  {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem poly_lemma (θ : E) (hθ : IntermediateField.adjoin ℚ {θ} = ⊤) (a : E) :
    ∃ p : ℚ[X], aeval θ p = a := by
  have hint : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  have h1 : Algebra.adjoin ℚ {θ} = ⊤ := by
    first
      | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isIntegral hint, hθ,
          IntermediateField.top_toSubalgebra]
      | rw [← IntermediateField.adjoin_algebraic_toSubalgebra (fun x hx => by
            rw [Set.mem_singleton_iff.mp hx]; exact hint.isAlgebraic), hθ, IntermediateField.top_toSubalgebra]
      | rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => by
            rw [Set.mem_singleton_iff.mp hx]; exact hint.isAlgebraic), hθ, IntermediateField.top_toSubalgebra]
      | rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ,
          IntermediateField.top_toSubalgebra]
  have h2 : a ∈ Algebra.adjoin ℚ {θ} := by
    rw [h1]
    exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
  obtain ⟨p, hp⟩ := (AlgHom.mem_range (aeval θ)).mp h2
  exact ⟨p, hp⟩
private theorem eqchi_lemma_2 (θ : E) (hθ : IntermediateField.adjoin ℚ {θ} = ⊤) (χ₁ χ₂ : E →+* S)
    (h : χ₁ θ = χ₂ θ) : χ₁ = χ₂ := by
  ext a
  obtain ⟨p, rfl⟩ := poly_lemma θ hθ a
  have e : ∀ χ' : E →+* S, χ' (aeval θ p) = aeval (χ' θ) p := fun χ' =>
    (Polynomial.aeval_algHom_apply χ'.toRatAlgHom θ p).symm
  rw [e, e, h]
private theorem dvd_lemma_3 {κ : Type} [Fintype κ] (l : κ → S) (hl : Function.Injective l) (f : S[X])
    (hf : f ≠ 0) (hr : ∀ σ, f.eval (l σ) = 0) : ∏ σ, (X - C (l σ)) ∣ f := by
  classical
  have hs : (Finset.univ.val.map l) ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hl Finset.univ.nodup)]
    intro x hx
    obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hf).mpr (hr σ)
  have h := (Multiset.prod_X_sub_C_dvd_iff_le_roots hf _).mpr hs
  rw [Multiset.map_map] at h
  exact h
private theorem annih_lemma_4 (χ : ι → (E →+* S)) (hχ : Function.Injective χ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End S M) (θ : 𝓞 E)
    (hθ : IntermediateField.adjoin ℚ {(θ : E)} = ⊤) :
    aeval (ρ θ) (∏ σ, (X - C (χ σ (θ : E)))) = 0 := by
  classical
  have hint : IsIntegral ℤ (θ : E) := RingOfIntegers.isIntegral_coe θ
  have hqm : (minpoly ℤ (θ : E)).Monic := minpoly.monic hint
  have hq0 : aeval θ (minpoly ℤ (θ : E)) = 0 := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact minpoly.aeval ℤ (θ : E)
  have hqT : aeval (ρ θ) (minpoly ℤ (θ : E)) = 0 := by
    have h := Polynomial.aeval_algHom_apply ρ.toIntAlgHom θ (minpoly ℤ (θ : E))
    rw [hq0, map_zero] at h
    exact h
  have hlinj : Function.Injective (fun σ => χ σ (θ : E)) :=
    fun σ τ h => hχ (eqchi_lemma_2 (θ : E) hθ (χ σ) (χ τ) h)
  have hqS0 : (minpoly ℤ (θ : E)).map (algebraMap ℤ S) ≠ 0 := (hqm.map _).ne_zero
  have hroot : ∀ σ, ((minpoly ℤ (θ : E)).map (algebraMap ℤ S)).eval (χ σ (θ : E)) = 0 := by
    intro σ
    rw [Polynomial.eval_map_algebraMap]
    have h := Polynomial.aeval_algHom_apply (χ σ).toIntAlgHom (θ : E) (minpoly ℤ (θ : E))
    rw [minpoly.aeval, map_zero] at h
    exact h
  have hdvd := dvd_lemma_3 (fun σ => χ σ (θ : E)) hlinj _ hqS0 hroot
  have hPm : (∏ σ, (X - C (χ σ (θ : E)))).Monic := monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C _
  have hPdeg : (∏ σ, (X - C (χ σ (θ : E)))).natDegree = Fintype.card ι := by
    rw [natDegree_prod_of_monic _ _ fun σ _ => monic_X_sub_C _]
    simp
  have hqdeg : ((minpoly ℤ (θ : E)).map (algebraMap ℤ S)).natDegree ≤ Fintype.card ι := by
    rw [hqm.natDegree_map, hcard]
    have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have h2 := minpoly.natDegree_le (A := ℚ) (θ : E)
    rw [h1, hqm.natDegree_map] at h2
    exact h2
  have heq := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm (hqm.map _) hdvd (by rw [hPdeg]; exact hqdeg)
  rw [← heq, Polynomial.aeval_map_algebraMap]
  exact hqT
private theorem eig_lemma_5 (χ' : E →+* S) (ρ : 𝓞 E →+* Module.End S M) (θ : 𝓞 E)
    (hθ : IntermediateField.adjoin ℚ {(θ : E)} = ⊤) (v : M) (hv : ρ θ v = χ' (θ : E) • v) (a : 𝓞 E) :
    ρ a v = χ' (a : E) • v := by
  obtain ⟨p, hp⟩ := poly_lemma (θ : E) hθ (a : E)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) p
  have hb0 : ((b : ℤ) : S) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero b.prop)
  have hE : aeval (θ : E) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) = (b : ℤ) • (a : E) := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hb, map_zsmul, hp]
  have hO : (b : ℤ) • a = aeval θ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_zsmul, ← Polynomial.aeval_algebraMap_apply]
    exact hE.symm
  have h1 : ρ ((b : ℤ) • a) v = ((b : ℤ) : S) • ρ a v := by
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul S, LinearMap.smul_apply]
  have h2' : ρ (aeval θ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p)) =
      aeval (ρ θ) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) :=
    (Polynomial.aeval_algHom_apply ρ.toIntAlgHom θ _).symm
  have h2 : ρ (aeval θ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p)) v =
      aeval (χ' (θ : E)) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) • v := by
    rw [h2', ← Polynomial.aeval_map_algebraMap (A := S), aeval_eig (ρ θ) (χ' (θ : E)) v hv,
      Polynomial.eval_map_algebraMap]
  have h3 : aeval (χ' (θ : E)) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) =
      χ' ((b : ℤ) • (a : E)) := by
    rw [← hE]
    exact Polynomial.aeval_algHom_apply χ'.toIntAlgHom (θ : E) _
  rw [hO, h2, h3, map_zsmul, ← Int.cast_smul_eq_zsmul S, smul_eq_mul, mul_smul] at h1
  exact (smul_right_injective M hb0 h1).symm
end Decomp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable {E : Type} [Field E] [NumberField E] {S M : Type} [Field S] [CharZero S] [AddCommGroup M] [Module S M]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
theorem _root_.solution (χ : ι → (E →+* S)) (hχ : Function.Injective χ) (hcard : Fintype.card ι = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End S M) :
    (∀ m : M, ∃ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ (a : E) • mσ σ) ∧ ∑ σ, mσ σ = m) ∧
    (∀ mσ : ι → M, (∀ σ (a : 𝓞 E), ρ a (mσ σ) = χ σ (a : E) • mσ σ) → ∑ σ, mσ σ = 0 → ∀ σ, mσ σ = 0) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive E
  have hlinj : Function.Injective (fun σ => χ σ (θ : E)) :=
    fun σ τ h => hχ (eqchi_lemma_2 (θ : E) hθ (χ σ) (χ τ) h)
  have hP := annih_lemma_4 χ hχ hcard ρ θ hθ
  have hinj : Set.InjOn (fun σ => χ σ (θ : E)) (Finset.univ : Finset ι) := fun σ _ τ _ h => hlinj h
  have hLself : ∀ σ, (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ).eval (χ σ (θ : E)) = 1 :=
    fun σ => Lagrange.eval_basis_self hinj (Finset.mem_univ σ)
  have hLne : ∀ σ τ, σ ≠ τ → (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ).eval (χ τ (θ : E)) = 0 :=
    fun σ τ h => Lagrange.eval_basis_of_ne (v := fun σ => χ σ (θ : E)) h (Finset.mem_univ τ)
  have hLsum : ∑ σ, Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ = 1 := by
    by_cases hι : Nonempty ι
    · exact Lagrange.sum_basis hinj Finset.univ_nonempty
    · exfalso
      have h0 : Fintype.card ι = 0 := Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hι)
      rw [hcard] at h0
      exact (Module.finrank_pos (R := ℚ) (M := E)).ne' h0
  have hproj : ∀ σ (w : M), ρ θ (aeval (ρ θ) (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ) w) =
      χ σ (θ : E) • aeval (ρ θ) (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ) w := by
    intro σ w
    have hdvd : (∏ τ, (X - C (χ τ (θ : E)))) ∣
        (X - C (χ σ (θ : E))) * Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ := by
      apply dvd_lemma_3 (fun τ => χ τ (θ : E)) hlinj
      · intro h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact X_sub_C_ne_zero _ h
        · have h1 := hLself σ
          rw [h, Polynomial.eval_zero] at h1
          exact zero_ne_one h1
      · intro τ
        rw [Polynomial.eval_mul]
        by_cases h : σ = τ
        · subst h
          simp
        · rw [hLne σ τ h, mul_zero]
    obtain ⟨r, hr⟩ := hdvd
    have h0 : aeval (ρ θ) ((X - C (χ σ (θ : E))) * Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ) = 0 := by
      rw [hr, map_mul, hP, zero_mul]
    have e : aeval (ρ θ) ((X - C (χ σ (θ : E))) * Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ) w = 0 := by
      rw [h0]
      rfl
    rw [map_mul, map_sub, aeval_X, aeval_C] at e
    exact sub_eq_zero.mp e
  refine ⟨fun m => ⟨fun σ => aeval (ρ θ) (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ) m,
    fun σ a => eig_lemma_5 (χ σ) ρ θ hθ _ (hproj σ m) a, ?_⟩, ?_⟩
  · have h1 : (∑ σ, aeval (ρ θ) (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ)) m = m := by
      rw [← map_sum, hLsum, map_one]
      rfl
    rwa [LinearMap.sum_apply] at h1
  · intro mσ hmσ hsum σ
    have h := congrArg (aeval (ρ θ) (Lagrange.basis Finset.univ (fun σ => χ σ (θ : E)) σ)) hsum
    rw [map_sum, map_zero, Finset.sum_eq_single σ] at h
    · rwa [aeval_eig (ρ θ) (χ σ (θ : E)) (mσ σ) (hmσ σ θ), hLself, one_smul] at h
    · intro τ _ hτ
      rw [aeval_eig (ρ θ) (χ τ (θ : E)) (mσ τ) (hmσ τ θ), hLne σ τ (Ne.symm hτ), zero_smul]
    · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
