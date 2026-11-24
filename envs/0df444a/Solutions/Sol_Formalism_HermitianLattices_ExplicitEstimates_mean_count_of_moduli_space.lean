-- Prove2me | solution 1 for Formalism.HermitianLattices.ExplicitEstimates.mean_count_of_moduli_space
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:47.93341+00:00
-- url     : https://prove2.me/submissions/74671267-f0f2-4461-af53-cd155b6c9ed2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_IntegralMultipleNormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SeparatedSetPackingBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FibreCardinalityOfModuliMap
import Theorems.Thm_Formalism_HermitianLattices_TraceIntegrality_separated_set_packing_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.ExplicitEstimates
open Finset
open scoped NumberField
private theorem g4w1_min (K : Type) [Field K] [NumberField K] (x : 𝓞 K) (hx : x ≠ 0) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ φ : K →+* ℂ, ‖φ (x : K)‖ := by
  have hx' : (x : K) ≠ 0 := by simpa using hx
  have hN : (1:ℝ) ≤ ∏ φ : K →+* ℂ, ‖φ (x:K)‖ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K)) = ∏ σ : K →ₐ[ℚ] ℂ, σ (x:K) :=
      Algebra.norm_eq_prod_embeddings ℚ ℂ (x:K)
    have h2 : ∏ φ : K →+* ℂ, ‖φ (x:K)‖ = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K))‖ := by
      rw [h1, norm_prod]
      exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
    rw [h2, ← Algebra.coe_norm_int x]
    have h3 : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    simp
    exact_mod_cast Int.one_le_abs h3
  have hpos : ∀ φ : K →+* ℂ, 0 < ‖φ (x:K)‖ := fun φ => norm_pos_iff.mpr ((map_ne_zero φ).mpr hx')
  have hlog : 0 ≤ ∑ φ : K →+* ℂ, Real.log (‖φ (x:K)‖) := by
    rw [← Real.log_prod (fun φ _ => (hpos φ).ne')]
    exact Real.log_nonneg hN
  have : ∑ φ : K →+* ℂ, (1 + Real.log (‖φ (x:K)‖)) ≤ ∑ φ : K →+* ℂ, ‖φ (x:K)‖ :=
    Finset.sum_le_sum fun φ _ => by
      linarith [Real.add_one_le_exp (Real.log (‖φ (x:K)‖)), Real.exp_log (hpos φ)]
  rw [Finset.sum_add_distrib] at this
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, mul_one] at this
  linarith
end Formalism.HermitianLattices.ExplicitEstimates
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ExplicitEstimates
open Finset
open scoped NumberField
namespace Formalism.HermitianLattices.ExplicitEstimates
theorem _root_.solution : Ms_count_mean := by
  intro K _ _ ρ hρ
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Module.finrank_pos
  set S : Set (𝓞 K) := {x : 𝓞 K | (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (d : ℝ) ≤ ρ} with hS

  let ι : 𝓞 K →+ PiLp 1 (fun _ : K →+* ℂ => ℂ) :=
    { toFun := fun x => WithLp.toLp 1 (fun φ : K →+* ℂ => φ (x : K))
      map_zero' := by ext φ; simp
      map_add' := by intro x y; ext φ; simp }
  have hιn : ∀ x : 𝓞 K, ‖ι x‖ = ∑ φ : K →+* ℂ, ‖φ (x : K)‖ := by
    intro x
    rw [PiLp.norm_eq_of_L1]
    rfl
  let b := NumberField.RingOfIntegers.basis K
  let E : Submodule ℝ (PiLp 1 (fun _ : K →+* ℂ => ℂ)) := Submodule.span ℝ (Set.range fun i => ι (b i))
  have hE : Module.finrank ℝ E ≤ d := by
    have h := finrank_range_le_card (R := ℝ) (fun i => ι (b i))
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank] at h
    exact h
  have hmem : ∀ x : 𝓞 K, ι x ∈ E := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact E.toAddSubgroup.zsmul_mem (Submodule.subset_span ⟨i, rfl⟩) _
  let j : 𝓞 K → E := fun x => ⟨ι x, hmem x⟩
  have hsep : ∀ x y : 𝓞 K, x ≠ y → (d : ℝ) ≤ ‖j x - j y‖ := by
    intro x y hxy
    have : ‖j x - j y‖ = ‖ι (x - y)‖ := by
      rw [map_sub]; rfl
    rw [this, hιn]
    exact g4w1_min K (x - y) (sub_ne_zero.mpr hxy)
  have hj : Function.Injective j := by
    intro x y hxy
    by_contra hne
    have := hsep x y hne
    rw [hxy, sub_self, norm_zero] at this
    linarith
  have hbound : ∀ s : Finset (𝓞 K), (↑s : Set (𝓞 K)) ⊆ S → (s.card : ℝ) ≤ (2 * ρ + 1) ^ d := by
    intro s hs
    classical
    have h := Formalism.HermitianLattices.TraceIntegrality.separated_set_packing_bound E (s.image j) (d * ρ) d hd0 (by positivity)
      (by
        intro c hc
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
        have hx' : (∑ φ : K →+* ℂ, ‖φ (x : K)‖) / (d : ℝ) ≤ ρ := hs hx
        have : ‖j x‖ = ‖ι x‖ := rfl
        rw [this, hιn]
        rw [div_le_iff₀ hd0] at hx'
        linarith)
      (by
        intro c hc c' hc' hne
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc'
        exact hsep x y (fun h => hne (by rw [h])))
    rw [Finset.card_image_of_injective _ hj] at h
    have e : 1 + 2 * ((d : ℝ) * ρ) / d = 2 * ρ + 1 := by field_simp; ring
    rw [e] at h
    exact h.trans (pow_le_pow_right₀ (by linarith) hE)
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 * ρ + 1) ^ d)
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have := hbound s hs
    rw [hcard] at this
    linarith
  refine ⟨hfin, ?_⟩
  have := hbound hfin.toFinset (by simp)
  rwa [← Set.ncard_eq_toFinset_card S hfin] at this
end Formalism.HermitianLattices.ExplicitEstimates
