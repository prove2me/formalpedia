-- Prove2me | solution 1 for Formalism.NG.colKerChiOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:25.259904+00:00
-- url     : https://prove2.me/submissions/d303f2d9-e33d-44cc-a847-4eff000bc67a

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Theorems.Thm_Formalism_NG_ColKerChi_map_nuRel
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_eq_zero_of_gens
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sigRel
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open ColumnGeneratorDecomposition ColKerChi
namespace Formalism.NG
theorem _root_.solution : StatColKerChiOne := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 ℓ e' hu he₁ hE hδ hk
  let K := kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0
  let q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0 := Submodule.mkQ _
  have hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j),
      z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0 := fun φ z hz => by
    rw [LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0 := fun φ hφ y =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)
  have hσ : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) = 0 := by
    intro φ l a
    have h := hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    rw [map_sigRel, sub_smul, one_smul, he₁, sub_zero] at h
    exact h
  have hν : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fNu l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l E 0 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))))
    rw [map_nuRel, hE] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hσ0 : ∀ φ ∈ K, ∀ l, φ (q (fSig0 l)) ∈ LinearMap.ker
      (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) := by
    intro φ hφ l
    obtain ⟨g, hgD, c, hc, hkc⟩ := hk l
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, hgD, rfl⟩))
    rw [map_colGenJ] at h
    have hu' : ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) = φ (q (fNu l)) := hu g _
    simp only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, sub_smul, one_smul, hu', sub_self,
      neg_smul, mul_smul, hkc, hδ, smul_zero, Finset.sum_const_zero, add_zero,
      neg_eq_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    have key : c • (((ℓ : O) ^ e' l * δO * δO) • φ (q (fSig0 l))) = 0 := by
      rw [smul_smul, show c * ((ℓ : O) ^ e' l * δO * δO) = δO * ((ℓ : O) ^ e' l * δO * c) by ring]
      simpa only [mul_smul] using h
    exact hc.smul_eq_zero.mp key
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let Φ : K →ₗ[O] ((l : ι) →
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) ×
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
    LinearMap.pi fun l =>
      (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 φ.2 l)).prod
        (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 l))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have h1 : ∀ l, φ.1 (q (fSig0 l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.fst (congrFun h l))
    have h2 : ∀ l, φ.1 (q (fNu l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.snd (congrFun h l))
    exact Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h2 (hσ φ.1) h1)
  calc Module.length O K
      ≤ Module.length O ((l : ι) →
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) ((ℓ : O) ^ e' l * δO * δO)) ×
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
        Module.length_le_of_injective Φ hΦ
    _ = ∑ l, ((Fintype.card d : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          2 * IsDiscreteValuationRing.addVal O δO) +
          (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) := by
        rw [Module.length_pi_of_fintype]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Module.length_prod, KernelLengthBounds.length_ker_smul_pi, KernelLengthBounds.length_ker_smul_pi,
          AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow,
          ← IdempotentNormalFormsLenFacts.length_quot_span (ℓ : O), nsmul_eq_mul]
        ring
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_assoc]
end Formalism.NG
