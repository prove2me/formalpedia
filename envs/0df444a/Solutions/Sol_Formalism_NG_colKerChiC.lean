-- Prove2me | solution 1 for Formalism.NG.colKerChiC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:24.348726+00:00
-- url     : https://prove2.me/submissions/3ba21da7-37f7-418a-bef5-2f7644a8fc34

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_eq_zero_of_gens
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sig0Rel
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sigRel
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
theorem _root_.solution : StatColKerChiC := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 he₁ hE hk0 hδ
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
  have hσ0 : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    rw [map_sig0Rel, sub_smul, hδ, hE, sub_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hν : ∀ φ ∈ K, ∀ l, φ (q (fNu l)) ∈
      LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) := by
    intro φ hφ l
    rw [LinearMap.mem_ker]
    funext g
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, g.2, rfl⟩))
    rw [map_colGenJ] at h
    obtain ⟨b, hb⟩ := hk0 l g
    simp only [LinearMap.comp_apply, hKY φ hφ, hσ φ, zero_add, hb, neg_smul, mul_smul, hE,
      smul_zero, neg_zero, add_zero, Finset.sum_const_zero] at h
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) - φ (q (fNu l)) = 0
    rw [sub_smul, one_smul] at h
    exact h
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let Φ : K →ₗ[O] ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) ×
      LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
    LinearMap.pi fun l =>
      (LinearMap.codRestrict _ (evK (q (fNu l))) (fun φ => hν φ.1 φ.2 l)).prod
        (LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 l))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have h1 : ∀ l, φ.1 (q (fNu l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.fst (congrFun h l))
    have h2 : ∀ l, φ.1 (q (fSig0 l)) = 0 := fun l =>
      congrArg Subtype.val (congrArg Prod.snd (congrFun h l))
    exact Subtype.ext (eq_zero_of_gens φ.1 (hKY φ.1 φ.2) h1 (hσ φ.1) h2)
  calc Module.length O K
      ≤ Module.length O ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) ×
          LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO)) :=
        Module.length_le_of_injective Φ hΦ
    _ = ∑ l, (Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) +
          (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) := by
        rw [Module.length_pi_of_fintype]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Module.length_prod, KernelLengthBounds.length_ker_smul_pi]
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_assoc]
end Formalism.NG
