-- Prove2me | solution 1 for Formalism.NG.colKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:33.512622+00:00
-- url     : https://prove2.me/submissions/6e41d853-335d-4cd7-a352-1702e5a35d02

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_colGenJ
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sigRel
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_map_sig0Rel
import Theorems.Thm_Formalism_NG_ColumnGeneratorDecomposition_eq_zero_of_gens
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_colData_le


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
open ColumnGeneratorDecomposition
namespace Formalism.NG
theorem _root_.solution : StatColKer := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 ℓ e' hE hk0 hδ heq hlift
  obtain ⟨eqv⟩ := heq
  set R1 := LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁) with hR1
  let K := kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0
  let q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0 := Submodule.mkQ _
  have hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j),
      z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0 := fun φ z hz => by
    rw [LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0 := fun φ hφ y =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)
  have hσmem : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) ∈ R1 := by
    intro φ l a
    have h := hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    rw [map_sigRel, sub_smul, one_smul, sub_eq_zero] at h
    exact ⟨_, by rw [DistribSMul.toLinearMap_apply]; exact h.symm⟩
  have hσ0 : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    rw [map_sig0Rel, sub_smul, hδ, hE, sub_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hg : ∀ φ ∈ K, ∀ l (g : D l), colDO (O := O) r χ (D l) (φ (q (fNu l))) g =
      ∑ a, Kc l a g • (δO • φ (q (fSig l a))) := by
    intro φ hφ l g
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, g.2, rfl⟩))
    rw [map_colGenJ] at h
    obtain ⟨b, hb⟩ := hk0 l g
    simp only [LinearMap.comp_apply, hKY φ hφ, zero_add, hb, neg_smul, mul_smul, hE, smul_zero,
      neg_zero, add_zero, hδ, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at h
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) - φ (q (fNu l)) = _
    rw [sub_smul, one_smul] at h
    rw [h]
    exact Finset.sum_congr rfl fun a _ => (smul_comm _ _ _).symm
  have hlift' : ∀ φ ∈ K, ∀ l a, ((ℓ : O) ^ e' l) • (δO • φ (q (fSig l a))) = 0 := by
    intro φ hφ l a
    exact hlift l (fun a => δO • φ (q (fSig l a))) (fun a => R1.smul_mem δO (hσmem φ l a))
      ⟨φ (q (fNu l)), funext fun g => hg φ hφ l g⟩ a
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let sR : ∀ l (a : Fin (j l)), K →ₗ[O] R1 := fun l a =>
    LinearMap.codRestrict R1 (evK (q (fSig l a))) (fun φ => hσmem φ.1 l a)
  have hsk : ∀ l a (φ : K), eqv (sR l a φ) ∈
      LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' l * δO)) := by
    intro l a φ
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← map_smul]
    have : ((ℓ : O) ^ e' l * δO) • sR l a φ = 0 := Subtype.ext (by
      rw [Submodule.coe_smul, mul_smul, Submodule.coe_zero]
      exact hlift' φ.1 φ.2 l a)
    rw [this, map_zero]
  let sK : ∀ l (a : Fin (j l)), K →ₗ[O]
      LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' l * δO)) := fun l a =>
    LinearMap.codRestrict _ (eqv.toLinearMap ∘ₗ sR l a) (hsk l a)
  let s0K : ∀ l, K →ₗ[O] LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := fun l =>
    LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 l)
  let Φ : K →ₗ[O] ((l : ι) → ColData O ℓ δO (e' l) (j l) Unit d) :=
    LinearMap.pi fun l => (LinearMap.pi fun a => sK l a).prod ((0 : K →ₗ[O] Unit).prod (s0K l))
  have hΦ0 : ∀ φ : K, Φ φ = 0 →
      (∀ l a, φ.1 (q (fSig l a)) = 0) ∧ (∀ l, φ.1 (q (fSig0 l)) = 0) := by
    intro φ h
    refine ⟨fun l a => ?_, fun l => ?_⟩
    · have h1 : sK l a φ = 0 := congrFun (congrArg Prod.fst (congrFun h l)) a
      have h2 : sR l a φ = 0 := eqv.map_eq_zero_iff.mp (congrArg Subtype.val h1)
      exact congrArg Subtype.val h2
    · have h1 : s0K l φ = 0 := congrArg Prod.snd (congrArg Prod.snd (congrFun h l))
      exact congrArg Subtype.val h1
  have hΘmem : ∀ l (φ : LinearMap.ker Φ), evK (q (fNu l)) φ.1 ∈
      LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) := by
    intro l φ
    obtain ⟨hs, _⟩ := hΦ0 φ.1 (LinearMap.mem_ker.mp φ.2)
    rw [LinearMap.mem_ker]
    funext g
    show colDO (O := O) r χ (D l) (φ.1.1 (q (fNu l))) g = 0
    rw [hg φ.1.1 φ.1.2 l g]
    simp [hs]
  let Θ : LinearMap.ker Φ →ₗ[O]
      ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) :=
    LinearMap.pi fun l =>
      LinearMap.codRestrict _ (evK (q (fNu l)) ∘ₗ (LinearMap.ker Φ).subtype) (hΘmem l)
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have hν : ∀ l, φ.1.1 (q (fNu l)) = 0 := fun l => congrArg Subtype.val (congrFun h l)
    obtain ⟨hs, hs0⟩ := hΦ0 φ.1 (LinearMap.mem_ker.mp φ.2)
    have : φ.1.1 = 0 := eq_zero_of_gens φ.1.1 (hKY φ.1.1 φ.1.2) hν hs hs0
    exact Subtype.ext (Subtype.ext this)
  have h1 : Module.length O (LinearMap.ker Φ) ≤
      ∑ l, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) :=
    (Module.length_le_of_injective Θ hΘ).trans_eq (Module.length_pi_of_fintype O _)
  have h2 : Module.length O (LinearMap.range Φ) ≤
      ∑ l, (((j l : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          IsDiscreteValuationRing.addVal O δO) + 0) +
        (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) :=
    calc Module.length O (LinearMap.range Φ)
        ≤ Module.length O ((l : ι) → ColData O ℓ δO (e' l) (j l) Unit d) :=
          Module.length_le_of_injective (LinearMap.range Φ).subtype Subtype.val_injective
      _ = ∑ l, Module.length O (ColData O ℓ δO (e' l) (j l) Unit d) :=
          Module.length_pi_of_fintype O _
      _ ≤ _ := Finset.sum_le_sum fun l _ =>
          KernelLengthBounds.length_colData_le ℓ δO (e' l) (j l) Unit d 0 (by rw [Module.length_eq_zero])
  rw [IdempotentNormalFormsRhoFacts.length_eq_ker_add_range Φ]
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by
      simp only [add_zero, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
end Formalism.NG
