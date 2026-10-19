-- Prove2me | solution 1 for BookProof.PermSector.good_swap0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:13:27.826894+00:00
-- url     : https://prove2.me/submissions/de4a9f48-25ba-44d7-873c-05f01cb656d6

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterTensorGraphCore
-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_swap0
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)
theorem h43_incl_tmul (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (n : ℕ) (a : E₂)
    (r : ((domSpace H E₂).pow n).carrier) :
    inclPow H E₂ (n + 1) (a ⊗ₜ[ℂ] r : ((domSpace H E₂).pow (n + 1)).carrier)
      = ((a : H.carrier) ⊗ₜ[ℂ] inclPow H E₂ n r : (H.pow (n + 1)).carrier) := rfl

theorem h43_der_tmul (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (n : ℕ) (a : E₂) (r : ((domSpace H E₂).pow n).carrier) :
    derPow H E₂ B (n + 1) (a ⊗ₜ[ℂ] r : ((domSpace H E₂).pow (n + 1)).carrier)
      = ((B a ⊗ₜ[ℂ] inclPow H E₂ n r : (H.pow (n + 1)).carrier)
        + ((a : H.carrier) ⊗ₜ[ℂ] derPow H E₂ B n r : (H.pow (n + 1)).carrier)) := rfl

theorem h43_good_refl (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (C : Submodule ℂ H.carrier) (n : ℕ) :
    Good H E₂ B C n (LinearIsometryEquiv.refl ℂ _) (LinearIsometryEquiv.refl ℂ _) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ ht => ht⟩

theorem h43_good_trans {H : IPSpace} {E₂ : Submodule ℂ H.carrier} {B : E₂ →ₗ[ℂ] H.carrier}
    {C : Submodule ℂ H.carrier} {n : ℕ} {uD vD : ((domSpace H E₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace H E₂).pow n).carrier}
    {uH vH : (H.pow n).carrier ≃ₗᵢ[ℂ] (H.pow n).carrier}
    (hu : Good H E₂ B C n uD uH) (hv : Good H E₂ B C n vD vH) :
    Good H E₂ B C n (uD.trans vD) (uH.trans vH) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t ht => hv.core _ (hu.core t ht)⟩
  · simp only [LinearIsometryEquiv.trans_apply]; rw [hv.incl, hu.incl]
  · simp only [LinearIsometryEquiv.trans_apply]; rw [hv.der, hu.der]

theorem h43_good_liftTail {H : IPSpace} {E₂ : Submodule ℂ H.carrier} {B : E₂ →ₗ[ℂ] H.carrier}
    {C : Submodule ℂ H.carrier} {n : ℕ} {uD : ((domSpace H E₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace H E₂).pow n).carrier}
    {uH : (H.pow n).carrier ≃ₗᵢ[ℂ] (H.pow n).carrier}
    (hu : Good H E₂ B C n uD uH) :
    Good H E₂ B C (n + 1) (liftTail (domSpace H E₂) uD) (liftTail H uH) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t ht => ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a r =>
      rw [liftTail_tmul, h43_incl_tmul, h43_incl_tmul, liftTail_tmul, hu.incl]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a r =>
      rw [liftTail_tmul, h43_der_tmul, h43_der_tmul, LinearIsometryEquiv.map_add, liftTail_tmul,
        liftTail_tmul, hu.incl, hu.der]
    | add x y hx hy => simp only [map_add, hx, hy]
  · change t ∈ Submodule.span ℂ _ at ht
    change _ ∈ Submodule.span ℂ _
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact Submodule.subset_span ⟨a, ha, uD b, hu.core b hb, rfl⟩
    | zero => rw [LinearIsometryEquiv.map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [LinearIsometryEquiv.map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearIsometryEquiv.map_smul]; exact Submodule.smul_mem _ c hx

theorem h43_good_swapFirst (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (C : Submodule ℂ H.carrier) (n : ℕ) :
    Good H E₂ B C (n + 2) (swapFirst (domSpace H E₂) n) (swapFirst H n) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t ht => ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a s =>
      induction s using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul b r =>
        rw [swapFirst_tmul, h43_incl_tmul, h43_incl_tmul, h43_incl_tmul, h43_incl_tmul,
          swapFirst_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a s =>
      induction s using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul b r =>
        rw [swapFirst_tmul, h43_der_tmul, h43_der_tmul, h43_der_tmul, h43_der_tmul,
          h43_incl_tmul, h43_incl_tmul]
        simp only [TensorProduct.tmul_add, map_add]
        rw [swapFirst_tmul, swapFirst_tmul, swapFirst_tmul]
        abel
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  · change t ∈ Submodule.span ℂ _ at ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, s, hs, rfl⟩ := hz
      change s ∈ Submodule.span ℂ _ at hs
      induction hs using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, hb, r, hr, rfl⟩ := hw
        rw [swapFirst_tmul]
        refine Submodule.subset_span ⟨b, hb, a ⊗ₜ[ℂ] r, ?_, rfl⟩
        exact Submodule.subset_span ⟨a, ha, r, hr, rfl⟩
      | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [TensorProduct.tmul_smul, map_smul]; exact Submodule.smul_mem _ c hx
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem h43_good_swap0 (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (C : Submodule ℂ H.carrier) : ∀ (n : ℕ) (p : Fin (n + 1)),
    Good H E₂ B C (n + 1) (swap0 (domSpace H E₂) (n + 1) p) (swap0 H (n + 1) p) := by
  intro n
  induction n with
  | zero => intro p; exact h43_good_refl H E₂ B C 1
  | succ n ih =>
    intro p
    refine Fin.cases ?_ ?_ p
    · exact h43_good_refl H E₂ B C (n + 2)
    · intro j
      rw [swap0_succ, swap0_succ]
      exact h43_good_trans (h43_good_liftTail (ih j))
        (h43_good_trans (h43_good_swapFirst H E₂ B C n) (h43_good_liftTail (ih j)))

theorem h43_good_permOp (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (C : Submodule ℂ H.carrier) : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    Good H E₂ B C n (permOp (domSpace H E₂) n σ) (permOp H n σ) := by
  intro n
  induction n with
  | zero => intro σ; exact h43_good_refl H E₂ B C 0
  | succ n ih =>
    intro σ
    exact h43_good_trans (h43_good_swap0 H E₂ B C n _) (h43_good_liftTail (ih _))

theorem h43_sectorOp_incl (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (n : ℕ) (t : ((domSpace H E₂).pow n).carrier) (h : inclPow H E₂ n t ∈ sectorDom H E₂ n) :
    sectorOp H E₂ B n ⟨inclPow H E₂ n t, h⟩ = derPow H E₂ B n t := by
  have e : (LinearEquiv.ofInjective (inclPow H E₂ n).toLinearMap (inclPow H E₂ n).injective).symm
      ⟨inclPow H E₂ n t, h⟩ = t := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  change derPow H E₂ B n ((LinearEquiv.ofInjective (inclPow H E₂ n).toLinearMap
    (inclPow H E₂ n).injective).symm ⟨inclPow H E₂ n t, h⟩) = _
  rw [e]

theorem h43_mem_sectorDom (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (n : ℕ)
    (t : ((domSpace H E₂).pow n).carrier) : inclPow H E₂ n t ∈ sectorDom H E₂ n := ⟨t, rfl⟩

theorem h43_sectorOp_permOp (H : IPSpace) (E₂ : Submodule ℂ H.carrier) (B : E₂ →ₗ[ℂ] H.carrier)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom H E₂ n)
    (h : permOp H n σ (x : (H.pow n).carrier) ∈ sectorDom H E₂ n) :
    sectorOp H E₂ B n ⟨permOp H n σ (x : (H.pow n).carrier), h⟩
      = permOp H n σ (sectorOp H E₂ B n x) := by
  obtain ⟨t, ht⟩ := x.2
  have hg := h43_good_permOp H E₂ B ⊥ n σ
  have hx : x = ⟨inclPow H E₂ n t, h43_mem_sectorDom H E₂ n t⟩ := Subtype.ext ht.symm
  have h1 : (⟨permOp H n σ (x : (H.pow n).carrier), h⟩ : sectorDom H E₂ n)
      = ⟨inclPow H E₂ n (permOp (domSpace H E₂) n σ t), h43_mem_sectorDom H E₂ n _⟩ := by
    apply Subtype.ext
    change permOp H n σ (x : (H.pow n).carrier) = inclPow H E₂ n (permOp (domSpace H E₂) n σ t)
    rw [hg.incl]; exact congrArg _ ht.symm
  rw [h1, hx, h43_sectorOp_incl, h43_sectorOp_incl, hg.der]

theorem solution : ∀ (n : ℕ) (p : Fin (n + 1)),
    Good Hs D₂ A D (n + 1) (swap0 (domSpace Hs D₂) (n + 1) p) (swap0 Hs (n + 1) p) := by
  exact h43_good_swap0 Hs D₂ A D

