-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.point_count_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:28.265334+00:00
-- url     : https://prove2.me/submissions/3bb6247c-c56f-4acb-ad3b-70e98fdf1cbd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
section Count
variable {F : Type} [Field F]
private lemma dot_product_dual_apply (m : ℕ) (a b : Fin m → F) : dotProductDual m a b = a ⬝ᵥ b := rfl
private lemma dot_product_dual_surjective (m : ℕ) : Function.Surjective (dotProductDual (F := F) m) := by
  intro φ
  refine ⟨fun i => φ (Pi.single i 1), ?_⟩
  ext i
  simp [dot_product_dual_apply]
private lemma functional_with_scalar_apply {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (c : F) (v : Fin n → F) (s : F) :
    functionalWithScalar fL c (v, s) = fL v + c * s := by
  simp [functionalWithScalar]
private lemma level_set_eq_ker_functional {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (he : fL e = 1) (c : F) :
    Uc fL e c = LinearMap.ker (functionalWithScalar fL c) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨l, hl, rfl⟩
      have hl' : fL l = 0 := hl
      simp [LinearMap.mem_ker, functional_with_scalar_apply, hl']
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, functional_with_scalar_apply]
      simp [he]
  · rintro ⟨v, s⟩ h
    rw [LinearMap.mem_ker, functional_with_scalar_apply] at h
    have h1 : ((v, s) : (Fin n → F) × F) =
        LinearMap.inl F (Fin n → F) F (v + (c * s) • e) + s • ((-c) • e, (1 : F)) := by
      ext
      · simp [smul_smul]; ring
      · simp
    rw [h1]
    refine Submodule.add_mem_sup (Submodule.mem_map_of_mem ?_)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    simp [LinearMap.mem_ker, he, h]
private lemma condition_iff_dual_eq_functional {n m : ℕ} (fL : (Fin n → F) →ₗ[F] F) (e : Fin n → F) (he : fL e = 1)
    (x' : ((Fin n → F) × F) →ₗ[F] (Fin m → F)) (c : F) (fW : Fin m → F) :
    ((∀ l ∈ LinearMap.ker fL, fW ⬝ᵥ x' (l, 0) = 0) ∧ fW ⬝ᵥ x' (e, 0) = 1 ∧ fW ⬝ᵥ x' (0, 1) = c) ↔
      (x'.dualMap ∘ₗ dotProductDual m) fW = functionalWithScalar fL c := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    apply LinearMap.ext
    rintro ⟨v, s⟩
    have hd : ((v, s) : (Fin n → F) × F) =
        (v - fL v • e, 0) + fL v • (e, (0 : F)) + s • ((0 : Fin n → F), (1 : F)) := by
      ext <;> simp
    have hk : v - fL v • e ∈ LinearMap.ker fL := by simp [LinearMap.mem_ker, he]
    have := h1 _ hk
    rw [functional_with_scalar_apply]
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, dot_product_dual_apply]
    rw [hd, map_add, map_add, map_smul, map_smul, dotProduct_add, dotProduct_add,
      dotProduct_smul, dotProduct_smul, this, h2, h3]
    simp [mul_comm]
  · intro h
    have h' : ∀ v s, fW ⬝ᵥ x' (v, s) = fL v + c * s := by
      intro v s
      rw [← functional_with_scalar_apply, ← h]
      rfl
    refine ⟨fun l hl => ?_, ?_, ?_⟩
    · have hl' : fL l = 0 := hl
      rw [h', hl']; simp
    · rw [h', he]; simp
    · rw [h']; simp
variable [Fintype F]
private lemma card_fibre_linear_map {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Module.Finite F V] (T : V →ₗ[F] W) (w : W) (hw : w ∈ LinearMap.range T) :
    Nat.card {v : V // T v = w} = Fintype.card F ^ Module.finrank F (LinearMap.ker T) := by
  obtain ⟨v0, rfl⟩ := hw
  rw [← Nat.card_eq_fintype_card, ← Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker T)]
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1 - v0, by simp [LinearMap.mem_ker, v.2]⟩
      invFun := fun u => ⟨u.1 + v0, by
        have : T u.1 = 0 := u.2
        simp [this]⟩
      left_inv := fun v => by simp
      right_inv := fun u => by simp }
private lemma finrank_ker_dual_composition {n g : ℕ} (hg : 1 ≤ g)
    (x' : ((Fin n → F) × F) →ₗ[F] (Fin (n + g) → F)) :
    Module.finrank F (LinearMap.ker (x'.dualMap ∘ₗ dotProductDual (n + g))) =
      g - 1 + Module.finrank F (LinearMap.ker x') := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (x'.dualMap ∘ₗ dotProductDual (F := F) (n + g))
  have h2 := LinearMap.finrank_range_add_finrank_ker x'
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)),
    LinearMap.finrank_range_dualMap_eq_finrank_range] at h1
  simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at h1 h2
  omega
end Count
section FJ
variable {F : Type} [Field F] [Fintype F]
end FJ
section Onto
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
section FFOnto
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
end FFOnto
end Onto
end Formalism.HermitianLattices.LocalLatticeBases
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
variable {F : Type} [Field F]
variable [Fintype F]
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : KernelDimensionCount := by
  intro F _ _ n g hg fL e he x' c
  have hq : (1 : ℤ) ≤ (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  set T := x'.dualMap ∘ₗ dotProductDual (F := F) (n + g) with hT
  have hcount : fjCount fL e x' c = Nat.card {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c} := by
    unfold fjCount
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun fW => condition_iff_dual_eq_functional fL e he x' c fW))
  have hrange : LinearMap.range T = (LinearMap.ker x').dualAnnihilator := by
    rw [hT, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 (dot_product_dual_surjective _)),
      LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [hcount, level_set_eq_ker_functional fL e he c]
  by_cases hle : LinearMap.ker x' ≤ LinearMap.ker (functionalWithScalar fL c)
  · have hmem : functionalWithScalar fL c ∈ LinearMap.range T := by
      rw [hrange, Submodule.mem_dualAnnihilator]
      exact fun w hw => hle hw
    rw [card_fibre_linear_map T _ hmem, finrank_ker_dual_composition hg, inf_eq_right.2 hle]
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  · have hemp : IsEmpty {fW : Fin (n + g) → F // T fW = functionalWithScalar fL c} := by
      refine ⟨fun ⟨fW, h⟩ => hle ?_⟩
      have : functionalWithScalar fL c ∈ LinearMap.range T := ⟨fW, h⟩
      rw [hrange, Submodule.mem_dualAnnihilator] at this
      exact fun w hw => this w hw
    rw [Nat.card_of_isEmpty]
    set R := (functionalWithScalar fL c).domRestrict (LinearMap.ker x') with hR
    have hRne : R ≠ 0 := by
      intro h0
      apply hle
      intro w hw
      have := LinearMap.congr_fun h0 ⟨w, hw⟩
      simpa [hR] using this
    have hsurj : LinearMap.range R = ⊤ := LinearMap.range_eq_top.2 (LinearMap.surjective hRne)
    have h3 := LinearMap.finrank_range_add_finrank_ker R
    rw [hsurj, finrank_top, Module.finrank_self] at h3
    have h4 : Module.finrank F (LinearMap.ker R) =
        Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F)) := by
      rw [hR, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
        Submodule.map_comap_subtype, inf_comm]
    have h5 : g + Module.finrank F (LinearMap.ker (functionalWithScalar fL c) ⊓ LinearMap.ker x' :
          Submodule F ((Fin n → F) × F)) = g - 1 + Module.finrank F (LinearMap.ker x') := by
      omega
    rw [h5]
    simp
end Formalism.HermitianLattices.LocalLatticeBases
