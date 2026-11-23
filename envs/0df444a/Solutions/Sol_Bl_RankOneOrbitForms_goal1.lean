-- Prove2me | solution 1 for Bl.RankOneOrbitForms.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:25.055796+00:00
-- url     : https://prove2.me/submissions/1edd9286-7e60-4b80-8bd9-b8f98d9ded18

import Mathlib
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField
namespace Bl.RankOneOrbitForms
variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
private lemma rank_one_form (f : T →ₗ[K] T) (h1 : finrank K (LinearMap.range f) = 1) :
    ∃ (φ : T →ₗ[K] K) (v : T), v ≠ 0 ∧ φ ≠ 0 ∧ f = φ.smulRight v := by
  obtain ⟨v, hv, hw⟩ := finrank_eq_one_iff'.mp h1
  choose a ha using fun x => hw ⟨f x, LinearMap.mem_range_self f x⟩
  have hv' : (v : T) ≠ 0 := fun h => hv (Subtype.ext h)
  have hav : ∀ x, a x • (v : T) = f x := fun x => congrArg Subtype.val (ha x)
  have inj := smul_left_injective K hv'
  let φ : T →ₗ[K] K :=
    { toFun := a
      map_add' := fun x y => inj (by simp only [add_smul, hav, map_add])
      map_smul' := fun c x => inj (by
        simp only [smul_eq_mul, mul_smul, hav, map_smul, RingHom.id_apply]) }
  refine ⟨φ, v, hv', ?_, ?_⟩
  · intro h0
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp v.2
    apply hv'
    rw [← hy, ← hav y]
    have : a y = 0 := LinearMap.congr_fun h0 y
    rw [this, zero_smul]
  · ext x
    simp only [LinearMap.smulRight_apply]
    exact (hav x).symm
private lemma span_orbit (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : T) (hv : v ≠ 0) : Submodule.span K (Set.range fun g => τ g v) = ⊤ := by
  have hinvar : ∀ g : G, ∀ w ∈ Submodule.span K (Set.range fun g => τ g v),
      τ g w ∈ Submodule.span K (Set.range fun g => τ g v) := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show τ (g * h) v = τ g (τ h v); rw [map_mul]; rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  rcases hirr _ hinvar with h | h
  · exfalso
    apply hv
    have : τ 1 v ∈ Submodule.span K (Set.range fun g => τ g v) := Submodule.subset_span ⟨1, rfl⟩
    rw [h, Submodule.mem_bot, map_one, Module.End.one_apply] at this
    exact this
  · exact h
private lemma orbit_ker (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (φ : T →ₗ[K] K) (hφ : φ ≠ 0) (x : T) (hx : ∀ g, φ (τ g x) = 0) : x = 0 := by
  let W : Submodule K T := ⨅ g : G, LinearMap.ker (φ ∘ₗ τ g)
  have memW : ∀ y, y ∈ W ↔ ∀ g, φ (τ g y) = 0 := by
    intro y
    simp [W, Submodule.mem_iInf]
  have hinvar : ∀ g : G, ∀ w ∈ W, τ g w ∈ W := by
    intro g w hw
    rw [memW] at hw ⊢
    intro h
    have := hw (h * g)
    rwa [map_mul, Module.End.mul_apply] at this
  rcases hirr W hinvar with h | h
  · have : x ∈ W := (memW x).2 hx
    rw [h, Submodule.mem_bot] at this
    exact this
  · exfalso
    apply hφ
    ext y
    have hy : y ∈ W := h ▸ Submodule.mem_top
    have := (memW y).1 hy 1
    simpa using this
private lemma select {ι M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : ι → M) (r : ℕ) (hr : finrank K (Submodule.span K (Set.range f)) = r) :
    ∃ s : Fin r → ι, LinearIndependent K (f ∘ s) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K f
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hsp, hr]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩
end Bl.RankOneOrbitForms
end

set_option autoImplicit false
open Module NumberField
open Bl Bl.RankOneOrbitForms
variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
namespace Bl.RankOneOrbitForms
theorem _root_.solution (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  obtain ⟨φ, v, hv, hφ, rfl⟩ := rank_one_form ε₀ h1
  have hspanT := span_orbit τ hirr v hv
  have hspanR : Submodule.span K (Set.range fun g => ε (τ g v)) = LinearMap.range ε := by
    have : (Set.range fun g => ε (τ g v)) = ε '' (Set.range fun g => τ g v) := by
      ext y; simp
    rw [this, ← Submodule.map_span, hspanT, Submodule.map_top]
  obtain ⟨γ, hγ⟩ := select (fun g => ε (τ g v)) (finrank K (LinearMap.range ε)) (by rw [hspanR])
  have hle : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) ≤ LinearMap.range ε := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_range_self _ _
  have hueq : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) = LinearMap.range ε :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hγ, Fintype.card_fin])
  let w : G → Fin (finrank K (LinearMap.range ε)) → K := fun g j => φ (τ g (ε (τ (γ j) v)))
  have hw : Submodule.span K (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle'⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hℓ
    let b : Fin (finrank K (LinearMap.range ε)) → K := fun j => ℓ (fun k => if j = k then 1 else 0)
    have key : ∀ g, ∑ j, w g j • b j = 0 := by
      intro g
      have := hle' (Submodule.subset_span ⟨g, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      exact this
    have hx : ∑ j, b j • ε (τ (γ j) v) = 0 := by
      apply orbit_ker τ hirr φ hφ
      intro g
      simp only [map_sum, map_smul, smul_eq_mul]
      have := key g
      simp only [w, smul_eq_mul] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hz := Fintype.linearIndependent_iff.mp hγ b hx
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by
      have : ℓ (fun k => if j = k then 1 else 0) = 0 := hz j
      rw [this, smul_zero]
  obtain ⟨δ, hδ⟩ := select w (finrank K (LinearMap.range ε))
    (by rw [hw, finrank_top, Module.finrank_fin_fun])
  let c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K :=
    Matrix.of fun i j => φ (τ (δ i) (ε (τ (γ j) v)))
  have hc : IsUnit c := Matrix.linearIndependent_rows_iff_isUnit.mp hδ
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).mp hc
  refine ⟨γ, δ, c, hcd.ne_zero, ?_, ?_, ?_⟩
  · intro i j
    rw [show (φ.smulRight v) ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)
        = (φ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)).smulRight v from LinearMap.ext fun _ => rfl,
      LinearMap.trace_smulRight]
    rfl
  · intro i j
    ext x
    simp [c, smul_smul, mul_comm]
  · ext x
    have hx : ε x ∈ Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) :=
      by rw [hueq]; exact LinearMap.mem_range_self ε x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    simp only [Function.comp_apply] at ha
    have hcoef : ∀ i, φ (τ (δ i) (ε x)) = ∑ k, c i k * a k := by
      intro i
      rw [← ha]
      simp [c, map_sum, map_smul, mul_comm]
    have hinv : ∀ j, ∑ i, c⁻¹ j i * ∑ k, c i k * a k = a j := by
      intro j
      have := congrFun (show Matrix.mulVec c⁻¹ (Matrix.mulVec c a) = a by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcd, Matrix.one_mulVec]) j
      simpa [Matrix.mulVec, dotProduct] using this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_smul, hcoef]
    rw [← ha]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hinv j, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
end Bl.RankOneOrbitForms
