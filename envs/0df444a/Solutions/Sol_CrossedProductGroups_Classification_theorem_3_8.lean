-- Prove2me | solution 1 for CrossedProductGroups.Classification.theorem_3_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:04:23.176761+00:00
-- url     : https://prove2.me/submissions/a8b2be5d-0b17-4749-b9b9-8c1f2f6e9c38

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

open CategoryTheory

open CrossedProductGroups.Classification

/-
The foundation below is the actual accepted proof of iso_iff_equiv2 by Ethan Cheung,
submission 9c5a2a87-3dc5-438c-9026-1039ff510e93. Its entrypoint alone is renamed.
-/
namespace CPG34Aux

variable {H G : Type*} [Group H] [Group G]

lemma alpha_one (c : E2 H G) (h : H) : c.1.1 1 h = h := by
  have := c.2.1.twisted 1 1 h
  rw [c.2.2, one_mul, one_mul, inv_one, mul_one] at this
  exact (c.1.1 1).injective this

lemma f_one_left (c : E2 H G) (g : G) : c.1.2 1 g = 1 := by
  have := c.2.1.cocycle 1 1 g
  rw [c.2.2, one_mul, one_mul, alpha_one, one_mul] at this
  exact (mul_eq_left.mp this.symm)

lemma f_one_right (c : E2 H G) (g : G) : c.1.2 g 1 = 1 := by
  have := c.2.1.cocycle g 1 1
  rw [c.2.2, mul_one, mul_one, map_one, one_mul] at this
  exact mul_eq_right.mp this

theorem prop34 {H G : Type*} [Group H] [Group G] (c c' : E2 H G)
    (η : H →* H) (γ : G →* G) (ψ : H × G → H × G) :
    (∃ m : E2Hom c c', m.η = η ∧ m.γ = γ ∧ m.ψ = ψ) ↔
      ∃! r : G → H,
        (∀ g : G, ∀ h : H, η (c.1.1 g h) * r g = r g * c'.1.1 (γ g) (η h)) ∧
        (∀ g₁ g₂ : G, r g₁ * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) =
          η (c.1.2 g₁ g₂) * r (g₁ * g₂)) ∧
        ∀ h : H, ∀ g : G, ψ (h, g) = (η h * r g, γ g) := by
  constructor
  · rintro ⟨m, rfl, rfl, rfl⟩
    have hform : ∀ h g, m.ψ (h, g) = (m.η h * (m.ψ (1, g)).1, m.γ g) := by
      intro h g
      have hx : ((h, g) : H × G) = crossedMul c.1.1 c.1.2 (h, 1) (1, g) := by
        simp [crossedMul, alpha_one, f_one_left]
      rw [hx, m.map_mul, m.comm_inl]
      have h2 := m.comm_snd (1, g)
      simp only [crossedMul, alpha_one, f_one_left, one_mul]
      rw [h2]
      simp [alpha_one, f_one_left]
    refine ⟨fun g => (m.ψ (1, g)).1, ⟨?_, ?_, hform⟩, ?_⟩
    · intro g h
      have e := m.map_mul (1, g) (h, 1)
      have hl : crossedMul c.1.1 c.1.2 (1, g) (h, 1) = (c.1.1 g h, g) := by
        simp [crossedMul, f_one_right]
      rw [hl, hform, hform 1 g, m.comm_inl] at e
      have e1 := congrArg Prod.fst e
      simp only [crossedMul, map_one, one_mul, f_one_right] at e1
      simpa [f_one_right] using e1
    · intro g₁ g₂
      have e := m.map_mul (1, g₁) (1, g₂)
      have hl : crossedMul c.1.1 c.1.2 (1, g₁) (1, g₂) = (c.1.2 g₁ g₂, g₁ * g₂) := by
        simp [crossedMul]
      rw [hl, hform, hform 1 g₁, hform 1 g₂] at e
      have e1 := congrArg Prod.fst e
      simp only [crossedMul, map_one, one_mul] at e1
      exact e1.symm
    · rintro r ⟨_, _, hr⟩
      funext g
      rw [hr 1 g]; simp
  · rintro ⟨r, ⟨h1, h2, h3⟩, -⟩
    have hr1 : r 1 = 1 := by
      have := h2 1 1
      rw [map_one, alpha_one, c'.2.2, c.2.2, map_one, mul_one, one_mul, mul_one] at this
      exact mul_eq_right.mp this
    have hψ : ψ = fun x => (η x.1 * r x.2, γ x.2) := by
      funext x; exact h3 x.1 x.2
    subst hψ
    refine ⟨⟨η, γ, fun x => (η x.1 * r x.2, γ x.2), ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
    · rintro ⟨a₁, g₁⟩ ⟨a₂, g₂⟩
      simp only [crossedMul, map_mul, Prod.mk.injEq, and_true]
      have k1 := h1 g₁ a₂
      have k2 := h2 g₁ g₂
      calc η a₁ * η (c.1.1 g₁ a₂) * η (c.1.2 g₁ g₂) * r (g₁ * g₂)
          = η a₁ * η (c.1.1 g₁ a₂) * (η (c.1.2 g₁ g₂) * r (g₁ * g₂)) := by group
        _ = η a₁ * (η (c.1.1 g₁ a₂) * r g₁) * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) := by
            rw [← k2]; group
        _ = η a₁ * r g₁ * (c'.1.1 (γ g₁) (η a₂) * c'.1.1 (γ g₁) (r g₂)) *
              c'.1.2 (γ g₁) (γ g₂) := by rw [k1]; group
        _ = _ := by rw [← map_mul]
    · intro h; simp [hr1]
    · intro x; rfl

lemma exists_hom (c c' : E2 H G) (η : H →* H) (γ : G →* G) (r : G → H)
    (C1 : ∀ g : G, ∀ h : H, η (c.1.1 g h) * r g = r g * c'.1.1 (γ g) (η h))
    (C2 : ∀ g₁ g₂ : G, r g₁ * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) =
          η (c.1.2 g₁ g₂) * r (g₁ * g₂)) :
    ∃ m : E2Hom c c', m.η = η ∧ m.γ = γ ∧ m.ψ = fun x => (η x.1 * r x.2, γ x.2) := by
  refine (prop34 c c' η γ _).mpr ⟨r, ⟨C1, C2, fun h g => rfl⟩, ?_⟩
  rintro r' ⟨-, -, h3⟩
  funext g
  have := congrArg Prod.fst (h3 1 g)
  simpa using this.symm

def invHom {c c' : E2 H G} (m : E2Hom c c') (eη : H ≃* H) (eγ : G ≃* G) (eψ : H × G ≃ H × G)
    (hη : ∀ x, eη x = m.η x) (hγ : ∀ x, eγ x = m.γ x) (hψ : ∀ x, eψ x = m.ψ x) :
    E2Hom c' c where
  η := eη.symm.toMonoidHom
  γ := eγ.symm.toMonoidHom
  ψ := eψ.symm
  map_mul := by
    intro x y
    apply eψ.injective
    rw [Equiv.apply_symm_apply, hψ, m.map_mul, ← hψ, ← hψ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  comm_inl := by
    intro h
    rw [Equiv.symm_apply_eq, hψ, m.comm_inl, ← hη]
    simp
  comm_snd := by
    intro x
    have := m.comm_snd (eψ.symm x)
    rw [← hψ, Equiv.apply_symm_apply, ← hγ] at this
    rw [this]; simp

end CPG34Aux

open CPG34Aux

theorem iso_iff_equiv2_proof (H G : Type*) [Group H] [Group G] :
    (∀ c c' : E2 H G, Nonempty (c ≅ c') ↔ Equiv2 c c') ∧
      Equivalence (Equiv2 (H := H) (G := G)) := by
  have part1 : ∀ c c' : E2 H G, Nonempty (c ≅ c') ↔ Equiv2 c c' := by
    intro c c'
    constructor
    · rintro ⟨e⟩
      let m : E2Hom c c' := e.hom
      let mi : E2Hom c' c := e.inv
      have h1 : E2Hom.comp m mi = E2Hom.id c := e.hom_inv_id
      have h2 : E2Hom.comp mi m = E2Hom.id c' := e.inv_hom_id
      have hη1 := congrArg E2Hom.η h1
      have hη2 := congrArg E2Hom.η h2
      have hγ1 := congrArg E2Hom.γ h1
      have hγ2 := congrArg E2Hom.γ h2
      let eη : H ≃* H := MonoidHom.toMulEquiv m.η mi.η hη1 hη2
      let eγ : G ≃* G := MonoidHom.toMulEquiv m.γ mi.γ hγ1 hγ2
      obtain ⟨r, ⟨C1, C2, -⟩, -⟩ := (prop34 c c' m.η m.γ m.ψ).mp ⟨m, rfl, rfl, rfl⟩
      have C1' : ∀ g h, eη (c.1.1 g h) * r g = r g * c'.1.1 (eγ g) (eη h) := C1
      have C2' : ∀ a b, r a * c'.1.1 (eγ a) (r b) * c'.1.2 (eγ a) (eγ b) =
          eη (c.1.2 a b) * r (a * b) := C2
      refine ⟨eη, eγ, fun g => eη.symm (r (eγ.symm g))⁻¹, ?_, ?_⟩
      · intro g h
        obtain ⟨g0, rfl⟩ := eγ.surjective g
        obtain ⟨h0, rfl⟩ := eη.surjective h
        simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
        have : c'.1.1 (eγ g0) (eη h0) = (r g0)⁻¹ * (eη (c.1.1 g0 h0) * r g0) := by
          rw [C1']; group
        rw [this]; group
      · intro g1 g2
        obtain ⟨a, rfl⟩ := eγ.surjective g1
        obtain ⟨b, rfl⟩ := eγ.surjective g2
        rw [← map_mul eγ]
        simp only [MulEquiv.symm_apply_apply]
        have hA : eη (c.1.1 a (eη.symm (r b))) =
            r a * c'.1.1 (eγ a) (r b) * (r a)⁻¹ := by
          have := C1' a (eη.symm (r b))
          rw [MulEquiv.apply_symm_apply] at this
          exact eq_mul_inv_of_mul_eq this
        have hF : eη (c.1.2 a b) = r a * c'.1.1 (eγ a) (r b) * c'.1.2 (eγ a) (eγ b) *
            (r (a * b))⁻¹ := eq_mul_inv_of_mul_eq (C2' a b).symm
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hA, hF]
        group
    · rintro ⟨eη, eγ, t, h38, h39⟩
      set r : G → H := fun g => (eη (t (eγ g)))⁻¹ with hr
      have C1 : ∀ g h, eη.toMonoidHom (c.1.1 g h) * r g =
          r g * c'.1.1 (eγ.toMonoidHom g) (eη.toMonoidHom h) := by
        intro g h
        simp only [MulEquiv.coe_toMonoidHom, hr, h38, MulEquiv.symm_apply_apply, map_mul,
          map_inv]
        group
      have C2 : ∀ a b, r a * c'.1.1 (eγ.toMonoidHom a) (r b) *
          c'.1.2 (eγ.toMonoidHom a) (eγ.toMonoidHom b) =
          eη.toMonoidHom (c.1.2 a b) * r (a * b) := by
        intro a b
        simp only [MulEquiv.coe_toMonoidHom, hr, h38, h39, MulEquiv.symm_apply_apply, map_mul,
          map_inv, MulEquiv.apply_symm_apply]
        group
      obtain ⟨m, hmη, hmγ, hmψ⟩ := exists_hom c c' eη.toMonoidHom eγ.toMonoidHom r C1 C2
      let eψ : H × G ≃ H × G :=
        { toFun := fun x => (eη x.1 * r x.2, eγ x.2)
          invFun := fun y => (eη.symm (y.1 * (r (eγ.symm y.2))⁻¹), eγ.symm y.2)
          left_inv := by intro x; simp
          right_inv := by intro y; simp }
      have hη : ∀ x, eη x = m.η x := by intro x; rw [hmη]; rfl
      have hγ : ∀ x, eγ x = m.γ x := by intro x; rw [hmγ]; rfl
      have hψ : ∀ x, eψ x = m.ψ x := by intro x; rw [hmψ]; rfl
      let mi := invHom m eη eγ eψ hη hγ hψ
      refine ⟨{ hom := m, inv := mi, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
      · show E2Hom.comp m mi = E2Hom.id c
        apply E2Hom.ext
        · ext x; show eη.symm (m.η x) = x; rw [← hη]; simp
        · ext x; show eγ.symm (m.γ x) = x; rw [← hγ]; simp
        · funext x; show eψ.symm (m.ψ x) = x; rw [← hψ]; simp
      · show E2Hom.comp mi m = E2Hom.id c'
        apply E2Hom.ext
        · ext x; show m.η (eη.symm x) = x; rw [← hη]; simp
        · ext x; show m.γ (eγ.symm x) = x; rw [← hγ]; simp
        · funext x; show m.ψ (eψ.symm x) = x; rw [← hψ]; simp
  refine ⟨part1, ⟨fun c => (part1 c c).mp ⟨@Iso.refl (E2 H G) _ c⟩, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩⟩
  · obtain ⟨e⟩ := (part1 x y).mpr h
    exact (part1 y x).mp ⟨e.symm⟩
  · obtain ⟨e1⟩ := (part1 x y).mpr h1
    obtain ⟨e2⟩ := (part1 y z).mpr h2
    exact (part1 x z).mp ⟨e1 ≪≫ e2⟩

/-- The classification map sends each isomorphism class to its 2-equivalence class. -/
theorem solution (H G : Type*) [Group H] [Group G] :
    Equivalence (Equiv2 (H := H) (G := G)) ∧
      ∃ e : CategoryTheory.Skeleton (E2 H G) ≃ Quot (Equiv2 (H := H) (G := G)),
        ∀ c : Crossed H G,
          e (CategoryTheory.toSkeleton (C := E2 H G) c) = Quot.mk _ c := by
  obtain ⟨hiso, hequiv⟩ := iso_iff_equiv2_proof H G
  exact ⟨hequiv, Quot.congrRight hiso, fun _ => rfl⟩
