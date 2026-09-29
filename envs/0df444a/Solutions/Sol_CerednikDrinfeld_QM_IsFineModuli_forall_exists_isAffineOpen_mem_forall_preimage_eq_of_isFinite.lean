-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7eb6802b-888c-56d1-b68e-44742ff30b53

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (hsep : IsSeparated fM) (hfin : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (ℓ : HeckeTower.AwayPrime r rbar)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (πℓ : Mℓ ⟶ M) (hπℓf : πℓ ≫ fM = fMℓ) [IsFinite πℓ]
    (hG : Finite G)
    (ρℓ : G →* Aut Mℓ) (hρℓf : ∀ h : G, (ρℓ h).hom ≫ fMℓ = fMℓ)
    (hρℓπ : ∀ h : G, (ρℓ h).hom ≫ πℓ = πℓ ≫ (ρ h).hom) :
    ∀ x : Mℓ, ∃ U : Mℓ.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ h : G, (ρℓ h).hom ⁻¹ᵁ U = U := by
  classical
  intro x
  haveI : Fintype G := Fintype.ofFinite G
  haveI : IsSeparated fM := hsep

  haveI : IsAffineHom (pullback.diagonal fM) := inferInstance
  have hinf : ∀ V₁ V₂ : M.Opens, IsAffineOpen V₁ → IsAffineOpen V₂ → IsAffineOpen (V₁ ⊓ V₂) := fun V₁ V₂ h₁ h₂ =>
    (isAffineHom_diagonal_iff (f := fM)).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂ (by simp) h₁ h₂

  have hρmul : ∀ h h' : G, (ρ h).hom ≫ (ρ h').hom = (ρ (h' * h)).hom := by
    intro h h'; rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom]
  have hρone : ∀ y : M, (ρ 1).hom.base y = y := by
    intro y; rw [map_one]; rfl

  obtain ⟨U₀, hU₀, hF⟩ := hfin (Finset.univ.image fun h : G => (ρ h).hom.base (πℓ.base x))
  have horb : ∀ h : G, (ρ h).hom.base (πℓ.base x) ∈ U₀ := fun h => hF _ (Finset.mem_image.2 ⟨h, Finset.mem_univ _, rfl⟩)

  let f : G → M.Opens := fun h => (ρ h).hom ⁻¹ᵁ U₀
  let U₁ : M.Opens := (Finset.univ : Finset G).inf f
  have hU₁le : ∀ h : G, U₁ ≤ (ρ h).hom ⁻¹ᵁ U₀ := fun h => Finset.inf_le (Finset.mem_univ h)
  have mem_U₁ : ∀ y : M, y ∈ U₁ ↔ ∀ h : G, (ρ h).hom.base y ∈ U₀ := by
    intro y
    constructor
    · intro hy h; exact hU₁le h hy
    · intro hy
      have gen : ∀ s : Finset G, y ∈ s.inf f := by
        intro s
        induction s using Finset.induction_on with
        | empty => rw [Finset.inf_empty]; exact TopologicalSpace.Opens.mem_top y
        | insert a s ha ih => rw [Finset.inf_insert]; exact (TopologicalSpace.Opens.mem_inf).2 ⟨hy a, ih⟩
      exact gen _
  have haff_aux : ∀ s : Finset G, IsAffineOpen (U₀ ⊓ s.inf f) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.inf_empty, inf_top_eq]; exact hU₀
    | insert a s ha ih =>
      rw [Finset.inf_insert, inf_left_comm, inf_comm]
      exact hinf _ _ ih (hU₀.preimage_of_isIso (ρ a).hom)
  have hU₁aff : IsAffineOpen U₁ := by
    have hle : U₁ ≤ U₀ := by
      intro y hy
      have := (mem_U₁ y).1 hy 1
      rwa [hρone] at this
    have : U₀ ⊓ U₁ = U₁ := inf_eq_right.2 hle
    rw [← this]
    exact haff_aux _

  refine ⟨πℓ ⁻¹ᵁ U₁, hU₁aff.preimage πℓ, ?_, ?_⟩
  · show πℓ.base x ∈ U₁
    exact (mem_U₁ _).2 horb
  · intro h
    ext y
    constructor
    · intro hy
      change πℓ.base y ∈ U₁
      have hy' : πℓ.base ((ρℓ h).hom.base y) ∈ U₁ := hy
      rw [← Scheme.Hom.comp_apply, hρℓπ h, Scheme.Hom.comp_apply] at hy'
      refine (mem_U₁ _).2 fun h' => ?_
      have := (mem_U₁ _).1 hy' (h' * h⁻¹)
      rw [← Scheme.Hom.comp_apply, hρmul, inv_mul_cancel_right] at this
      exact this
    · intro hy
      change πℓ.base ((ρℓ h).hom.base y) ∈ U₁
      rw [← Scheme.Hom.comp_apply, hρℓπ h, Scheme.Hom.comp_apply]
      refine (mem_U₁ _).2 fun h' => ?_
      rw [← Scheme.Hom.comp_apply, hρmul]
      exact (mem_U₁ _).1 hy (h' * h)

end S_CerednikDrinfeld_QM_IsFineModuli_forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_forall_exists_isAffineOpen_mem_forall_preimage_eq_of_isFinite (solution)
