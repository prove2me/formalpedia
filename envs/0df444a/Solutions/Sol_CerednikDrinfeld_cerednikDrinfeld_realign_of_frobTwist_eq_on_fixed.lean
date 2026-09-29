-- Prove2me | solution 1 for CerednikDrinfeld.cerednikDrinfeld_realign_of_frobTwist_eq_on_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/caf25441-9b4d-5e12-b43b-5f3b4f1fbf93

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Theorems.Thm_CerednikDrinfeld_dvd_of_forall_frobenius_zpow_apply_eq_of_fixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_cerednikDrinfeld_realign_of_frobTwist_eq_on_fixed

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

namespace CDRealign

open CerednikDrinfeld.FormalOmega LT.LatticeTree

theorem frobTwist_zero {𝒪 : Type} [CommRing 𝒪] (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : frobTwist Onr Fr 0 ψ = ψ := by
  ext y; simp [frobTwist]

theorem frobTwist_apply {𝒪 : Type} [CommRing 𝒪] (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (n : ℤ) (ψ : Onr →ₐ[𝒪] B) (y : Onr) :
    frobTwist Onr Fr n ψ y = ψ ((Fr ^ n) y) := rfl

theorem isPullback_scalarGL {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    (B : Type) [CommRing B] [Algebra 𝒪 B] (c : Kˣ) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B (scalarGL c) d d := by
  intro M
  rw [d.homothety c M, Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL c) M).injective]

theorem zpow_apply_eq_self {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (σ : A ≃ₐ[R] A) (y : A)
    (h : σ y = y) (n : ℤ) : (σ ^ n) y = y := by
  have hinv : σ⁻¹ y = y := by
    conv_lhs => rw [← h]
    exact σ.symm_apply_apply y
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, h, ih]
  | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]

end CDRealign

open CDRealign LT.LatticeTree in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)
    {a₁ b₁ : ℚ} (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁])
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (G : Type) [Group G] [Finite G] (θt : ↥Γt →* G)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k]
    (γ : ↥Γt × G) (ψ : Onr →ₐ[𝒪] k)
    (hceq : ∀ y : Onr,
      (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c₀ : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c₀ • (1 : ℍ[ℚ, a₁, b₁])) → θt ⟨z, hz⟩ = 1 →
        (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
      ψ y = (frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ)))) ψ) y) :
    ∃ z : ↥Γt × G,
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) ((z * γ).1 : (ℍ[ℚ, a₁, b₁])ˣ)))) ψ = ψ ∧
      ∀ x : (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G)).obj k,
        DeligneDatum.IsPullback (K := K₀) (π := π) k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (z.1 : (ℍ[ℚ, a₁, b₁])ˣ))⁻¹ x.1 x.1 ∧
        @Eq G x.2 (@HMul.hMul G G G _ (@HMul.hMul G G G _ (θt z.1) x.2) (z.2)⁻¹) := by
  classical

  let V : (ℍ[ℚ, a₁, b₁])ˣ →* Multiplicative ℤ := vdet.comp (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀))
  have hV : ∀ z : (ℍ[ℚ, a₁, b₁])ˣ, V z = vdet (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) z) := fun z => rfl

  let C : ↥Γt → Prop := fun z => (∃ c₀ : ℚ, ((z : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c₀ • (1 : ℍ[ℚ, a₁, b₁])) ∧ θt z = 1
  have hC_one : C 1 := ⟨⟨1, by simp⟩, map_one θt⟩
  have hC_mul : ∀ x y, C x → C y → C (x * y) := by
    rintro x y ⟨⟨cx, hx⟩, hθx⟩ ⟨⟨cy, hy⟩, hθy⟩
    refine ⟨⟨cx * cy, ?_⟩, by rw [map_mul, hθx, hθy, one_mul]⟩
    show ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((y : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = _
    rw [hx, hy, smul_mul_smul_comm, one_mul, mul_smul]
  have hscalar_inv : ∀ (x : (ℍ[ℚ, a₁, b₁])ˣ) (cx : ℚ), (x : ℍ[ℚ, a₁, b₁]) = cx • 1 →
      cx ≠ 0 ∧ ((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = cx⁻¹ • (1 : ℍ[ℚ, a₁, b₁]) := by
    intro x cx hx
    have hcx : cx ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [hx, zero_smul])
    refine ⟨hcx, ?_⟩
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hx, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hcx, one_smul])
  have hC_inv : ∀ x, C x → C x⁻¹ := by
    rintro x ⟨⟨cx, hx⟩, hθx⟩
    obtain ⟨-, hinv⟩ := hscalar_inv (x : (ℍ[ℚ, a₁, b₁])ˣ) cx hx
    exact ⟨⟨cx⁻¹, by rw [Subgroup.coe_inv]; exact hinv⟩, by rw [map_inv, hθx, inv_one]⟩

  let A : AddSubgroup ℤ :=
    { carrier := {n | ∃ z : ↥Γt, C z ∧ Multiplicative.toAdd (V z) = n}
      zero_mem' := ⟨1, hC_one, by simp⟩
      add_mem' := by
        rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, hC_mul x y hx hy, by rw [Subgroup.coe_mul, map_mul, toAdd_mul]⟩
      neg_mem' := by
        rintro a ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, hC_inv x hx, by rw [Subgroup.coe_inv, map_inv, toAdd_inv]⟩ }
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic A
  have hgA : g ∈ A := by rw [hg]; exact AddSubgroup.subset_closure (Set.mem_singleton g)
  have hAmul : ∀ n ∈ A, ∃ j : ℤ, j * g = n := by
    intro n hn
    rw [hg, AddSubgroup.mem_closure_singleton] at hn
    obtain ⟨j, hj⟩ := hn
    exact ⟨j, by rw [← hj, smul_eq_mul]⟩

  set vγ : ℤ := Multiplicative.toAdd (vdet (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ))) with hvγ
  have hfix : ∀ y : Onr, (Fr ^ g) y = y → ψ ((Fr ^ (-vγ)) y) = ψ y := by
    intro y hy
    have := hceq y (fun z hz hcent hθ => by
      obtain ⟨j, hj⟩ := hAmul _ ⟨⟨z, hz⟩, ⟨hcent, hθ⟩, rfl⟩
      show (Fr ^ Multiplicative.toAdd (V z)) y = y
      rw [← hj, zpow_mul']
      exact zpow_apply_eq_self _ y hy j)
    rw [this, frobTwist_apply]
  have hdvd : g ∣ -vγ :=
    CerednikDrinfeld.dvd_of_forall_frobenius_zpow_apply_eq_of_fixed 𝒪 π hπ hres hunr Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr k ψ g (-vγ) hfix

  have hmem : -vγ ∈ A := by
    obtain ⟨j, hj⟩ := hdvd
    rw [hj, mul_comm, ← smul_eq_mul, hg]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_singleton g)) j
  obtain ⟨h, ⟨⟨c₀, hc₀⟩, hθh⟩, hVh⟩ := hmem
  refine ⟨(h, 1), ?_, ?_⟩
  ·
    have : Multiplicative.toAdd (vdet (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (((h, (1 : G)) * γ).1 : (ℍ[ℚ, a₁, b₁])ˣ))) = 0 := by
      rw [Prod.fst_mul, Subgroup.coe_mul, map_mul, map_mul, toAdd_mul, ← hV, hVh, ← hvγ, neg_add_cancel]
    rw [this, neg_zero, frobTwist_zero]
  · rintro ⟨x1, x2⟩
    change G at x2
    obtain ⟨hc₀0, hinv⟩ := hscalar_inv (h : (ℍ[ℚ, a₁, b₁])ˣ) c₀ hc₀
    have hc₀K : (algebraMap ℚ K₀ c₀) ≠ 0 := (map_ne_zero _).mpr hc₀0
    refine ⟨?_, ?_⟩
    ·
      have hscal : (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (h : (ℍ[ℚ, a₁, b₁])ˣ))⁻¹ =
          scalarGL (Units.mk0 (algebraMap ℚ K₀ c₀) hc₀K)⁻¹ := by
        apply Units.ext
        rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, hinv, map_smul, map_one, scalarGL_coe, Units.val_inv_eq_inv_val,
          Units.val_mk0, ← map_inv₀, algebraMap_smul]
      rw [hscal]
      exact isPullback_scalarGL k _ x1
    · show x2 = θt h * x2 * (1 : G)⁻¹
      rw [hθh, one_mul, inv_one, mul_one]

end S_CerednikDrinfeld_cerednikDrinfeld_realign_of_frobTwist_eq_on_fixed
end P2MW
export P2MW.S_CerednikDrinfeld_cerednikDrinfeld_realign_of_frobTwist_eq_on_fixed (solution)
