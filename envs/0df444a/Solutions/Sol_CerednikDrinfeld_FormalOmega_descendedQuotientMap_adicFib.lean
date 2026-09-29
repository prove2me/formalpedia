-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_adicFib
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2fbcf4fb-40a4-5164-8c53-07705be0df95

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_CerednikDrinfeld_FormalOmega_frobTwo_frobTwo_and_exists_generator
import Theorems.Thm_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
import Theorems.Thm_CerednikDrinfeld_FormalOmega_IsAdicFrame_isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalOmega_IsAdicFrame_isLocalRing_and_nontrivial_modPow
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AdicPoint_exists_isTwistedAct_iff_exists_eq_act
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib

set_option autoImplicit false

p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib.CerednikDrinfeld.FormalOmega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree FormalOmega.AdicPoint FormalOmega.IsAdicFrame FormalOmega.MumfordTower FormalOmega.frobTwo_frobTwo_and_exists_generator FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer FormalOmega.IsAdicFrame.isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed FormalOmega.IsAdicFrame.isLocalRing_and_nontrivial_modPow FormalOmega.AdicPoint.exists_isTwistedAct_iff_exists_eq_act"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "DeligneDatum.pullback DeligneDatum.isPullback_pullback Omega Omega.action DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback OmegaNr.IsTwistedAct AlgFunctor AlgFunctor.prod AlgFunctor.corep Omega.action_scalarGL modPow modPowTransition AdicPoint AdicPoint.ext' IsAdicFrame MumfordTower frobTwo_frobTwo_and_exists_generator algHom_eq_or_eq_comp_frobTwo_of_isLocalRing MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer IsAdicFrame.isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed IsAdicFrame.isLocalRing_and_nontrivial_modPow AdicPoint.exists_isTwistedAct_iff_exists_eq_act"
namespace F6cAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section Pullback

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (K : Type) [Field K] [Algebra 𝒪 K] (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem act_eq_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d : (Omega K π).obj B) :
    (Omega.action K π).act B g d = DeligneDatum.pullback (K := K) π B g⁻¹ d := rfl

theorem eq_pullback_of_isPullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : (Omega K π).obj B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g d d') : d' = DeligneDatum.pullback (K := K) π B g d := by
  apply DeligneDatum.ext'
  funext M
  exact h M

theorem isPullback_iff_eq_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : (Omega K π).obj B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d' ↔ d' = (Omega.action K π).act B g d := by
  constructor
  · intro h; rw [act_eq_pullback]; exact eq_pullback_of_isPullback π K B _ d d' h
  · intro h; rw [h, act_eq_pullback]; exact DeligneDatum.isPullback_pullback (K := K) π B _ d

theorem isPullback_trans (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) K) (d d' d'' : (Omega K π).obj B)
    (h₁ : DeligneDatum.IsPullback (K := K) (π := π) B g₁⁻¹ d d')
    (h₂ : DeligneDatum.IsPullback (K := K) (π := π) B g₂⁻¹ d' d'') :
    DeligneDatum.IsPullback (K := K) (π := π) B (g₂ * g₁)⁻¹ d d'' := by
  rw [isPullback_iff_eq_act] at h₁ h₂ ⊢
  rw [h₂, h₁, (Omega.action K π).act_mul]

theorem isPullback_refl (d : (Omega K π).obj B) :
    DeligneDatum.IsPullback (K := K) (π := π) B (1 : Matrix.GeneralLinearGroup (Fin 2) K)⁻¹ d d := by
  rw [isPullback_iff_eq_act, (Omega.action K π).act_one]

theorem isPullback_symm (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : (Omega K π).obj B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d') :
    DeligneDatum.IsPullback (K := K) (π := π) B (g⁻¹)⁻¹ d' d := by
  rw [isPullback_iff_eq_act] at h ⊢
  rw [h, ← (Omega.action K π).act_mul, inv_mul_cancel, (Omega.action K π).act_one]

theorem scalarGL_eq_scalar (c : Kˣ) : scalarGL c = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  simp [scalarGL, Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem act_of_mem_center (z : Matrix.GeneralLinearGroup (Fin 2) K) (hz : z ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K))
    (d : (Omega K π).obj B) : (Omega.action K π).act B z d = d := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, rfl⟩ := hz
  rw [← scalarGL_eq_scalar]
  exact Omega.action_scalarGL π B c d

theorem isPullback_iff_of_mk_eq (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (e : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk h) (d d' : (Omega K π).obj B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ d d' ↔ DeligneDatum.IsPullback (K := K) (π := π) B h⁻¹ d d' := by
  have hz : g⁻¹ * h ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, map_inv, e, inv_mul_cancel]
  have : h = g * (g⁻¹ * h) := by rw [mul_inv_cancel_left]
  rw [isPullback_iff_eq_act, isPullback_iff_eq_act, this, (Omega.action K π).act_mul, act_of_mem_center π K B _ hz]

end Pullback

section Frob

variable {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A]

theorem algEquiv_mul_self_eq_one (F : A ≃ₐ[R] A) (hF : ∀ z, F (F z) = z) : F * F = 1 := by
  ext z; exact hF z

theorem algEquiv_zpow_of_even (F : A ≃ₐ[R] A) (hF : ∀ z, F (F z) = z) (m : ℤ) (hm : Even m) : F ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, zpow_mul, show (F ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact algEquiv_mul_self_eq_one F hF, one_zpow]

theorem algEquiv_zpow_of_odd (F : A ≃ₐ[R] A) (hF : ∀ z, F (F z) = z) (m : ℤ) (hm : Odd m) : F ^ m = F := by
  obtain ⟨k, rfl⟩ := hm
  rw [zpow_add, zpow_one, zpow_mul, show (F ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact algEquiv_mul_self_eq_one F hF,
    one_zpow, one_mul]

end Frob

theorem comp_ne_of_isUnit_sub {R A k : Type} [CommRing R] [CommRing A] [CommRing k] [Nontrivial k] [Algebra R A] [Algebra R k]
    (F : A ≃ₐ[R] A) (α : A) (hα : IsUnit (F α - α)) (ψ : A →ₐ[R] k) : ψ.comp (F : A →ₐ[R] A) ≠ ψ := by
  intro h
  have : ψ (F α - α) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun φ : A →ₐ[R] k => φ α) h
  exact not_isUnit_zero (this ▸ hα.map ψ)

section Quot

variable {𝒪 : Type} [CommRing 𝒪]

theorem quotientMap_comp_algebraMap {A : Type} [CommRing A] [Algebra 𝒪 A] (J : Ideal 𝒪) (I : Ideal A)
    (h : J ≤ I.comap (algebraMap 𝒪 A)) :
    (Ideal.quotientMap I (algebraMap 𝒪 A) h).comp (algebraMap 𝒪 (𝒪 ⧸ J)) = algebraMap 𝒪 (A ⧸ I) := by
  ext x; rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl

theorem nontrivial_quotient_pow {A : Type} [CommRing A] (s : A) (n : ℕ) (h : Nontrivial (A ⧸ Ideal.span {s ^ (0 + 1)})) :
    Nontrivial (A ⧸ Ideal.span {s ^ (n + 1)}) := by
  refine nontrivial_of_ne (0 : A ⧸ Ideal.span {s ^ (n + 1)}) 1 fun h01 => ?_
  have htop : Ideal.span {s ^ (n + 1)} = ⊤ := Ideal.Quotient.zero_eq_one_iff.mp h01
  have htop' : Ideal.span {s ^ (0 + 1)} = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow s (Nat.succ_le_succ (Nat.zero_le n)))
  exact (zero_ne_one (α := A ⧸ Ideal.span {s ^ (0 + 1)})) (Ideal.Quotient.zero_eq_one_iff.mpr htop')

theorem isLocalRing_quotient {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (h : Nontrivial (A ⧸ I)) :
    IsLocalRing (A ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

end Quot

end CerednikDrinfeld.FormalOmega.F6cAux

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

set_option maxHeartbeats 1600000 in

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

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0)
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)

    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] [Finite G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (θ : ↥Γ →* G₂) (Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (ha_over : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hX : ∀ n : ℕ, IsPullback (pr₁ n) (pr₂ n) (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hxb : ∀ n : ℕ, xb n = pr₁ n ≫ DM.zb n)
    (hxt₁ : ∀ n : ℕ, xt n ≫ pr₁ (n + 1) = pr₁ n ≫ DM.zt n)
    (hxt₂ : ∀ n : ℕ, xt n ≫ pr₂ (n + 1) = pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))))
    (hθsurj : Function.Surjective θ) (hθker : ∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N)
    (hFr₂ : ∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (ha_pr₂ : ∀ (n : ℕ) (γ : ↥Γ), (a n (θ γ)).hom ≫ pr₂ n =
      pr₂ n ≫ Spec.map (CommRingCat.ofHom ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom))
    (ha_pr₁ : ∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
      ∀ x : Spec (CommRingCat.of B) ⟶ X n, x ≫ pr₁ n = DM.q n B hB P → (x ≫ (a n (θ γ)).hom) ≫ pr₁ n = DM.q n B hB P')

    (DQ : TowerQuotientDatum 𝒪 π X xb xt G₂ a)
    (q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ DQ.Y n))
    (hqdef : (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B)
        (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr))
        (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X n),
        x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → q n B hB (ψ, P) = x ≫ DQ.p n)) :
    (∀ (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
          [CompleteSpace C] [IsAlgClosed C]
          (R : Type) [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
          (ϖ : PseudoUniformizer K₀ C), IsAdicFrame π ϖ R → ∀ (ψ₀ : Onr →ₐ[𝒪] R)
          (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0),
        (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ DQ.Y n,
          (∀ n : ℕ, η n ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
            Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
          (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ DQ.yt n) →
          ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)) ∧
        (∀ x x' : AdicPoint K₀ π R,
          (∀ n : ℕ, q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) = q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) ↔
          ∃ γ ∈ Γ, ∀ n : ℕ, OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) (σ γ) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n))) := by
  classical
  intro C _ _ _ Γ₀ _ _ _ _ R _ _ _ _ _ _ ϖ hF ψ₀ hmod

  let O₂ : Subalgebra 𝒪 Onr := AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)
  let I₂ : ∀ n : ℕ, Ideal ↥O₂ := fun n => Ideal.span {(algebraMap 𝒪 ↥O₂ π) ^ (n + 1)}
  let IR : ∀ n : ℕ, Ideal R := fun n => Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}

  haveI hdvrI : IsDiscreteValuationRing 𝒪 := hdvr
  obtain ⟨hRloc, hR0⟩ := CerednikDrinfeld.FormalOmega.IsAdicFrame.isLocalRing_and_nontrivial_modPow (K₀ := K₀) ϖ hF
  haveI := hRloc
  have hRn : ∀ n : ℕ, Nontrivial (modPow π R n) := fun n => F6cAux.nontrivial_quotient_pow (algebraMap 𝒪 R π) n hR0
  have hRnloc : ∀ n : ℕ, IsLocalRing (modPow π R n) := fun n => F6cAux.isLocalRing_quotient (IR n) (hRn n)
  have hNfin : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ N ∧ g • v = v} := fun v =>
    (hdisc v).subset fun g hg => ⟨hNle hg.1, hg.2⟩

  let ψ₀n : ∀ n : ℕ, Onr →ₐ[𝒪] modPow π R n := fun n => (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀
  have hI₂R : ∀ n : ℕ, I₂ n ≤ (IR n).comap (ψ₀.comp O₂.val) := by
    intro n
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, AlgHom.commutes]
    exact Ideal.subset_span rfl
  let ψ₂ : ∀ n : ℕ, (↥O₂ ⧸ I₂ n) →ₐ[𝒪] modPow π R n := fun n => Ideal.quotientMapₐ (IR n) (ψ₀.comp O₂.val) (hI₂R n)
  have hψ₂ : ∀ (n : ℕ) (y : ↥O₂), ψ₂ n (Ideal.Quotient.mk (I₂ n) y) = ψ₀n n (y : Onr) := fun n y => rfl

  have htfac : ∀ n : ℕ, (modPowTransition π R n).toRingHom =
      Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))) :=
    fun n => rfl
  have hψ₂compat : ∀ n : ℕ, (modPowTransition π R n).toRingHom.comp (ψ₂ (n + 1)).toRingHom =
      (ψ₂ n).toRingHom.comp (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 ↥O₂ π) (Nat.le_succ (n + 1))))) := by
    intro n
    apply Ideal.Quotient.ringHom_ext
    ext y
    rfl

  have hc0a := fun n : ℕ => CerednikDrinfeld.FormalOmega.frobTwo_frobTwo_and_exists_generator 𝒪 hdvr π hπ hcomplete hres hunr
    Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr n (Fr₂ n) (hFr₂ n)
  have hFF : ∀ (n : ℕ) z, Fr₂ n (Fr₂ n z) = z := fun n => (hc0a n).1
  have hFr₂even : ∀ (n : ℕ) (m : ℤ), Even m → (Fr₂ n) ^ m = 1 := fun n m hm => F6cAux.algEquiv_zpow_of_even (Fr₂ n) (hFF n) m hm
  have hFr₂odd : ∀ (n : ℕ) (m : ℤ), Odd m → (Fr₂ n) ^ m = Fr₂ n := fun n m hm => F6cAux.algEquiv_zpow_of_odd (Fr₂ n) (hFF n) m hm
  have hneFr : ∀ (n : ℕ) (S : Type) [CommRing S] [Algebra 𝒪 S] (hS : Nontrivial S) (φ : (↥O₂ ⧸ I₂ n) →ₐ[𝒪] S),
      φ.comp (Fr₂ n).toAlgHom ≠ φ := by
    intro n S _ _ hS φ
    obtain ⟨-, α, hαu, -, -⟩ := hc0a n
    exact F6cAux.comp_ne_of_isUnit_sub (Fr₂ n) α hαu φ

  have hmono : ∀ n : ℕ, Mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := by
    intro n
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hI₂le : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤ (I₂ n).comap (algebraMap 𝒪 ↥O₂) := by
    intro n
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl
  have hIRle : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤ (IR n).comap (algebraMap 𝒪 R) := by
    intro n
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl
  have hqm : ∀ n : ℕ, (Ideal.quotientMap (I₂ n) (algebraMap 𝒪 ↥O₂) (hI₂le n)).comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) =
      algebraMap 𝒪 (↥O₂ ⧸ I₂ n) := fun n => F6cAux.quotientMap_comp_algebraMap _ _ _
  have hqmR : ∀ n : ℕ, (Ideal.quotientMap (IR n) (algebraMap 𝒪 R) (hIRle n)).comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) =
      algebraMap 𝒪 (modPow π R n) := fun n => F6cAux.quotientMap_comp_algebraMap _ _ _
  have hring : ∀ n : ℕ, (ψ₂ n).toRingHom.comp ((Ideal.quotientMap (I₂ n) (algebraMap 𝒪 ↥O₂) (hI₂le n)).comp
      (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = algebraMap 𝒪 (modPow π R n) := by
    intro n
    rw [hqm n]
    exact (ψ₂ n).comp_algebraMap
  have hψ₂over : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I₂ n) (algebraMap 𝒪 ↥O₂) (hI₂le n))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n))) := by
    intro n
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring n]
  have wq : ∀ (n : ℕ) (P : (Omega K₀ π).obj (modPow π R n)), DM.q n (modPow π R n) (hmod n) P ≫ DM.zb n =
      Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I₂ n) (algebraMap 𝒪 ↥O₂) (hI₂le n))) := by
    intro n P
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc,
      DM.q_over, Category.assoc, hψ₂over n]
  let xOf : ∀ n : ℕ, (Omega K₀ π).obj (modPow π R n) → (Spec (CommRingCat.of (modPow π R n)) ⟶ X n) := fun n P =>
    (hX n).lift (DM.q n (modPow π R n) (hmod n) P) (Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom)) (wq n P)
  have xOf_pr₁ : ∀ n P, xOf n P ≫ pr₁ n = DM.q n (modPow π R n) (hmod n) P := fun n P => (hX n).lift_fst _ _ _
  have xOf_pr₂ : ∀ n P, xOf n P ≫ pr₂ n = Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom) := fun n P => (hX n).lift_snd _ _ _
  have hq : ∀ n P, q n (modPow π R n) (hmod n) (ψ₀n n, P) = xOf n P ≫ DQ.p n := fun n P =>
    hqdef n (modPow π R n) (hmod n) (ψ₀n n) (ψ₂ n) (hψ₂ n) P (xOf n P) (xOf_pr₁ n P) (xOf_pr₂ n P)

  have hpr₂γ : ∀ (n : ℕ) (γ : ↥Γ) (x : Spec (CommRingCat.of (modPow π R n)) ⟶ X n) (ε : (↥O₂ ⧸ I₂ n) →ₐ[𝒪] modPow π R n),
      x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ε.toRingHom) →
      (x ≫ (a n (θ γ)).hom) ≫ pr₂ n =
        Spec.map (CommRingCat.ofHom (ε.comp ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toAlgHom).toRingHom) := by
    intro n γ x ε hx
    rw [Category.assoc, ha_pr₂, ← Category.assoc, hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hmod' : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1 + 1) = 0 := fun n => by rw [pow_succ, hmod n, zero_mul]
  have xOf_compat : ∀ (x : AdicPoint K₀ π R) (n : ℕ),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ xOf (n + 1) (x.pt (n + 1)) = xOf n (x.pt n) ≫ xt n := by
    intro x n
    apply (hX (n + 1)).hom_ext
    · rw [Category.assoc, xOf_pr₁, Category.assoc, hxt₁, ← Category.assoc, xOf_pr₁, ← DM.q_zt n _ (hmod n) (hmod' n), ← htfac n,
        ← DM.q_natural (n + 1) _ _ (hmod (n + 1)) (hmod' n) (modPowTransition π R n) (x.pt (n + 1))]
      exact congrArg (DM.q (n + 1) (modPow π R n) (hmod' n)) (x.compat n)
    · rw [Category.assoc, xOf_pr₂, Category.assoc, hxt₂, ← Category.assoc, xOf_pr₂, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← htfac n, hψ₂compat n]
  refine ⟨?_, ?_⟩
  ·
    intro η hηover hηcompat
    obtain ⟨hRcompl, hRdom, hRval, hRfrac, hRac⟩ :=
      CerednikDrinfeld.FormalOmega.IsAdicFrame.isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed (K₀ := K₀) ϖ hF
    haveI := hRdom
    haveI := hRval
    have hηover' : ∀ n : ℕ, η n ≫ DQ.yb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (IR n) (algebraMap 𝒪 R) (hIRle n))) := by
      intro n
      rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc, hηover n,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, hqmR n]
    have hηcompat' : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ η (n + 1) = η n ≫ DQ.yt n := by
      intro n; rw [← htfac n]; exact hηcompat n
    obtain ⟨⟨xf₀, hxf₀p, hxf₀c⟩, -⟩ := DQ.adicFib R hRcompl hRac η hηover' hηcompat'

    have hεalg : ∀ (n : ℕ) (x : Spec (CommRingCat.of (modPow π R n)) ⟶ X n), x ≫ DQ.p n = η n →
        ∃ ε : (↥O₂ ⧸ I₂ n) →ₐ[𝒪] modPow π R n, x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ε.toRingHom) := by
      intro n x hx
      obtain ⟨εr, hεr⟩ := Spec.map_surjective (x ≫ pr₂ n)
      have hεO : εr.hom.comp (algebraMap 𝒪 (↥O₂ ⧸ I₂ n)) = algebraMap 𝒪 (modPow π R n) := by
        have e1 : x ≫ pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I₂ n) (algebraMap 𝒪 ↥O₂) (hI₂le n))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
            Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n))) := by
          rw [← Category.assoc (pr₂ n), ← (hX n).w, Category.assoc, ← Category.assoc (pr₁ n), ← hxb, ← DQ.p_over n,
            Category.assoc, ← Category.assoc x, hx]
          exact hηover n
        rw [← Category.assoc, ← hεr, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at e1
        have e2 := Spec.map_injective e1
        have e3 := congrArg CommRingCat.Hom.hom e2
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e3
        rw [← hqm n, ← RingHom.comp_assoc]
        exact e3
      let ε : (↥O₂ ⧸ I₂ n) →ₐ[𝒪] modPow π R n :=
        { toRingHom := εr.hom, commutes' := fun c => by
            have := congrArg (fun φ : 𝒪 →+* modPow π R n => φ c) hεO; simpa using this }
      exact ⟨ε, by rw [← hεr]; rfl⟩
    obtain ⟨xf, hxfp, hxfc, hxf0⟩ : ∃ xf : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ X n,
        (∀ n : ℕ, xf n ≫ DQ.p n = η n) ∧
        (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
          (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ xf (n + 1) = xf n ≫ xt n) ∧
        xf 0 ≫ pr₂ 0 = Spec.map (CommRingCat.ofHom (ψ₂ 0).toRingHom) := by
      obtain ⟨ε, hε⟩ := hεalg 0 (xf₀ 0) (hxf₀p 0)
      rcases CerednikDrinfeld.FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing 𝒪 hdvr π hπ hcomplete hres hunr
          Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr 0 (Fr₂ 0) (hFr₂ 0) (modPow π R 0) (ψ₂ 0) ε with h0 | h0
      · exact ⟨xf₀, hxf₀p, hxf₀c, by rw [hε, h0]⟩
      · obtain ⟨w, hwΓ, hw⟩ := hodd
        refine ⟨fun n => xf₀ n ≫ (a n (θ ⟨w, hwΓ⟩)).hom, fun n => by rw [Category.assoc, DQ.p_inv]; exact hxf₀p n, fun n => ?_, ?_⟩
        · rw [← Category.assoc, hxf₀c n, Category.assoc, Category.assoc, ha_xt]
        · rw [hpr₂γ 0 ⟨w, hwΓ⟩ (xf₀ 0) ε hε, h0]
          have hF : (Fr₂ 0) ^ (- Multiplicative.toAdd (vdet (σ ((⟨w, hwΓ⟩ : ↥Γ) : G)))) = Fr₂ 0 := by
            apply hFr₂odd
            rw [Subgroup.coe_mk, hw]
            decide
          rw [hF]
          congr 2
          apply congrArg AlgHom.toRingHom
          apply AlgHom.ext
          intro z
          show ψ₂ 0 ((Fr₂ 0) ((Fr₂ 0) z)) = ψ₂ 0 z
          rw [hFF]

    have hxfpr₂ : ∀ n : ℕ, xf n ≫ pr₂ n = Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom) := by
      intro n
      induction n with
      | zero => exact hxf0
      | succ n ih =>
        obtain ⟨ε, hε⟩ := hεalg (n + 1) (xf (n + 1)) (hxfp (n + 1))
        rcases CerednikDrinfeld.FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing 𝒪 hdvr π hπ hcomplete hres hunr
            Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr (n + 1) (Fr₂ (n + 1)) (hFr₂ (n + 1)) (modPow π R (n + 1))
            (ψ₂ (n + 1)) ε with h1 | h1
        · rw [hε, h1]
        · exfalso

          have e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ xf (n + 1) ≫ pr₂ (n + 1) =
              xf n ≫ pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
                (pow_dvd_pow (algebraMap 𝒪 ↥O₂ π) (Nat.le_succ (n + 1)))))) := by
            rw [← Category.assoc, hxfc n, Category.assoc, hxt₂]
          rw [hε, ← Category.assoc, ih, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
            ← hψ₂compat n, ← htfac n, h1] at e1
          have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
          simp only [CommRingCat.hom_ofHom] at e3
          apply hneFr (n + 1) (modPow π R n) (hRn n) ((modPowTransition π R n).comp (ψ₂ (n + 1)))
          apply AlgHom.ext
          intro z
          exact congrArg (fun φ : _ →+* modPow π R n => φ z) e3

    have hz := (CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer 𝒪 hdvr π hπ
      hcomplete hres hunr K₀ g₁ hg₁ N hNfin DM R hmod).1 (fun n => xf n ≫ pr₁ n) (fun n => by
        rw [Category.assoc, ← Category.assoc (pr₁ n), ← hxb, ← DQ.p_over n, Category.assoc, ← Category.assoc (xf n), hxfp n]
        exact hηover n) (fun n => by
        rw [htfac n, ← Category.assoc, hxfc n, Category.assoc, hxt₁, Category.assoc])
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, fun n => ?_⟩
    rw [hqdef n (modPow π R n) (hmod n) (ψ₀n n) (ψ₂ n) (hψ₂ n) (x.pt n) (xf n) (hx n) (hxfpr₂ n), hxfp n]
  ·
    intro x x'
    rw [CerednikDrinfeld.FormalOmega.AdicPoint.exists_isTwistedAct_iff_exists_eq_act 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
      hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt R hR0 ψ₀ x x']
    constructor
    · intro hPP'
      obtain ⟨hRcompl, hRdom, hRval, hRfrac, hRac⟩ :=
        CerednikDrinfeld.FormalOmega.IsAdicFrame.isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed (K₀ := K₀) ϖ hF
      haveI := hRdom
      haveI := hRval

      have hy : ∀ n : ℕ, xOf n (x'.pt n) ≫ DQ.p n = xOf n (x.pt n) ≫ DQ.p n := fun n => by
        rw [← hq, ← hq]; exact (hPP' n).symm
      have hyover : ∀ n : ℕ, (xOf n (x.pt n) ≫ DQ.p n) ≫ DQ.yb n =
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap (IR n) (algebraMap 𝒪 R) (hIRle n))) := by
        intro n
        rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))),
          Category.assoc _ (DQ.p n) (DQ.yb n), DQ.p_over, hxb, ← Category.assoc _ (pr₁ n) (DM.zb n), xOf_pr₁, Category.assoc,
          DM.q_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hqmR n]
      have hycompat : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
          (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ (xOf (n + 1) (x.pt (n + 1)) ≫ DQ.p (n + 1)) =
          (xOf n (x.pt n) ≫ DQ.p n) ≫ DQ.yt n := by
        intro n; rw [← Category.assoc, xOf_compat x n, Category.assoc, Category.assoc, DQ.p_xt]
      obtain ⟨g, hg⟩ := (DQ.adicFib R hRcompl hRac (fun n => xOf n (x.pt n) ≫ DQ.p n) hyover hycompat).2
        (fun n => xOf n (x.pt n)) (fun n => xOf n (x'.pt n)) (fun n => rfl) hy (xOf_compat x) (xOf_compat x')
      obtain ⟨γ, rfl⟩ := hθsurj g

      have h2 := hpr₂γ 0 γ (xOf 0 (x.pt 0)) (ψ₂ 0) (xOf_pr₂ 0 _)
      rw [← hg 0, xOf_pr₂ 0] at h2
      have hcomp : ψ₂ 0 = (ψ₂ 0).comp ((Fr₂ 0) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toAlgHom := by
        have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
        simp only [CommRingCat.hom_ofHom] at e3
        exact AlgHom.ext fun z => congrArg (fun φ : _ →+* modPow π R 0 => φ z) e3
      have heven : Even (Multiplicative.toAdd (vdet (σ (γ : G)))) := by
        by_contra hne
        have hodd' : Odd (- Multiplicative.toAdd (vdet (σ (γ : G)))) := by
          rw [odd_neg]; exact Int.not_even_iff_odd.mp hne
        rw [hFr₂odd 0 _ hodd'] at hcomp
        exact hneFr 0 (modPow π R 0) hR0 (ψ₂ 0) hcomp.symm

      have h1 : ∀ n : ℕ, DM.q n (modPow π R n) (hmod n) ((x.act (σ (γ : G))).pt n) = DM.q n (modPow π R n) (hmod n) (x'.pt n) := by
        intro n
        have hPP₂ : DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) (σ (γ : G))⁻¹ (x.pt n) ((x.act (σ (γ : G))).pt n) :=
          (F6cAux.isPullback_iff_eq_act π K₀ (modPow π R n) _ _ _).mpr rfl
        have h := ha_pr₁ n γ (modPow π R n) (hmod n) (x.pt n) _ hPP₂ (xOf n (x.pt n)) (xOf_pr₁ n _)
        rw [← hg n, xOf_pr₁] at h
        exact h.symm
      obtain ⟨h, hhN, hh⟩ := ((CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
        𝒪 hdvr π hπ hcomplete hres hunr K₀ g₁ hg₁ N hNfin DM R hmod).2 (x.act (σ (γ : G))) x').mp h1
      obtain ⟨δ, hδ, hδh⟩ := Subgroup.mem_map.mp (hNle hhN)
      have hδh' : Matrix.ProjGenLinGroup.mk (σ δ) = Matrix.ProjGenLinGroup.mk h := by rw [← hρ]; exact hδh
      obtain ⟨hδΓ, hδeven⟩ := (hΓ' δ).mp hδ
      refine ⟨δ * (γ : G), (hΓ' _).mpr ⟨Γ.mul_mem hδΓ γ.2, ?_⟩, ?_⟩
      · rw [map_mul, map_mul, toAdd_mul]; exact hδeven.add heven
      · apply AdicPoint.ext'
        funext n
        have hh' := (F6cAux.isPullback_iff_of_mk_eq π K₀ (modPow π R n) h (σ δ) hδh'.symm _ _).mp (hh n)
        have hPP₂ : DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) (σ (γ : G))⁻¹ (x.pt n) ((x.act (σ (γ : G))).pt n) :=
          (F6cAux.isPullback_iff_eq_act π K₀ (modPow π R n) _ _ _).mpr rfl
        have htot := F6cAux.isPullback_trans π K₀ (modPow π R n) (σ (γ : G)) (σ δ) (x.pt n) _ (x'.pt n) hPP₂ hh'
        rw [← map_mul] at htot
        exact (F6cAux.isPullback_iff_eq_act π K₀ (modPow π R n) _ _ _).mp htot
    · rintro ⟨γ', hγ', rfl⟩
      intro n
      obtain ⟨hγ'Γ, hγ'even⟩ := (hΓ' γ').mp hγ'
      have hPB : DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) (σ γ')⁻¹ (x.pt n) ((x.act (σ γ')).pt n) :=
        (F6cAux.isPullback_iff_eq_act π K₀ (modPow π R n) _ _ _).mpr rfl
      have h1 : (xOf n (x.pt n) ≫ (a n (θ ⟨γ', hγ'Γ⟩)).hom) ≫ pr₁ n = DM.q n (modPow π R n) (hmod n) ((x.act (σ γ')).pt n) :=
        ha_pr₁ n ⟨γ', hγ'Γ⟩ (modPow π R n) (hmod n) (x.pt n) _ hPB (xOf n (x.pt n)) (xOf_pr₁ n _)
      have h2 : (xOf n (x.pt n) ≫ (a n (θ ⟨γ', hγ'Γ⟩)).hom) ≫ pr₂ n = Spec.map (CommRingCat.ofHom (ψ₂ n).toRingHom) := by
        rw [hpr₂γ n ⟨γ', hγ'Γ⟩ (xOf n (x.pt n)) (ψ₂ n) (xOf_pr₂ n _), hFr₂even n _ (by rw [even_neg]; exact hγ'even)]
        rfl
      rw [hq n (x.pt n), hqdef n (modPow π R n) (hmod n) (ψ₀n n) (ψ₂ n) (hψ₂ n) ((x.act (σ γ')).pt n) _ h1 h2, Category.assoc,
        DQ.p_inv]

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_adicFib (solution)
