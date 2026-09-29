-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_fib
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e342fe17-8b44-51d7-a91b-f0373fc0ca6c

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_CerednikDrinfeld_FormalOmega_frobTwo_frobTwo_and_exists_generator
import Theorems.Thm_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_q_eq_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_OmegaNr_exists_isTwistedAct_iff_exists_even_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib

set_option autoImplicit false

p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib.CerednikDrinfeld.FormalOmega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree FormalOmega.MumfordTower FormalOmega.frobTwo_frobTwo_and_exists_generator FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing FormalOmega.MumfordTower.exists_q_eq_of_isAlgClosed OmegaNr.exists_isTwistedAct_iff_exists_even_isPullback"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "DeligneDatum.pullback DeligneDatum.isPullback_pullback Omega Omega.action DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback OmegaNr.IsTwistedAct AlgFunctor AlgFunctor.prod AlgFunctor.corep Omega.action_scalarGL MumfordTower frobTwo_frobTwo_and_exists_generator algHom_eq_or_eq_comp_frobTwo_of_isLocalRing MumfordTower.exists_q_eq_of_isAlgClosed"
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

end CerednikDrinfeld.FormalOmega.F6cAux

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

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
    (∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : (algebraMap 𝒪 k π) ^ (n + 1) = 0)
    (ψ : Onr →ₐ[𝒪] k),
    (∀ η : Spec (CommRingCat.of k) ⟶ DQ.Y n,
      η ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) →
      ∃ P : (Omega K₀ π).obj k, q n k hk (ψ, P) = η) ∧
    ∀ P P' : (Omega K₀ π).obj k, q n k hk (ψ, P) = q n k hk (ψ, P') ↔
      ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P')) := by
  classical
  intro n k _ _ _ hk ψ

  let O₂ : Subalgebra 𝒪 Onr := AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)
  let I₂ : Ideal ↥O₂ := Ideal.span {(algebraMap 𝒪 ↥O₂ π) ^ (n + 1)}
  haveI : Nontrivial k := inferInstance
  have hπk : algebraMap 𝒪 k π = 0 := pow_eq_zero_iff (n := n + 1) (Nat.succ_ne_zero n) |>.mp hk

  let ψO₂ : ↥O₂ →ₐ[𝒪] k := ψ.comp O₂.val
  have hψO₂ : ∀ a ∈ I₂, ψO₂ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_pow, AlgHom.commutes, hπk, zero_pow (Nat.succ_ne_zero n), zero_mul]
  let ψ₂ : (↥O₂ ⧸ I₂) →ₐ[𝒪] k := Ideal.Quotient.liftₐ I₂ ψO₂ hψO₂
  have hψ₂ : ∀ y : ↥O₂, ψ₂ (Ideal.Quotient.mk I₂ y) = ψ (y : Onr) := fun y => rfl

  obtain ⟨hFF, α, hαu, -, -⟩ := CerednikDrinfeld.FormalOmega.frobTwo_frobTwo_and_exists_generator 𝒪 hdvr π hπ hcomplete hres hunr
    Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr n (Fr₂ n) (hFr₂ n)
  have hFr₂even : ∀ m : ℤ, Even m → (Fr₂ n) ^ m = 1 := fun m hm => F6cAux.algEquiv_zpow_of_even (Fr₂ n) hFF m hm
  have hFr₂odd : ∀ m : ℤ, Odd m → (Fr₂ n) ^ m = Fr₂ n := fun m hm => F6cAux.algEquiv_zpow_of_odd (Fr₂ n) hFF m hm
  have hψ₂Fr := F6cAux.comp_ne_of_isUnit_sub (Fr₂ n) α hαu ψ₂

  have hmono : Mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hI₂le : Ideal.span {π ^ (n + 1)} ≤ I₂.comap (algebraMap 𝒪 ↥O₂) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl
  have hring : ψ₂.toRingHom.comp ((Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le).comp
      (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = algebraMap 𝒪 k := by
    ext x
    show ψ₂ (Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) x)) = algebraMap 𝒪 k x
    rw [Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]
    exact ψ₂.commutes x
  have hψ₂over : Spec.map (CommRingCat.ofHom ψ₂.toRingHom) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have wq : ∀ P : (Omega K₀ π).obj k, DM.q n k hk P ≫ DM.zb n =
      Spec.map (CommRingCat.ofHom ψ₂.toRingHom) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le)) := by
    intro P
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc,
      DM.q_over, Category.assoc, hψ₂over]
  let xOf : (Omega K₀ π).obj k → (Spec (CommRingCat.of k) ⟶ X n) := fun P =>
    (hX n).lift (DM.q n k hk P) (Spec.map (CommRingCat.ofHom ψ₂.toRingHom)) (wq P)
  have xOf_pr₁ : ∀ P, xOf P ≫ pr₁ n = DM.q n k hk P := fun P => (hX n).lift_fst _ _ _
  have xOf_pr₂ : ∀ P, xOf P ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) := fun P => (hX n).lift_snd _ _ _
  have hq : ∀ P, q n k hk (ψ, P) = xOf P ≫ DQ.p n := fun P => hqdef n k hk ψ ψ₂ hψ₂ P (xOf P) (xOf_pr₁ P) (xOf_pr₂ P)

  have hpr₂γ : ∀ (γ : ↥Γ) (x : Spec (CommRingCat.of k) ⟶ X n) (ε : (↥O₂ ⧸ I₂) →ₐ[𝒪] k),
      x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ε.toRingHom) →
      (x ≫ (a n (θ γ)).hom) ≫ pr₂ n =
        Spec.map (CommRingCat.ofHom (ε.comp ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toAlgHom).toRingHom) := by
    intro γ x ε hx
    rw [Category.assoc, ha_pr₂, ← Category.assoc, hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  refine ⟨?_, ?_⟩
  ·
    intro η hη
    obtain ⟨⟨x, hx⟩, -⟩ := DQ.fib n k η
    obtain ⟨εr, hεr⟩ := Spec.map_surjective (x ≫ pr₂ n)
    have hqm : (Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le).comp (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})) =
        algebraMap 𝒪 (↥O₂ ⧸ I₂) := by
      ext x; rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Ideal.quotientMap_mk]; rfl
    have hεO : εr.hom.comp (algebraMap 𝒪 (↥O₂ ⧸ I₂)) = algebraMap 𝒪 k := by
      have e1 : x ≫ pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap I₂ (algebraMap 𝒪 ↥O₂) hI₂le)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) := by
        rw [← Category.assoc (pr₂ n), ← (hX n).w, Category.assoc, ← Category.assoc (pr₁ n), ← hxb, ← DQ.p_over n,
          Category.assoc, ← Category.assoc x, hx]
        exact hη
      rw [← Category.assoc, ← hεr, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at e1
      have e2 := Spec.map_injective e1
      have e3 := congrArg CommRingCat.Hom.hom e2
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e3
      rw [← hqm, ← RingHom.comp_assoc]
      exact e3
    let ε : (↥O₂ ⧸ I₂) →ₐ[𝒪] k :=
      { toRingHom := εr.hom, commutes' := fun c => by
          have := congrArg (fun φ : 𝒪 →+* k => φ c) hεO; simpa using this }
    have hxε : x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ε.toRingHom) := by rw [← hεr]; rfl
    obtain ⟨x₁, hx₁p, hx₁pr₂⟩ : ∃ x₁ : Spec (CommRingCat.of k) ⟶ X n,
        x₁ ≫ DQ.p n = η ∧ x₁ ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) := by
      rcases CerednikDrinfeld.FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing 𝒪 hdvr π hπ hcomplete hres hunr
          Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr n (Fr₂ n) (hFr₂ n) k ψ₂ ε with hε | hε
      · exact ⟨x, hx, by rw [hxε, hε]⟩
      · obtain ⟨w, hwΓ, hw⟩ := hodd
        refine ⟨x ≫ (a n (θ ⟨w, hwΓ⟩)).hom, by rw [Category.assoc, DQ.p_inv]; exact hx, ?_⟩
        rw [hpr₂γ ⟨w, hwΓ⟩ x ε hxε, hε]
        have hF : (Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ ((⟨w, hwΓ⟩ : ↥Γ) : G)))) = Fr₂ n := by
          apply hFr₂odd
          rw [Subgroup.coe_mk, hw]
          decide
        rw [hF]
        congr 2
        apply congrArg AlgHom.toRingHom
        apply AlgHom.ext
        intro z
        show ψ₂ ((Fr₂ n) ((Fr₂ n) z)) = ψ₂ z
        rw [hFF]
    have hz : (x₁ ≫ pr₁ n) ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k)) := by
      rw [Category.assoc, ← Category.assoc (pr₁ n), ← hxb, ← DQ.p_over n, Category.assoc, ← Category.assoc x₁, hx₁p]
      exact hη
    obtain ⟨P, hP⟩ := CerednikDrinfeld.FormalOmega.MumfordTower.exists_q_eq_of_isAlgClosed 𝒪 hdvr π hπ hcomplete hres hunr
      K₀ g₁ hg₁ N DM n k hk (x₁ ≫ pr₁ n) hz
    exact ⟨P, by rw [hqdef n k hk ψ ψ₂ hψ₂ P x₁ hP.symm hx₁pr₂, hx₁p]⟩
  ·
    intro P P'
    rw [CerednikDrinfeld.OmegaNr.exists_isTwistedAct_iff_exists_even_isPullback 𝒪 π K₀ Onr Fr hOnr_complete hOnr_max
      hOnr_closed hFr vdet G σ Γ hcent Γ' hΓ' k ψ P P']
    constructor
    · intro hPP'
      rw [hq P, hq P'] at hPP'
      obtain ⟨g, hg⟩ := ((DQ.fib n k (xOf P ≫ DQ.p n)).2 (xOf P) (xOf P') rfl).mp hPP'.symm
      obtain ⟨γ, rfl⟩ := hθsurj g

      have h2 := hpr₂γ γ (xOf P) ψ₂ (xOf_pr₂ P)
      rw [← hg, xOf_pr₂ P'] at h2
      have hcomp : ψ₂ = ψ₂.comp ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toAlgHom := by
        have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
        simp only [CommRingCat.hom_ofHom] at e3
        exact AlgHom.ext fun z => congrArg (fun φ : _ →+* k => φ z) e3
      have heven : Even (Multiplicative.toAdd (vdet (σ (γ : G)))) := by
        by_contra hne
        have hodd' : Odd (- Multiplicative.toAdd (vdet (σ (γ : G)))) := by
          rw [odd_neg]; exact Int.not_even_iff_odd.mp hne
        rw [hFr₂odd _ hodd'] at hcomp
        exact hψ₂Fr hcomp.symm

      have hPP₂ : DeligneDatum.IsPullback (K := K₀) (π := π) k (σ (γ : G))⁻¹ P ((Omega.action K₀ π).act k (σ (γ : G)) P) :=
        (F6cAux.isPullback_iff_eq_act π K₀ k _ P _).mpr rfl
      have h1 := ha_pr₁ n γ k hk P _ hPP₂ (xOf P) (xOf_pr₁ P)
      rw [← hg, xOf_pr₁ P'] at h1
      obtain ⟨h, hhN, hh⟩ := (DM.q_localFib n k hk _ P').mp h1.symm
      obtain ⟨δ, hδ, hδh⟩ := Subgroup.mem_map.mp (hNle hhN)
      have hδh' : Matrix.ProjGenLinGroup.mk (σ δ) = Matrix.ProjGenLinGroup.mk h := by rw [← hρ]; exact hδh
      have hh' := (F6cAux.isPullback_iff_of_mk_eq π K₀ k h (σ δ) hδh'.symm _ P').mp hh
      have htot := F6cAux.isPullback_trans π K₀ k (σ (γ : G)) (σ δ) P _ P' hPP₂ hh'
      obtain ⟨hδΓ, hδeven⟩ := (hΓ' δ).mp hδ
      refine ⟨δ * (γ : G), (hΓ' _).mpr ⟨Γ.mul_mem hδΓ γ.2, ?_⟩, by rwa [map_mul]⟩
      rw [map_mul, map_mul, toAdd_mul]
      exact hδeven.add heven
    · rintro ⟨γ', hγ', hPB⟩
      obtain ⟨hγ'Γ, hγ'even⟩ := (hΓ' γ').mp hγ'
      have h1 : (xOf P ≫ (a n (θ ⟨γ', hγ'Γ⟩)).hom) ≫ pr₁ n = DM.q n k hk P' :=
        ha_pr₁ n ⟨γ', hγ'Γ⟩ k hk P P' hPB (xOf P) (xOf_pr₁ P)
      have h2 : (xOf P ≫ (a n (θ ⟨γ', hγ'Γ⟩)).hom) ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) := by
        rw [hpr₂γ ⟨γ', hγ'Γ⟩ (xOf P) ψ₂ (xOf_pr₂ P), hFr₂even _ (by rw [even_neg]; exact hγ'even)]
        rfl
      rw [hq P, hqdef n k hk ψ ψ₂ hψ₂ P' _ h1 h2, Category.assoc, DQ.p_inv]

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_fib (solution)
