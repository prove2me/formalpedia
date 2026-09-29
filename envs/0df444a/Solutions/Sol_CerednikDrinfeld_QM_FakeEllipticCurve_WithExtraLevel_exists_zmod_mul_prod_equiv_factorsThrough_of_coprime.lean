-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/71a9ce6c-9f29-5cdf-8f75-c0f59cb47930

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    {C' : Scheme.{0}} (lev' : C' ⟶ u.1.A)
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough lev' P ↔
        FactorsThrough u.1.lev (nsmulPt u.1.L t ℓ P) ∧ FactorsThrough u.2.levK (nsmulPt u.1.L t N P))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hk : ((N * ℓ : ℕ) : k) ≠ 0) :
    ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (geomPoint k sk) u.1.f // FactorsThrough lev' P},
      ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
        (e (x + y) : SchemeHomOver (geomPoint k sk) u.1.f) = u.1.L.mul (geomPoint k sk) (e x) (e y) := by
  classical

  letI grp : CommGroup (SchemeHomOver (geomPoint k sk) u.1.f) :=
    { u.1.L.pointGroup (geomPoint k sk) with mul_comm := fun P Q => u.1.comm (geomPoint k sk) P Q }
  have hmul_def : ∀ P Q : SchemeHomOver (geomPoint k sk) u.1.f, P * Q = u.1.L.mul (geomPoint k sk) P Q := fun _ _ => rfl
  have hone_def : (1 : SchemeHomOver (geomPoint k sk) u.1.f) = u.1.L.one (geomPoint k sk) := rfl
  have hpow : ∀ (n : ℕ) (P : SchemeHomOver (geomPoint k sk) u.1.f), nsmulPt u.1.L (geomPoint k sk) n P = P ^ n := by
    intro n P
    induction n with
    | zero => rfl
    | succ n ih =>
      show u.1.L.mul (geomPoint k sk) (nsmulPt u.1.L (geomPoint k sk) n P) P = P ^ (n + 1)
      rw [ih, pow_succ]
      rfl

  have hNℓk : (N : k) ≠ 0 ∧ (ℓ : k) ≠ 0 := by
    rw [Nat.cast_mul] at hk
    exact mul_ne_zero_iff.mp hk
  obtain ⟨eC, heC⟩ := u.1.lev_fibre k sk hNℓk.1
  obtain ⟨eK, heK⟩ := u.2.levK_fibre k sk hNℓk.2

  have heC' : ∀ x y, (eC (x + y)).1 = (eC x).1 * (eC y).1 := fun x y => heC x y
  have heK' : ∀ x y, (eK (x + y)).1 = (eK x).1 * (eK y).1 := fun x y => heK x y
  have heC0 : (eC 0).1 = 1 := by
    have h := heC' 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have heK0 : (eK 0).1 = 1 := by
    have h := heK' 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  let φC : ZMod N × ZMod N →+ Additive (SchemeHomOver (geomPoint k sk) u.1.f) :=
    { toFun := fun x => Additive.ofMul (eC x).1, map_zero' := by simp [heC0], map_add' := fun x y => by simp [heC'] }
  let φK : ZMod ℓ × ZMod ℓ →+ Additive (SchemeHomOver (geomPoint k sk) u.1.f) :=
    { toFun := fun x => Additive.ofMul (eK x).1, map_zero' := by simp [heK0], map_add' := fun x y => by simp [heK'] }
  have heCz : ∀ (z : ℤ) (x : ZMod N × ZMod N), (eC (z • x)).1 = (eC x).1 ^ z := fun z x => by
    have h := map_zsmul φC z x
    exact congrArg Additive.toMul h
  have heKz : ∀ (z : ℤ) (x : ZMod ℓ × ZMod ℓ), (eK (z • x)).1 = (eK x).1 ^ z := fun z x => by
    have h := map_zsmul φK z x
    exact congrArg Additive.toMul h
  have heCn : ∀ (n : ℕ) (x : ZMod N × ZMod N), (eC (n • x)).1 = (eC x).1 ^ n := fun n x => by
    have h := map_nsmul φC n x
    exact congrArg Additive.toMul h
  have heKn : ∀ (n : ℕ) (x : ZMod ℓ × ZMod ℓ), (eK (n • x)).1 = (eK x).1 ^ n := fun n x => by
    have h := map_nsmul φK n x
    exact congrArg Additive.toMul h

  have hCtor : ∀ x : ZMod N × ZMod N, (eC x).1 ^ N = 1 := fun x => by
    rw [← heCn, show N • x = 0 from by ext <;> simp [nsmul_eq_mul], heC0]
  have hKtor : ∀ x : ZMod ℓ × ZMod ℓ, (eK x).1 ^ ℓ = 1 := fun x => by
    rw [← heKn, show ℓ • x = 0 from by ext <;> simp [nsmul_eq_mul], heK0]

  have hCmem : ∀ P : SchemeHomOver (geomPoint k sk) u.1.f, FactorsThrough u.1.lev P ↔ ∃ x, (eC x).1 = P := fun P =>
    ⟨fun h => ⟨eC.symm ⟨P, h⟩, by rw [Equiv.apply_symm_apply]⟩, fun ⟨x, hx⟩ => hx ▸ (eC x).2⟩
  have hKmem : ∀ P : SchemeHomOver (geomPoint k sk) u.1.f, FactorsThrough u.2.levK P ↔ ∃ x, (eK x).1 = P := fun P =>
    ⟨fun h => ⟨eK.symm ⟨P, h⟩, by rw [Equiv.apply_symm_apply]⟩, fun ⟨x, hx⟩ => hx ▸ (eK x).2⟩

  obtain ⟨a, b, hab⟩ : IsCoprime (N : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.mpr hNℓ
  have hkill : ∀ P : SchemeHomOver (geomPoint k sk) u.1.f, P ^ N = 1 → P ^ ℓ = 1 → P = 1 := by
    intro P hPN hPℓ
    calc P = P ^ ((1 : ℤ)) := (zpow_one P).symm
      _ = P ^ (a * N + b * ℓ) := by rw [hab]
      _ = 1 := by
        rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hPN, hPℓ, one_zpow, one_zpow,
          one_mul]
  have hdecomp : ∀ P : SchemeHomOver (geomPoint k sk) u.1.f, P = (P ^ ℓ) ^ b * (P ^ N) ^ a := by
    intro P
    calc P = P ^ ((1 : ℤ)) := (zpow_one P).symm
      _ = P ^ (b * ℓ + a * N) := by rw [add_comm, hab]
      _ = (P ^ ℓ) ^ b * (P ^ N) ^ a := by
        rw [zpow_add, mul_comm b, mul_comm a, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

  let Φ : (ZMod N × ZMod N) × (ZMod ℓ × ZMod ℓ) → SchemeHomOver (geomPoint k sk) u.1.f := fun p => (eC p.1).1 * (eK p.2).1
  have hΦadd : ∀ p q, Φ (p + q) = Φ p * Φ q := by
    intro p q
    show (eC (p.1 + q.1)).1 * (eK (p.2 + q.2)).1 = ((eC p.1).1 * (eK p.2).1) * ((eC q.1).1 * (eK q.2).1)
    rw [heC', heK', mul_mul_mul_comm]
  have hΦmem : ∀ p, FactorsThrough lev' (Φ p) := by
    intro p
    rw [hlev' (geomPoint k sk) (Φ p), hpow, hpow]
    refine ⟨(hCmem _).mpr ⟨ℓ • p.1, ?_⟩, (hKmem _).mpr ⟨N • p.2, ?_⟩⟩
    · show (eC (ℓ • p.1)).1 = ((eC p.1).1 * (eK p.2).1) ^ ℓ
      rw [mul_pow, hKtor, mul_one, heCn]
    · show (eK (N • p.2)).1 = ((eC p.1).1 * (eK p.2).1) ^ N
      rw [mul_pow, hCtor, one_mul, heKn]
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    have h1 : Φ (p - q) = 1 := by
      have h := hΦadd (p - q) q
      rw [sub_add_cancel, hpq] at h
      exact mul_eq_right.mp h.symm
    have h2 : (eC (p - q).1).1 = ((eK (p - q).2).1)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hQ : (eC (p - q).1).1 = 1 := by
      refine hkill _ (hCtor _) ?_
      rw [h2, inv_pow, hKtor, inv_one]
    have hQ' : (eK (p - q).2).1 = 1 := by
      rw [← inv_inj, ← h2, hQ, inv_one]
    have hd1 : (p - q).1 = 0 := eC.injective (Subtype.ext (hQ.trans heC0.symm))
    have hd2 : (p - q).2 = 0 := eK.injective (Subtype.ext (hQ'.trans heK0.symm))
    have hd : p - q = 0 := Prod.ext hd1 hd2
    exact sub_eq_zero.mp hd
  have hΦsurj : ∀ P : SchemeHomOver (geomPoint k sk) u.1.f, FactorsThrough lev' P → ∃ p, Φ p = P := by
    intro P hP
    rw [hlev' (geomPoint k sk) P, hpow, hpow] at hP
    obtain ⟨x, hx⟩ := (hCmem _).mp hP.1
    obtain ⟨y, hy⟩ := (hKmem _).mp hP.2
    refine ⟨(b • x, a • y), ?_⟩
    show (eC (b • x)).1 * (eK (a • y)).1 = P
    rw [heCz, heKz, hx, hy]
    exact (hdecomp P).symm

  let split : ZMod (N * ℓ) × ZMod (N * ℓ) ≃+ (ZMod N × ZMod N) × (ZMod ℓ × ZMod ℓ) :=
    (AddEquiv.prodCongr (ZMod.chineseRemainder hNℓ).toAddEquiv (ZMod.chineseRemainder hNℓ).toAddEquiv).trans
      (AddEquiv.prodProdProdComm (ZMod N) (ZMod ℓ) (ZMod N) (ZMod ℓ))
  let F : ZMod (N * ℓ) × ZMod (N * ℓ) → {P : SchemeHomOver (geomPoint k sk) u.1.f // FactorsThrough lev' P} :=
    fun z => ⟨Φ (split z), hΦmem _⟩
  have hFbij : Function.Bijective F := by
    constructor
    · intro z w h
      exact split.injective (hΦinj (congrArg Subtype.val h))
    · rintro ⟨P, hP⟩
      obtain ⟨p, hp⟩ := hΦsurj P hP
      exact ⟨split.symm p, Subtype.ext (by simp [F, hp])⟩
  refine ⟨Equiv.ofBijective F hFbij, fun x y => ?_⟩
  show Φ (split (x + y)) = Φ (split x) * Φ (split y)
  rw [map_add, hΦadd]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime (solution)
