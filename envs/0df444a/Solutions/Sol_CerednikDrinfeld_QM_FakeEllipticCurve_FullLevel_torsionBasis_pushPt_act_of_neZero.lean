-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.torsionBasis_pushPt_act_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/b7ab2808-2ede-561a-83ee-9b61463230b2

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_torsionBasis_pushPt_act_of_neZero

set_option autoImplicit false
universe u
open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace DbAux

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

@[reducible] noncomputable def ptGroup (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) : CommGroup (SchemeHomOver t E.f) :=
  { E.L.pointGroup t with mul_comm := fun x y => E.comm t x y }

attribute [local instance] ptGroup

section
variable (E : FakeEllipticCurve Λ N S) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem mul_def (x y : SchemeHomOver t E.f) : x * y = E.L.mul t x y := rfl
theorem one_def : (1 : SchemeHomOver t E.f) = E.L.one t := rfl

theorem nsmulPt_eq_pow (n : ℕ) (R : SchemeHomOver t E.f) : nsmulPt E.L t n R = R ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
      rw [pow_succ, show nsmulPt E.L t (n + 1) R = E.L.mul t (nsmulPt E.L t n R) R from rfl, ih]
      rfl

noncomputable def actPt (x : ↥Λ) : SchemeHomOver t E.f →* SchemeHomOver t E.f :=
  MonoidHom.mk' (fun P => pushPt (E.act x) (E.act_over x) P) (E.act_hom x t)

theorem actPt_apply (x : ↥Λ) (P : SchemeHomOver t E.f) : actPt E t x P = pushPt (E.act x) (E.act_over x) P := rfl

theorem pushPt_congr {x y : ↥Λ} (h : x = y) (R : SchemeHomOver t E.f) :
    pushPt (E.act x) (E.act_over x) R = pushPt (E.act y) (E.act_over y) R := by
  subst h; rfl

theorem pushPt_zero (R : SchemeHomOver t E.f) : pushPt (E.act 0) (E.act_over 0) R = 1 := by
  have h := E.act_add 0 0 t R
  rw [pushPt_congr E t (add_zero (0 : ↥Λ))] at h
  change _ = pushPt (E.act 0) (E.act_over 0) R * pushPt (E.act 0) (E.act_over 0) R at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

noncomputable def orbitHom (R : SchemeHomOver t E.f) : Multiplicative ↥Λ →* SchemeHomOver t E.f :=
  { toFun := fun x => pushPt (E.act (Multiplicative.toAdd x)) (E.act_over (Multiplicative.toAdd x)) R
    map_one' := pushPt_zero E t R
    map_mul' := fun x y => E.act_add (Multiplicative.toAdd x) (Multiplicative.toAdd y) t R }

theorem orbitHom_ofAdd (R : SchemeHomOver t E.f) (x : ↥Λ) :
    orbitHom E t R (Multiplicative.ofAdd x) = pushPt (E.act x) (E.act_over x) R := rfl

theorem pushPt_nsmul (R : SchemeHomOver t E.f) (n : ℕ) (x : ↥Λ) :
    pushPt (E.act (n • x)) (E.act_over (n • x)) R = (pushPt (E.act x) (E.act_over x) R) ^ n := by
  rw [← orbitHom_ofAdd, ← orbitHom_ofAdd, ofAdd_nsmul, map_pow]

theorem pushPt_zsmul (R : SchemeHomOver t E.f) (z : ℤ) (x : ↥Λ) :
    pushPt (E.act (z • x)) (E.act_over (z • x)) R = (pushPt (E.act x) (E.act_over x) R) ^ z := by
  rw [← orbitHom_ofAdd, ← orbitHom_ofAdd, ofAdd_zsmul, map_zpow]

theorem comb_eq (v : Fin 4 → SchemeHomOver t E.f) (c : Fin 4 → ℕ) :
    E.L.mul t (E.L.mul t (E.L.mul t (nsmulPt E.L t (c 0) (v 0)) (nsmulPt E.L t (c 1) (v 1)))
      (nsmulPt E.L t (c 2) (v 2))) (nsmulPt E.L t (c 3) (v 3)) = ∏ i, v i ^ c i := by
  rw [Fin.prod_univ_four, nsmulPt_eq_pow, nsmulPt_eq_pow, nsmulPt_eq_pow, nsmulPt_eq_pow]
  rfl

theorem pushPt_sum (R : SchemeHomOver t E.f) (c : Fin 4 → ℤ) (e : Fin 4 → ↥Λ) :
    pushPt (E.act (∑ i, c i • e i)) (E.act_over (∑ i, c i • e i)) R =
      ∏ i, (pushPt (E.act (e i)) (E.act_over (e i)) R) ^ (c i) := by
  rw [← orbitHom_ofAdd, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, orbitHom_ofAdd]

theorem pushPt_pow (x : ↥Λ) (P : SchemeHomOver t E.f) (n : ℕ) :
    pushPt (E.act x) (E.act_over x) (P ^ n) = (pushPt (E.act x) (E.act_over x) P) ^ n :=
  map_pow (actPt E t x) P n

theorem pushPt_one (x : ↥Λ) : pushPt (E.act x) (E.act_over x) (1 : SchemeHomOver t E.f) = 1 :=
  map_one (actPt E t x)

end

section
variable (E : FakeEllipticCurve Λ N S) (k : Type u) [Field k] (sk : S →+* k)

theorem sectionAt_pushPt (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    FakeEllipticCurve.sectionAt (pushPt (E.act x) (E.act_over x) P) k sk =
      pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) := by
  apply Subtype.ext
  simp only [FakeEllipticCurve.sectionAt, pushPt, mapPt_coe, schemeHomOverComp_coe, Category.assoc]

theorem sectionAt_mul (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    FakeEllipticCurve.sectionAt (P * Q) k sk = FakeEllipticCurve.sectionAt P k sk * FakeEllipticCurve.sectionAt Q k sk :=
  E.L.mul_natural _ _ _ _ P Q

theorem sectionAt_one :
    FakeEllipticCurve.sectionAt (1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) k sk = 1 :=
  E.L.one_natural _ _ _ _

noncomputable def sectionAtHom :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f →* SchemeHomOver (geomPoint k sk) E.f :=
  { toFun := fun P => FakeEllipticCurve.sectionAt P k sk
    map_one' := sectionAt_one E k sk
    map_mul' := sectionAt_mul E k sk }

theorem sectionAt_pow (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) (n : ℕ) :
    FakeEllipticCurve.sectionAt (P ^ n) k sk = (FakeEllipticCurve.sectionAt P k sk) ^ n :=
  map_pow (sectionAtHom E k sk) P n

theorem sectionAt_nsmulPt (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f) :
    FakeEllipticCurve.sectionAt (nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) n P) k sk =
      nsmulPt E.L (geomPoint k sk) n (FakeEllipticCurve.sectionAt P k sk) := by
  rw [nsmulPt_eq_pow, nsmulPt_eq_pow, sectionAt_pow]

end

end DbAux

attribute [local instance] DbAux.ptGroup

open DbAux in

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) [NeZero m] (P : E.FullLevel m)
    (e : Fin 4 → ↥Λ)
    (hgen : ∀ x : ↥Λ, ∃ n : Fin 4 → ℤ, x = ∑ i, n i • e i)
    (hind : ∀ n : Fin 4 → ℤ, ∑ i, n i • e i = 0 → n = 0) :
      let Pe : Fin 4 → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f :=
        fun i => pushPt (E.act (e i)) (E.act_over (e i)) P.P

      (∀ i : Fin 4, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m (Pe i) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
        (∀ R : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m R = E.L.one (geomPoint k sk) →
          ∃ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 3)) = R) ∧
        (∀ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 3)) = E.L.one (geomPoint k sk) →
          ∀ i : Fin 4, m ∣ n i)) := by
  classical
  intro Pe
  have hPe : ∀ i, Pe i = pushPt (E.act (e i)) (E.act_over (e i)) P.P := fun i => rfl
  have hm : m ≠ 0 := NeZero.ne m
  have hm0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmne : (m : ℤ) ≠ 0 := ne_of_gt hm0

  have hP1 : P.P ^ m = 1 := by rw [← nsmulPt_eq_pow]; exact P.torsion
  have hPe1 : ∀ i, Pe i ^ m = 1 := fun i => by rw [hPe, ← pushPt_pow, hP1, pushPt_one]
  refine ⟨fun i => by rw [nsmulPt_eq_pow, hPe1]; rfl, fun k _ _ sk => ?_⟩

  have hw : ∀ i, FakeEllipticCurve.sectionAt (Pe i) k sk =
      pushPt (E.act (e i)) (E.act_over (e i)) (FakeEllipticCurve.sectionAt P.P k sk) := fun i => by
    rw [hPe, sectionAt_pushPt]
  have hw1 : ∀ i, pushPt (E.act (e i)) (E.act_over (e i)) (FakeEllipticCurve.sectionAt P.P k sk) ^ m = 1 := fun i => by
    rw [← hw, ← sectionAt_pow, hPe1, sectionAt_one]
  constructor
  ·
    intro R hR
    obtain ⟨x, hx⟩ := P.generates k sk R hR
    obtain ⟨z, hz⟩ := hgen x
    obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, ∀ i, ((c i : ℕ) : ℤ) = z i % (m : ℤ) :=
      ⟨fun i => ((z i) % (m : ℤ)).toNat, fun i => Int.toNat_of_nonneg (Int.emod_nonneg _ hmne)⟩
    refine ⟨c, (comb_eq E _ (fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) c).trans ?_⟩
    show ∏ i, FakeEllipticCurve.sectionAt (Pe i) k sk ^ c i = R
    rw [← hx, pushPt_congr E _ hz, pushPt_sum]
    simp only [hw]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod' (z i) (hw1 i), ← hc i, zpow_natCast]
  ·
    intro n hn i
    have hn' : ∏ i, FakeEllipticCurve.sectionAt (Pe i) k sk ^ n i = 1 := (comb_eq E _ (fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) n).symm.trans hn
    simp only [hw] at hn'
    have hx1 : pushPt (E.act (∑ i, (n i : ℤ) • e i)) (E.act_over _) (FakeEllipticCurve.sectionAt P.P k sk) =
        E.L.one (geomPoint k sk) := by
      rw [pushPt_sum]; simp only [zpow_natCast]; exact hn'
    obtain ⟨y, hy⟩ := (P.annihilator k sk _).mp hx1
    obtain ⟨u, hu⟩ := hgen y
    have hΛ1 : (∑ i, (n i : ℤ) • e i : ↥Λ) = (m : ℤ) • y := by
      apply Subtype.ext
      rw [hy, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    have hΛ2 : (∑ i, ((n i : ℤ) - m * u i) • e i : ↥Λ) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hΛ1, hu, Finset.smul_sum, smul_smul, sub_self]
    have h3 := congr_fun (hind _ hΛ2) i
    simp only [Pi.zero_apply, sub_eq_zero] at h3
    exact Int.natCast_dvd_natCast.mp ⟨u i, h3⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_torsionBasis_pushPt_act_of_neZero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_torsionBasis_pushPt_act_of_neZero (solution)
