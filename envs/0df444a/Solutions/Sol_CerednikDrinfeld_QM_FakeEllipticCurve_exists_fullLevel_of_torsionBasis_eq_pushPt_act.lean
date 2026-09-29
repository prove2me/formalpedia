-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fullLevel_of_torsionBasis_eq_pushPt_act
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/069dafee-e3d9-5bc4-9ee9-d3cfeabd3c95

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act

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
    (E : FakeEllipticCurve Λ N S) (m : ℕ)
    (e : Fin 4 → ↥Λ)
    (hgen : ∀ x : ↥Λ, ∃ n : Fin 4 → ℤ, x = ∑ i, n i • e i)
    (hind : ∀ n : Fin 4 → ℤ, ∑ i, n i • e i = 0 → n = 0)
    (Q : Fin 4 → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hQP : ∀ i : Fin 4, Q i = pushPt (E.act (e i)) (E.act_over (e i)) P)
    (hQ :

      (∀ i : Fin 4, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m (Q i) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
        (∀ R : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m R = E.L.one (geomPoint k sk) →
          ∃ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = R) ∧
        (∀ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Q i) k sk) 3)) = E.L.one (geomPoint k sk) →
          ∀ i : Fin 4, m ∣ n i))) :
    ∃ FL : E.FullLevel m, FL.P = P := by
  classical
  obtain ⟨hQi, hQk⟩ := hQ

  have hQ1 : ∀ i, Q i ^ m = 1 := fun i => by rw [← nsmulPt_eq_pow]; exact hQi i

  have htor : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S))) := by
    obtain ⟨c, hc⟩ := hgen ⟨1, hΛ.one_mem⟩
    have hP1 : P = pushPt (E.act ⟨1, hΛ.one_mem⟩) (E.act_over _) P := by
      apply Subtype.ext
      simp only [pushPt, mapPt_coe, E.act_one hΛ.one_mem, Category.comp_id]
    rw [nsmulPt_eq_pow, hP1, pushPt_congr E _ hc, pushPt_sum]
    simp only [← hQP]
    rw [← DbAux.one_def, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hQ1, one_zpow]

  have hsQ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : Fin 4),
      pushPt (E.act (e i)) (E.act_over (e i)) (FakeEllipticCurve.sectionAt P k sk) =
        FakeEllipticCurve.sectionAt (Q i) k sk := by
    intro k _ _ sk i
    rw [← sectionAt_pushPt, ← hQP]
  have hsQ1 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : Fin 4),
      (FakeEllipticCurve.sectionAt (Q i) k sk) ^ m = 1 := by
    intro k _ _ sk i
    rw [← sectionAt_pow, ← nsmulPt_eq_pow, hQi i]
    exact sectionAt_one E k sk
  refine ⟨⟨P, htor, ?_, ?_⟩, rfl⟩
  ·
    intro k _ _ sk R hR
    obtain ⟨n, hn⟩ := (hQk k sk).1 R hR
    refine ⟨∑ i, (n i : ℤ) • e i, ?_⟩
    rw [pushPt_sum]
    simp only [zpow_natCast, hsQ]
    rw [Fin.prod_univ_four, ← nsmulPt_eq_pow, ← nsmulPt_eq_pow, ← nsmulPt_eq_pow, ← nsmulPt_eq_pow]
    exact hn
  ·
    intro k _ _ sk x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := hgen x
      by_cases hm : m = 0
      ·
        exfalso
        subst hm
        set v : Fin 4 → SchemeHomOver (geomPoint k sk) E.f := fun i => FakeEllipticCurve.sectionAt (Q i) k sk with hv
        obtain ⟨n, hn⟩ := (hQk k sk).1 (v 0)⁻¹ rfl
        have hn' : ∏ i, v i ^ n i = (v 0)⁻¹ := (comb_eq E _ v n).symm.trans hn
        rw [Fin.prod_univ_four] at hn'
        have key := (hQk k sk).2 (fun i => n i + if i = 0 then 1 else 0)
          ((comb_eq E _ v (fun i => n i + if i = 0 then 1 else 0)).trans ?_) 0
        · simp at key
        · rw [Fin.prod_univ_four, if_pos rfl, if_neg (by decide : ¬ (1 : Fin 4) = 0),
            if_neg (by decide : ¬ (2 : Fin 4) = 0), if_neg (by decide : ¬ (3 : Fin 4) = 0),
            add_zero, add_zero, add_zero, pow_succ, ← DbAux.one_def]
          calc v 0 ^ n 0 * v 0 * v 1 ^ n 1 * v 2 ^ n 2 * v 3 ^ n 3
              = (v 0 ^ n 0 * v 1 ^ n 1 * v 2 ^ n 2 * v 3 ^ n 3) * v 0 := by
                simp only [mul_assoc, mul_comm, mul_left_comm]
            _ = (v 0)⁻¹ * v 0 := by rw [hn']
            _ = 1 := inv_mul_cancel _
      ·
        have hm0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
        have hmne : (m : ℤ) ≠ 0 := ne_of_gt hm0
        rw [pushPt_congr E _ hz, pushPt_sum] at hx
        simp only [hsQ] at hx

        obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ℕ, ∀ i, ((c i : ℕ) : ℤ) = z i % (m : ℤ) :=
          ⟨fun i => ((z i) % (m : ℤ)).toNat, fun i => Int.toNat_of_nonneg (Int.emod_nonneg _ hmne)⟩
        have hzc : ∀ i, FakeEllipticCurve.sectionAt (Q i) k sk ^ (z i) = FakeEllipticCurve.sectionAt (Q i) k sk ^ (c i) := by
          intro i
          rw [zpow_eq_zpow_emod' (z i) (hsQ1 k sk i), ← hc i, zpow_natCast]
        simp only [hzc] at hx
        have hdiv := (hQk k sk).2 c ((comb_eq E _ (fun i => FakeEllipticCurve.sectionAt (Q i) k sk) c).trans hx)

        have hw : ∀ i, ∃ w : ℤ, z i = m * w := by
          intro i
          have hci : c i < m := by
            have h1 : ((c i : ℕ) : ℤ) < m := by rw [hc i]; exact Int.emod_lt_of_pos _ hm0
            exact_mod_cast h1
          have hc0 : c i = 0 := Nat.eq_zero_of_dvd_of_lt (hdiv i) hci
          have hz0 : z i % m = 0 := by rw [← hc i, hc0]; simp
          exact Int.dvd_of_emod_eq_zero hz0
        choose w hw using hw
        refine ⟨∑ i, w i • e i, ?_⟩
        rw [hz]
        have : (∑ i, z i • e i : ↥Λ) = (m : ℤ) • ∑ i, w i • e i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hw i, smul_smul]
        rw [this, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    · rintro ⟨y, hy⟩
      have hxy : x = (m : ℤ) • y := by
        apply Subtype.ext
        rw [hy, Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
      rw [hxy, pushPt_zsmul, zpow_natCast, ← pushPt_pow, ← sectionAt_pow, ← nsmulPt_eq_pow, htor]
      change pushPt (E.act y) (E.act_over y) (FakeEllipticCurve.sectionAt (1 : SchemeHomOver _ E.f) k sk) = 1
      rw [sectionAt_one, pushPt_one]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fullLevel_of_torsionBasis_eq_pushPt_act (solution)
