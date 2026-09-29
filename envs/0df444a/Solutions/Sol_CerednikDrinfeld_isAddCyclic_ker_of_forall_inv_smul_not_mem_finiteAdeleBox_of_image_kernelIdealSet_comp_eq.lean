-- Prove2me | solution 1 for CerednikDrinfeld.isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/343af3cb-7a48-5f73-8486-957f4ebfdf84

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox
import Theorems.Thm_Submodule_fg_and_span_eq_top_ofFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

set_option autoImplicit false

namespace Ws47
namespace C0B1

section Group

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem natCard_ker_comp (f : A →+ B) (hf : Function.Surjective f) (g : B →+ C) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by

  let φ : (g.comp f).ker →+ g.ker :=
    { toFun := fun x => ⟨f x.1, by
        have := x.2; rw [AddMonoidHom.mem_ker] at this ⊢; exact this⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, by rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]; exact hy⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have h := x.2; rw [AddMonoidHom.mem_ker] at h
          exact (AddMonoidHom.mem_ker).mpr (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).mp x.2, map_zero]⟩,
          by rw [AddMonoidHom.mem_ker]; exact Subtype.ext ((AddMonoidHom.mem_ker).mp x.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv, Nat.mul_comm]

end Group

section Curve

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem natCard_torsion_eq_sq (E : WeierstrassCurve κ) [E.IsElliptic] (n : ℕ) (hn : (n : κ) ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} = n ^ 2 := by
  obtain ⟨L, -, -, hcard, -⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (F := κ) (Ω := κ) E (n := n) hn
  have hL : ∀ t : κ, t ∈ L := fun t => by simpa using L.algebraMap_mem t
  have hLinj : Function.Injective (L.val : ↥L →ₐ[κ] κ) := L.val.toRingHom.injective
  let φ : (E.baseChange ↥L).toAffine.Point →+ (E.baseChange κ).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E) L.val
  have hinj : Function.Injective φ := WeierstrassCurve.Affine.Point.map_injective (W' := E) L.val
  have hsurj : Function.Surjective φ := by
    rintro (_ | ⟨u, v, h⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨.some ⟨u, hL u⟩ ⟨v, hL v⟩ ((WeierstrassCurve.Affine.baseChange_nonsingular E hLinj ⟨u, hL u⟩ ⟨v, hL v⟩).mp h), rfl⟩
  rw [← hcard]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun P : {P : (E.baseChange ↥L).toAffine.Point // n • P = 0} =>
      (⟨φ P.1, by rw [← map_nsmul, P.2, map_zero]⟩ : {P : (E.baseChange κ).toAffine.Point // n • P = 0}))
    ⟨fun P Q hPQ => Subtype.ext (hinj (congrArg Subtype.val hPQ)), fun Q => ?_⟩)).symm
  obtain ⟨P, hP⟩ := hsurj Q.1
  refine ⟨⟨P, hinj ?_⟩, Subtype.ext hP⟩
  rw [map_nsmul, hP, Q.2, map_zero]

theorem isAddCyclic_of_forall_not_torsion_le (E : WeierstrassCurve κ) [E.IsElliptic]
    (K : AddSubgroup E.toAffine.Point) [Finite K]
    (hchar : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → (p : κ) ≠ 0)
    (hprim : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → ¬ ∀ P : E.toAffine.Point, p • P = 0 → P ∈ K) :
    IsAddCyclic K := by
  classical

  let T : ℕ → AddSubgroup E.toAffine.Point := fun n =>
    { carrier := {P | P ∈ K ∧ n • P = 0}
      zero_mem' := ⟨K.zero_mem, by simp⟩
      add_mem' := fun {x y} hx hy => ⟨K.add_mem hx.1 hy.1, by rw [nsmul_add, hx.2, hy.2, add_zero]⟩
      neg_mem' := fun {x} hx => ⟨K.neg_mem hx.1, by rw [smul_neg, hx.2, neg_zero]⟩ }
  have hTmem : ∀ n P, P ∈ T n ↔ P ∈ K ∧ n • P = 0 := fun n P => Iff.rfl
  have hTle : ∀ n, T n ≤ K := fun n P hP => hP.1
  haveI hTfin : ∀ n, Finite (T n) := fun n => Finite.of_injective _ (AddSubgroup.inclusion_injective (hTle n))

  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → Nat.card (T p) ≤ p := by
    intro p hp hpK
    let Ep : AddSubgroup E.toAffine.Point :=
      { carrier := {P | p • P = 0}
        zero_mem' := by simp
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at *; rw [nsmul_add, hx, hy, add_zero]
        neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx, neg_zero] }
    have hEp : Nat.card Ep = p ^ 2 := by
      rw [← natCard_torsion_eq_sq E p (hchar p hp hpK)]
      exact Nat.card_congr (Equiv.refl _)
    haveI : Finite Ep := Nat.finite_of_card_ne_zero (by rw [hEp]; exact pow_ne_zero 2 hp.ne_zero)
    have hle : T p ≤ Ep := fun P hP => hP.2
    have hdvd : Nat.card (T p) ∣ p ^ 2 := hEp ▸ AddSubgroup.card_dvd_of_le hle
    have hne : Nat.card (T p) ≠ p ^ 2 := by
      intro h
      apply hprim p hp hpK
      intro P hP
      have heq : T p = Ep := AddSubgroup.eq_of_le_of_card_ge hle (by rw [h, hEp])
      have : P ∈ T p := by rw [heq]; exact hP
      exact this.1
    obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases i
    · rw [hcard, pow_zero]; exact hp.one_lt.le
    · rw [hcard, pow_one]
    · exact absurd hcard hne

  have hall : ∀ g : ℕ, 0 < g → (∀ p : ℕ, p.Prime → p ∣ g → p ∣ Nat.card K) → Nat.card (T g) ≤ g := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro hg hgK
      by_cases hg1 : g = 1
      · subst hg1
        have : T 1 = ⊥ := by
          rw [eq_bot_iff]; intro P hP; exact (AddSubgroup.mem_bot).mpr (by simpa using hP.2)
        rw [this, AddSubgroup.card_bot]
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1
      obtain ⟨g', rfl⟩ := hpg
      have hg' : 0 < g' := Nat.pos_of_mul_pos_left hg
      have hlt : g' < p * g' := lt_mul_left hg' hp.one_lt
      let f : T (p * g') →+ T p :=
        { toFun := fun P => ⟨g' • P.1, ⟨K.nsmul_mem P.2.1 g', by
              have h : (p * g') • (P : E.toAffine.Point) = 0 := P.2.2
              rwa [smul_smul]⟩⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      have hkerle : Nat.card f.ker ≤ Nat.card (T g') := by
        refine Nat.card_le_card_of_injective (fun P => (⟨P.1.1, ⟨P.1.2.1, ?_⟩⟩ : T g')) ?_
        · have h := P.2; rw [AddMonoidHom.mem_ker] at h; exact congrArg Subtype.val h
        · intro P Q h
          have h' := congrArg (fun x : T g' => (x : E.toAffine.Point)) h
          exact Subtype.ext (Subtype.ext h')
      have h1 := ih g' hlt hg' (fun r hr hrg' => hgK r hr (Dvd.dvd.mul_left hrg' p))
      have h2 := hprime p hp (hgK p hp (Dvd.intro g' rfl))
      calc Nat.card (T (p * g')) = Nat.card f.ker * Nat.card f.range := by
              rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
                Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, Nat.mul_comm]
        _ ≤ Nat.card (T g') * Nat.card (T p) :=
              Nat.mul_le_mul hkerle (Nat.card_le_card_of_injective _ (AddSubgroup.subtype_injective f.range))
        _ ≤ g' * p := Nat.mul_le_mul h1 h2
        _ = p * g' := Nat.mul_comm _ _

  haveI : Fintype K := Fintype.ofFinite K
  apply isAddCyclic_of_card_nsmul_eq_zero_le
  intro n hn
  set g := Nat.gcd n (Nat.card K) with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgle : g ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left _ _)
  have hKg : ∀ a : K, n • a = 0 → g • (a : E.toAffine.Point) = 0 := by
    intro a ha
    have hbez : (g : ℤ) = n * Nat.gcdA n (Nat.card K) + (Nat.card K : ℕ) * Nat.gcdB n (Nat.card K) :=
      Nat.gcd_eq_gcd_ab n (Nat.card K)
    have h1 : n • (a : E.toAffine.Point) = 0 := by rw [← AddSubgroup.coe_nsmul, ha]; rfl
    have h2 : (Nat.card K) • (a : E.toAffine.Point) = 0 := by
      rw [← AddSubgroup.coe_nsmul, card_nsmul_eq_zero']; rfl
    have : (g : ℤ) • (a : E.toAffine.Point) = 0 := by
      rw [hbez, add_zsmul, mul_comm (n : ℤ), mul_comm ((Nat.card K : ℕ) : ℤ), mul_zsmul, mul_zsmul,
        natCast_zsmul, natCast_zsmul, h1, h2, zsmul_zero, zsmul_zero, add_zero]
    rwa [natCast_zsmul] at this
  have hinj : (Finset.univ.filter fun a : K => n • a = 0).card ≤ Nat.card (T g) := by
    rw [← Fintype.card_coe]
    rw [Fintype.card_eq_nat_card]
    refine Nat.card_le_card_of_injective
      (fun a => (⟨(a.1 : E.toAffine.Point), ⟨a.1.2, hKg a.1 (Finset.mem_filter.mp a.2).2⟩⟩ : T g)) ?_
    intro a b h
    have h' := congrArg (fun x : T g => (x : E.toAffine.Point)) h
    exact Subtype.ext (Subtype.ext h')
  exact hinj.trans ((hall g hgpos (fun p hp hpg => hpg.trans (Nat.gcd_dvd_right _ _))).trans hgle)

end Curve

section Dual

variable {κ : Type} [Field κ] [DecidableEq κ]

theorem dualPair_comp (W₀ W₁ W₂ : WeierstrassCurve κ)
    (φ₁ : W₀.toAffine.Point →+ W₁.toAffine.Point) (φ₁' : W₁.toAffine.Point →+ W₀.toAffine.Point)
    (φ₂ : W₁.toAffine.Point →+ W₂.toAffine.Point) (φ₂' : W₂.toAffine.Point →+ W₁.toAffine.Point)
    (n₁ n₂ : ℕ)
    (h₁ : φ₁ ∈ WeierstrassCurve.rationalHomSet κ W₀ W₁) (h₁' : φ₁' ∈ WeierstrassCurve.rationalHomSet κ W₁ W₀)
    (h₂ : φ₂ ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (h₂' : φ₂' ∈ WeierstrassCurve.rationalHomSet κ W₂ W₁)
    (hd₁ : φ₁'.comp φ₁ = n₁ • AddMonoidHom.id _) (hd₁' : φ₁.comp φ₁' = n₁ • AddMonoidHom.id _)
    (hd₂ : φ₂'.comp φ₂ = n₂ • AddMonoidHom.id _) (hd₂' : φ₂.comp φ₂' = n₂ • AddMonoidHom.id _) :
    φ₂.comp φ₁ ∈ WeierstrassCurve.rationalHomSet κ W₀ W₂ ∧ φ₁'.comp φ₂' ∈ WeierstrassCurve.rationalHomSet κ W₂ W₀ ∧
      (φ₁'.comp φ₂').comp (φ₂.comp φ₁) = (n₁ * n₂) • AddMonoidHom.id _ ∧
      (φ₂.comp φ₁).comp (φ₁'.comp φ₂') = (n₁ * n₂) • AddMonoidHom.id _ := by
  refine ⟨WeierstrassCurve.comp_mem_rationalHomSet κ W₀ W₁ W₂ h₁ h₂,
    WeierstrassCurve.comp_mem_rationalHomSet κ W₂ W₁ W₀ h₂' h₁', ?_, ?_⟩
  · ext P
    show φ₁' (φ₂' (φ₂ (φ₁ P))) = (n₁ * n₂) • P
    have e2 : φ₂' (φ₂ (φ₁ P)) = n₂ • φ₁ P := by
      have := congrArg (fun f : W₁.toAffine.Point →+ W₁.toAffine.Point => f (φ₁ P)) hd₂; simpa using this
    have e1 : φ₁' (φ₁ P) = n₁ • P := by
      have := congrArg (fun f : W₀.toAffine.Point →+ W₀.toAffine.Point => f P) hd₁; simpa using this
    rw [e2, map_nsmul, e1, ← mul_nsmul, Nat.mul_comm]
  · ext P
    show φ₂ (φ₁ (φ₁' (φ₂' P))) = (n₁ * n₂) • P
    have e1 : φ₁ (φ₁' (φ₂' P)) = n₁ • φ₂' P := by
      have := congrArg (fun f : W₁.toAffine.Point →+ W₁.toAffine.Point => f (φ₂' P)) hd₁'; simpa using this
    have e2 : φ₂ (φ₂' P) = n₂ • P := by
      have := congrArg (fun f : W₂.toAffine.Point →+ W₂.toAffine.Point => f P) hd₂'; simpa using this
    rw [e1, map_nsmul, e2, ← mul_nsmul, Nat.mul_comm]

end Dual

section Step

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem step_cyclic (W₀ : WeierstrassCurve κ) [W₀.IsElliptic] {W₁ W₂ : Type*} [AddCommGroup W₁] [AddCommGroup W₂]
    (ψ : W₀.toAffine.Point →+ W₁) (hψs : Function.Surjective ψ) (φ : W₁ →+ W₂)
    (n r : ℕ) (hcyc : IsAddCyclic ψ.ker) (hn : Nat.card ψ.ker = n) (hr : Nat.card φ.ker = r) (hrp : r.Prime)
    (hchar : ((n * r : ℕ) : κ) ≠ 0)
    (hnb : ¬ ∀ P : W₀.toAffine.Point, r • P = 0 → P ∈ (φ.comp ψ).ker) :
    IsAddCyclic (φ.comp ψ).ker ∧ Nat.card (φ.comp ψ).ker = n * r := by
  classical
  have hcard : Nat.card (φ.comp ψ).ker = n * r := by rw [natCard_ker_comp ψ hψs φ, hn, hr]
  have hn0 : n ≠ 0 := fun h => by apply hchar; rw [h, zero_mul, Nat.cast_zero]
  haveI : Finite ψ.ker := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0)
  haveI : Finite (φ.comp ψ).ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact mul_ne_zero hn0 hrp.ne_zero)
  refine ⟨isAddCyclic_of_forall_not_torsion_le W₀ (φ.comp ψ).ker ?_ ?_, hcard⟩
  ·
    intro p hp hpd hp0
    apply hchar
    rw [hcard] at hpd
    obtain ⟨c, hc⟩ := hpd
    rw [hc, Nat.cast_mul, hp0, zero_mul]
  · intro p hp hpd hall
    rw [hcard] at hpd
    by_cases hpr : p = r
    · subst hpr; exact hnb hall
    ·
      have hpn : p ∣ n := (Or.resolve_right ((Nat.Prime.dvd_mul hp).mp hpd)
        (fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hrp).mp h)))
      have hp0 : (p : κ) ≠ 0 := by
        intro h; apply hchar
        obtain ⟨c, hc⟩ := hpn
        rw [hc, Nat.cast_mul, Nat.cast_mul, h, zero_mul, zero_mul]

      let T : AddSubgroup W₀.toAffine.Point :=
        { carrier := {P | p • P = 0}
          zero_mem' := by simp
          add_mem' := fun {x y} hx hy => by
            simp only [Set.mem_setOf_eq] at *; rw [nsmul_add, hx, hy, add_zero]
          neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx, neg_zero] }
      have hT : Nat.card T = p ^ 2 := by
        rw [← natCard_torsion_eq_sq W₀ p hp0]; exact Nat.card_congr (Equiv.refl _)
      haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; exact pow_ne_zero 2 hp.ne_zero)

      let g : T →+ φ.ker :=
        { toFun := fun P => ⟨ψ P.1, by
            have := hall P.1 P.2
            rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at this
            exact (AddMonoidHom.mem_ker).mpr this⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }

      have hker_le : Nat.card g.ker ≤ p := by

        have hsub : Nat.card g.ker ≤ Nat.card {x : ψ.ker // p • x = 0} := by
          refine Nat.card_le_card_of_injective
            (fun P => ⟨⟨P.1.1, ?_⟩, ?_⟩) ?_
          · have h := P.2; rw [AddMonoidHom.mem_ker] at h
            exact (AddMonoidHom.mem_ker).mpr (congrArg Subtype.val h)
          · exact Subtype.ext (P.1.2)
          · intro P Q h
            have h' := congrArg (fun x : {x : ψ.ker // p • x = 0} => ((x : ψ.ker) : W₀.toAffine.Point)) h
            exact Subtype.ext (Subtype.ext h')
        refine hsub.trans ?_
        haveI : Fintype ψ.ker := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        exact IsAddCyclic.card_nsmul_eq_zero_le hp.pos
      have hrange_dvd : Nat.card g.range ∣ r := hr ▸ AddSubgroup.card_addSubgroup_dvd_card g.range
      have hrange_dvd' : Nat.card g.range ∣ p ^ 2 := by
        have := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
        rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hT] at this
        exact Dvd.intro _ this.symm
      have hrange1 : Nat.card g.range = 1 := by
        have h1 : Nat.card g.range ∣ Nat.gcd r (p ^ 2) := Nat.dvd_gcd hrange_dvd hrange_dvd'
        have hcop : Nat.Coprime r (p ^ 2) :=
          (Nat.Coprime.pow_right 2 ((Nat.coprime_primes hrp hp).mpr (Ne.symm hpr)))
        rw [Nat.Coprime.gcd_eq_one hcop] at h1
        exact Nat.dvd_one.mp h1
      have hTeq : Nat.card T = Nat.card g.ker * Nat.card g.range := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, Nat.mul_comm]
      rw [hT, hrange1, mul_one] at hTeq
      have : p ^ 2 ≤ p := hTeq ▸ hker_le
      have hp2 : p < p ^ 2 := by nlinarith [hp.one_lt]
      omega

end Step

end Ws47.C0B1

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace Ws47
namespace DictCyc

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem exists_coprime_nsmul_eq_zero (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (E : WeierstrassCurve κ) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, q' • P = 0 → P = 0) (k : ℕ) (hk : k ≠ 0) :
    ∃ m : ℕ, (m : κ) ≠ 0 ∧ ∀ P : E.toAffine.Point, k • P = 0 → m • P = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hq : q' ∣ k
    · obtain ⟨k', rfl⟩ := hq
      have hk' : k' ≠ 0 := fun h => hk (by rw [h, mul_zero])
      have hlt : k' < q' * k' := lt_mul_left (Nat.pos_of_ne_zero hk') (Fact.out : q'.Prime).one_lt
      obtain ⟨m, hm, hP⟩ := ih k' hlt hk'
      refine ⟨m, hm, fun P hP0 => hP P ?_⟩
      apply hss
      rw [smul_smul]; exact hP0
    · refine ⟨k, ?_, fun P hP => hP⟩
      intro h; exact hq ((CharP.cast_eq_zero_iff κ q' k).mp h)

variable {a b : ℚ}

theorem mem_star_image_smul_iff (d : (ℍ[ℚ, a, b])ˣ) (J : Submodule ℤ ℍ[ℚ, a, b]) (w : ℍ[ℚ, a, b]) :
    w ∈ star '' ((d • J : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔
      ∃ z ∈ J, w = star ((d : ℍ[ℚ, a, b]) * z) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    exact ⟨j, hj, by rw [smul_eq_mul]⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(d : ℍ[ℚ, a, b]) * z, ?_, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨z, hz, by rw [smul_eq_mul]⟩

theorem isAddCyclic_ker_of_forall_inv_smul_not_mem
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W')
    (hKJ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * g) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → ((ℓ : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) ∉ Submodule.finiteAdeleBox Λ₁) :
    IsAddCyclic ψ.ker := by
  classical
  have hΛo : IsOrder Λ₁ := hΛ₁.isOrder
  set I := Submodule.ofFiniteIdele Λ₁ x with hIdef
  set J := Submodule.ofFiniteIdele Λ₁ (x * g) with hJdef

  have hssW : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 :=
    WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero q' X₁ hss W χ hχ hχ0

  have hJne : ∃ z ∈ J, z ≠ 0 := by
    obtain ⟨-, hspan⟩ := Submodule.fg_and_span_eq_top_ofFiniteIdele Λ₁ hΛo.fg hΛo.spanTop (x * g)
    by_contra hcon
    push Not at hcon
    have hbot : (J : Set ℍ[ℚ, a, b]) ⊆ {0} := fun z hz => hcon z hz
    have : Submodule.span ℚ (J : Set ℍ[ℚ, a, b]) ≤ Submodule.span ℚ {0} := Submodule.span_mono hbot
    rw [hspan, Submodule.span_zero_singleton, top_le_iff] at this
    have h1 : (1 : ℍ[ℚ, a, b]) ∈ (⊥ : Submodule ℚ ℍ[ℚ, a, b]) := by rw [this]; trivial
    exact one_ne_zero ((Submodule.mem_bot ℚ).mp h1)
  have hψ0 : ψ ≠ 0 := by
    intro h0
    obtain ⟨z, hz, hz0⟩ := hJne
    have hw : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) := by
      rw [hKJ, mem_star_image_smul_iff]; exact ⟨z, hz, rfl⟩
    obtain ⟨e, ⟨ρ', -, he⟩, hθe⟩ := hw
    have he0 : e = 0 := by
      apply Subtype.ext
      rw [he, h0]
      ext P
      show ρ' ((0 : W.toAffine.Point →+ W'.toAffine.Point) (χ P)) = ((0 : ↥(WeierstrassCurve.rationalEndSubring κ X₁)) : AddMonoid.End (X₁.baseChange κ).toAffine.Point) P
      rw [AddMonoidHom.zero_apply]; exact (map_zero ρ').trans rfl
    rw [he0, map_zero] at hθe
    have : (d : ℍ[ℚ, a, b]) * z = 0 := by rw [← star_star ((d : ℍ[ℚ, a, b]) * z), ← hθe, star_zero]
    exact hz0 ((Units.mul_right_eq_zero d).mp this)

  obtain ⟨m, hmκ, hmker⟩ : ∃ m : ℕ, (m : κ) ≠ 0 ∧ ∀ P : W.toAffine.Point, ψ P = 0 → m • P = 0 := by
    obtain ⟨σ, -, n₀, hn₀, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ W W' hψ hψ0
    obtain ⟨m, hm, hP⟩ := exists_coprime_nsmul_eq_zero q' W hssW n₀.toNat (by omega)
    refine ⟨m, hm, fun P hP0 => hP P ?_⟩
    have h1 := hdual.comp_left P
    have h2 : σ (ψ P) = σ 0 := congrArg σ hP0
    have h3 : σ 0 = n₀ • P := h2.symm.trans h1
    rw [map_zero] at h3
    rw [← natCast_zsmul, Int.toNat_of_nonneg hn₀.le]; exact h3.symm
  have hm0 : m ≠ 0 := fun h => hmκ (by rw [h, Nat.cast_zero])
  have hcardT := C0B1.natCard_torsion_eq_sq W m hmκ
  haveI : Finite {P : W.toAffine.Point // m • P = 0} := Nat.finite_of_card_ne_zero (by rw [hcardT]; exact pow_ne_zero 2 hm0)
  haveI hfin : Finite ψ.ker :=
    Finite.of_injective (fun P : ψ.ker => (⟨P.1, hmker P.1 P.2⟩ : {P : W.toAffine.Point // m • P = 0}))
      (by
        intro P Q h
        have h' := congrArg (fun x : {P : W.toAffine.Point // m • P = 0} => x.1) h
        exact Subtype.ext h')
  have hkerdvd : Nat.card ψ.ker ∣ m ^ 2 := by
    rw [← hcardT]
    let T : AddSubgroup W.toAffine.Point :=
      { carrier := {P | m • P = 0}
        zero_mem' := by simp
        add_mem' := fun {x y} hx hy => by simp only [Set.mem_setOf_eq] at *; rw [nsmul_add, hx, hy, add_zero]
        neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx, neg_zero] }
    have hle : ψ.ker ≤ T := fun P hP => hmker P hP
    have : Nat.card T = Nat.card {P : W.toAffine.Point // m • P = 0} := Nat.card_congr (Equiv.refl _)
    rw [← this]; exact AddSubgroup.card_dvd_of_le hle

  have hstep : ∀ (p : ℕ) (β : W.toAffine.Point →+ W'.toAffine.Point), β ∈ WeierstrassCurve.rationalHomSet κ W W' →
      (∀ P, ψ P = (p : ℤ) • β P) → J ≤ ((p : ℕ) : ℤ) • I := by
    intro p β hβ hψβ z hz

    have hw : star ((d : ℍ[ℚ, a, b]) * z) ∈ θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) := by
      rw [hKJ, mem_star_image_smul_iff]; exact ⟨z, hz, rfl⟩
    obtain ⟨e, ⟨ρ', hρ', he⟩, hθe⟩ := hw

    have hρ'β : ρ'.comp β ∈ WeierstrassCurve.rationalHomSet κ W X₁ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W W' X₁ hβ hρ'
    have hmemE : ((ρ'.comp β).comp χ : AddMonoid.End (X₁.baseChange κ).toAffine.Point) ∈
        WeierstrassCurve.rationalEndSubring κ X₁ :=
      Subring.subset_closure (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W X₁ hχ hρ'β)
    set e' : ↥(WeierstrassCurve.rationalEndSubring κ X₁) := ⟨(ρ'.comp β).comp χ, hmemE⟩ with he'def
    have he'K : e' ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ := ⟨ρ'.comp β, hρ'β, rfl⟩
    have hθe' : θ₁ e' ∈ star '' ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
      rw [← hK]; exact ⟨e', he'K, rfl⟩
    obtain ⟨z', hz', hθz'⟩ := (mem_star_image_smul_iff d I _).mp hθe'

    have hee' : e = p • e' := by
      apply Subtype.ext
      rw [he]
      show (ρ'.comp (ψ.comp χ) : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = ((p • e' : ↥(WeierstrassCurve.rationalEndSubring κ X₁)) : AddMonoid.End _)
      rw [AddSubmonoidClass.coe_nsmul]
      ext P
      show ρ' (ψ (χ P)) = (p • ((ρ'.comp β).comp χ : AddMonoid.End (X₁.baseChange κ).toAffine.Point)) P
      rw [hψβ]
      refine (map_zsmul ρ' (p : ℤ) (β (χ P))).trans ?_
      rw [natCast_zsmul]
      rfl
    have : star ((d : ℍ[ℚ, a, b]) * z) = p • star ((d : ℍ[ℚ, a, b]) * z') := by
      rw [← hθe, hee', map_nsmul, hθz']
    have hz_eq : (d : ℍ[ℚ, a, b]) * z = (d : ℍ[ℚ, a, b]) * (p • z') := by
      rw [← star_star ((d : ℍ[ℚ, a, b]) * z), this, star_nsmul, star_star, mul_smul_comm]
    have hz_eq' : z = ((p : ℕ) : ℤ) • z' := by
      rw [natCast_zsmul]; exact (Units.mul_right_inj d).mp hz_eq
    rw [hz_eq']
    exact Submodule.smul_mem_pointwise_smul _ _ _ hz'

  apply C0B1.isAddCyclic_of_forall_not_torsion_le W ψ.ker
  · intro p hp hpd hpκ
    have hpm : p ∣ m := Nat.Prime.dvd_of_dvd_pow hp (hpd.trans hkerdvd)
    apply hmκ
    obtain ⟨c, hc⟩ := hpm
    rw [hc, Nat.cast_mul, hpκ, zero_mul]
  · intro p hp hpd hall
    have hpm : p ∣ m := Nat.Prime.dvd_of_dvd_pow hp (hpd.trans hkerdvd)
    have hpκ : (p : κ) ≠ 0 := by
      intro h; apply hmκ
      obtain ⟨c, hc⟩ := hpm
      rw [hc, Nat.cast_mul, h, zero_mul]
    haveI : NeZero p := ⟨hp.ne_zero⟩

    obtain ⟨β, hβ, hψβ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W W' hpκ hψ
      (fun P hP => (AddMonoidHom.mem_ker).mp (hall P (by rw [← natCast_zsmul]; exact hP)))
    have hJI : J ≤ ((p : ℕ) : ℤ) • I := hstep p β hβ (fun P => hψβ P)
    exact hprim p hp ((IsOrder.ofFiniteIdele_mul_le_zsmul_ofFiniteIdele_iff_inv_smul_mem_finiteAdeleBox hΛo x g p).mp hJI)

end Ws47.DictCyc

open scoped Quaternion TensorProduct NumberField Pointwise in
open QuaternionAlgebra CerednikDrinfeld in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (W : WeierstrassCurve κ) [W.IsElliptic] (χ : X₁.toAffine.Point →+ W.toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ)
    (hK : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hg : ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (W' : WeierstrassCurve κ) [W'.IsElliptic] (ψ : W.toAffine.Point →+ W'.toAffine.Point)
    (hψ : ψ ∈ WeierstrassCurve.rationalHomSet κ W W') (ψ' : W'.toAffine.Point →+ W.toAffine.Point)
    (hψ' : ψ' ∈ WeierstrassCurve.rationalHomSet κ W' W)
    (hψd : ψ'.comp ψ = Nat.card ψ.ker • AddMonoidHom.id _ ∧ ψ.comp ψ' = Nat.card ψ.ker • AddMonoidHom.id _)
    (hKJ : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W' (ψ.comp χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * g) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → ((ℓ : ℚ)⁻¹ • ((g : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) ∉ Submodule.finiteAdeleBox Λ₁) :
    IsAddCyclic ψ.ker :=
  Ws47.DictCyc.isAddCyclic_ker_of_forall_inv_smul_not_mem q' X₁ hss Λ₁ hΛ₁ θ₁ hθ₁ x W χ hχ hχ0 d hK g W' ψ hψ hKJ hprim

end S_CerednikDrinfeld_isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_isAddCyclic_ker_of_forall_inv_smul_not_mem_finiteAdeleBox_of_image_kernelIdealSet_comp_eq (solution)
