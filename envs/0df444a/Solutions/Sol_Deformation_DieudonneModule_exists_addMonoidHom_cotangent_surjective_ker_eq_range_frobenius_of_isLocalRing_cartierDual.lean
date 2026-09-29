-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1fe84769-2fc5-50b1-962e-876aa2536411

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Theorems.Thm_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.verschiebung TruncWitt.coeff_verschiebung_zero TruncWitt.coeff_verschiebung_succ TruncWitt.frobeniusFun TruncWitt.coeff_frobeniusFun TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung wittHomFrobenius wittHomFrobenius_verschiebung wittHomVerschiebung_frobenius wittHomShift wittHomRestrict wittHomShift_verschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.of_shift DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.lift DieudonneModule.lift_of DieudonneModule.hom_ext DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.frobenius_verschiebung TruncWitt.eq_zero_of_length_zero UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shift UnipotentWittCovector.of_injective UnipotentWittCovector.verschiebung UnipotentWittCovector.verschiebung_of UnipotentWittCovector.frobenius UnipotentWittCovector.frobenius_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convOne DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual"
p2m_open "Deformation"
namespace CotangentAux

open MvPolynomial in

theorem prod_pow_eq_of_forall_mul_eq_zero {T : Type*} [CommRing T]
    (d : (Fin 2 × ℕ) →₀ ℕ) (F : Fin 2 × ℕ → T)
    (hF : ∀ a b : Fin 2 × ℕ, a.1 = 0 → b.1 ≠ 0 → F a * F b = 0) :
    (d.prod fun a e => F a ^ e) =
      (d.prod fun a e => (if a.1 = 0 then F a else 0) ^ e) +
        (d.prod fun a e => (if a.1 = 0 then 0 else F a) ^ e) -
          d.prod fun _ e => (0 : T) ^ e := by
  classical
  by_cases h1 : ∃ b ∈ d.support, b.1 ≠ 0
  · by_cases h0 : ∃ a ∈ d.support, a.1 = 0
    · obtain ⟨a, ha, ha0⟩ := h0
      obtain ⟨b, hb, hb1⟩ := h1
      have hab : b ≠ a := fun h => hb1 (h ▸ ha0)
      have hda : d a ≠ 0 := Finsupp.mem_support_iff.1 ha
      have hdb : d b ≠ 0 := Finsupp.mem_support_iff.1 hb
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hda
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hdb
      have e1 : (d.prod fun a e => F a ^ e) = 0 := by
        unfold Finsupp.prod
        rw [← Finset.mul_prod_erase _ (fun x => F x ^ d x) ha]
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun x => F x ^ d x)
          (Finset.mem_erase.2 ⟨hab, hb⟩)
        rw [hc]
        show F a ^ d a * (F b ^ d b * c) = 0
        rw [hm, hk, pow_succ, pow_succ]
        linear_combination (F a ^ m * (F b ^ k * c)) * hF a b ha0 hb1
      have e2 : (d.prod fun a e => (if a.1 = 0 then F a else 0) ^ e) = 0 := by
        unfold Finsupp.prod
        exact Finset.prod_eq_zero hb (by
          show (if b.1 = 0 then F b else 0) ^ d b = 0
          rw [if_neg hb1, zero_pow hdb])
      have e3 : (d.prod fun a e => (if a.1 = 0 then 0 else F a) ^ e) = 0 := by
        unfold Finsupp.prod
        exact Finset.prod_eq_zero ha (by
          show (if a.1 = 0 then 0 else F a) ^ d a = 0
          rw [if_pos ha0, zero_pow hda])
      have e4 : (d.prod fun _ e => (0 : T) ^ e) = 0 := by
        unfold Finsupp.prod
        exact Finset.prod_eq_zero ha (by
          show (0 : T) ^ d a = 0
          rw [zero_pow hda])
      rw [e1, e2, e3, e4]; ring
    · push Not at h0
      have e1 : (d.prod fun a e => F a ^ e) = d.prod fun a e => (if a.1 = 0 then 0 else F a) ^ e :=
        Finsupp.prod_congr fun x hx => by
          show F x ^ d x = (if x.1 = 0 then 0 else F x) ^ d x
          rw [if_neg (h0 x hx)]
      have e2 : (d.prod fun a e => (if a.1 = 0 then F a else 0) ^ e) =
          d.prod fun _ e => (0 : T) ^ e :=
        Finsupp.prod_congr fun x hx => by
          show (if x.1 = 0 then F x else 0) ^ d x = (0 : T) ^ d x
          rw [if_neg (h0 x hx)]
      rw [e1, e2]; ring
  · push Not at h1
    have e1 : (d.prod fun a e => F a ^ e) = d.prod fun a e => (if a.1 = 0 then F a else 0) ^ e :=
      Finsupp.prod_congr fun x hx => by
        show F x ^ d x = (if x.1 = 0 then F x else 0) ^ d x
        rw [if_pos (h1 x hx)]
    have e2 : (d.prod fun a e => (if a.1 = 0 then 0 else F a) ^ e) =
        d.prod fun _ e => (0 : T) ^ e :=
      Finsupp.prod_congr fun x hx => by
        show (if x.1 = 0 then 0 else F x) ^ d x = (0 : T) ^ d x
        rw [if_pos (h1 x hx)]
    rw [e1, e2]; ring

open MvPolynomial in

theorem aeval_eq_of_forall_mul_eq_zero {T : Type*} [CommRing T]
    (φ : MvPolynomial (Fin 2 × ℕ) ℤ) (F : Fin 2 × ℕ → T)
    (hF : ∀ a b : Fin 2 × ℕ, a.1 = 0 → b.1 ≠ 0 → F a * F b = 0) :
    aeval F φ =
      aeval (fun a => if a.1 = 0 then F a else 0) φ +
        aeval (fun a => if a.1 = 0 then 0 else F a) φ - aeval (fun _ => (0 : T)) φ := by
  induction φ using MvPolynomial.induction_on' with
  | monomial d a =>
    simp only [aeval_monomial]
    rw [prod_pow_eq_of_forall_mul_eq_zero d F hF]
    ring
  | add φ ψ hφ hψ => rw [map_add, map_add, map_add, map_add, hφ, hψ]; ring

private theorem _root_.WittVector.coeff_add_of_forall_mul_eq_zero {p : ℕ} [Fact p.Prime]
    {T : Type*} [CommRing T] (x y : WittVector p T)
    (h : ∀ i j : ℕ, x.coeff i * y.coeff j = 0) (n : ℕ) :
    (x + y).coeff n = x.coeff n + y.coeff n := by
  have key : ∀ u v : WittVector p T, (u + v).coeff n =
      MvPolynomial.aeval (Function.uncurry ![u.coeff, v.coeff]) (WittVector.wittAdd p n) :=
    fun u v => WittVector.add_coeff u v n
  have hF : ∀ a b : Fin 2 × ℕ, a.1 = 0 → b.1 ≠ 0 →
      Function.uncurry ![x.coeff, y.coeff] a * Function.uncurry ![x.coeff, y.coeff] b = 0 := by
    rintro ⟨a1, i⟩ ⟨b1, j⟩ ha hb
    fin_cases a1 <;> fin_cases b1 <;> simp_all [Function.uncurry]
  have e1 : (fun a : Fin 2 × ℕ => if a.1 = 0 then Function.uncurry ![x.coeff, y.coeff] a else 0) =
      Function.uncurry ![x.coeff, (0 : WittVector p T).coeff] := by
    funext ⟨b, i⟩; fin_cases b <;> simp [Function.uncurry]
  have e2 : (fun a : Fin 2 × ℕ => if a.1 = 0 then 0 else Function.uncurry ![x.coeff, y.coeff] a) =
      Function.uncurry ![(0 : WittVector p T).coeff, y.coeff] := by
    funext ⟨b, i⟩; fin_cases b <;> simp [Function.uncurry]
  have e3 : (fun _ : Fin 2 × ℕ => (0 : T)) =
      Function.uncurry ![(0 : WittVector p T).coeff, (0 : WittVector p T).coeff] := by
    funext ⟨b, i⟩; fin_cases b <;> simp [Function.uncurry]
  rw [key x y, aeval_eq_of_forall_mul_eq_zero _ _ hF, e1, e2, e3, ← key, ← key, ← key,
    add_zero, zero_add, add_zero, WittVector.zero_coeff, sub_zero]

p2m_alias "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.WittVector.coeff_add_of_forall_mul_eq_zero" "WittVector.coeff_add_of_forall_mul_eq_zero"

private theorem _root_.TruncatedWittVector.coeff_add_of_forall_mul_eq_zero {p : ℕ} [Fact p.Prime] {n : ℕ}
    {T : Type*} [CommRing T] (x y : TruncatedWittVector p n T)
    (h : ∀ i j : Fin n, x.coeff i * y.coeff j = 0) (i : Fin n) :
    (x + y).coeff i = x.coeff i + y.coeff i := by
  have hx : WittVector.truncate n x.out = x := TruncatedWittVector.truncateFun_out x
  have hy : WittVector.truncate n y.out = y := TruncatedWittVector.truncateFun_out y
  have hout : ∀ (z : TruncatedWittVector p n T) (j : ℕ), n ≤ j → z.out.coeff j = 0 := by
    intro z j hj
    simp only [TruncatedWittVector.out, dif_neg (not_lt.2 hj)]
  have h' : ∀ a b : ℕ, x.out.coeff a * y.out.coeff b = 0 := by
    intro a b
    by_cases ha : a < n
    · by_cases hb : b < n
      · have := h ⟨a, ha⟩ ⟨b, hb⟩
        rwa [← TruncatedWittVector.coeff_out x ⟨a, ha⟩, ← TruncatedWittVector.coeff_out y ⟨b, hb⟩]
          at this
      · rw [hout y b (not_lt.1 hb), mul_zero]
    · rw [hout x a (not_lt.1 ha), zero_mul]
  rw [← hx, ← hy, ← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate,
    WittVector.coeff_truncate, WittVector.coeff_add_of_forall_mul_eq_zero _ _ h']

p2m_alias "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.TruncatedWittVector.coeff_add_of_forall_mul_eq_zero" "TruncatedWittVector.coeff_add_of_forall_mul_eq_zero"
end CotangentAux
end Deformation

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.verschiebung TruncWitt.coeff_verschiebung_zero TruncWitt.coeff_verschiebung_succ TruncWitt.frobeniusFun TruncWitt.coeff_frobeniusFun TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung wittHomFrobenius wittHomFrobenius_verschiebung wittHomVerschiebung_frobenius wittHomShift wittHomRestrict wittHomShift_verschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.of_shift DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.lift DieudonneModule.lift_of DieudonneModule.hom_ext DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.frobenius_verschiebung TruncWitt.eq_zero_of_length_zero UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shift UnipotentWittCovector.of_injective UnipotentWittCovector.verschiebung UnipotentWittCovector.verschiebung_of UnipotentWittCovector.frobenius UnipotentWittCovector.frobenius_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convOne DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual"
p2m_open "Deformation"
namespace CotangentAux

section Theta

variable (p : ℕ) [hp : Fact p.Prime] (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B]

theorem coeff_mem_ker {n : ℕ} (x : wittHom (ZMod p) p n B) (i : Fin n) :
    (x : TruncatedWittVector p n B).coeff i ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) :=
  (RingHom.mem_ker).2 (counit_coeff_of_mem_wittHom x.2 i)

theorem mem_augIdeal_iff (a : B) :
    a ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) ↔ Coalgebra.counit (R := ZMod p) a = 0 := by
  rw [RingHom.mem_ker]
  rfl

theorem coeff_add_sub_mem_sq {n : ℕ} (x y : wittHom (ZMod p) p n B) (i : Fin n) :
    ((x + y : wittHom (ZMod p) p n B) : TruncatedWittVector p n B).coeff i -
        ((x : TruncatedWittVector p n B).coeff i + (y : TruncatedWittVector p n B).coeff i) ∈
      RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) ^ 2 := by
  set I := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)
  set π := Ideal.Quotient.mk (I ^ 2)
  have hA := TruncatedWittVector.coeff_add_of_forall_mul_eq_zero
    (TruncWitt.map π (x : TruncatedWittVector p n B)) (TruncWitt.map π (y : TruncatedWittVector p n B))
    (fun a b => by
      rw [TruncWitt.coeff_map, TruncWitt.coeff_map, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        pow_two]
      exact Ideal.mul_mem_mul (coeff_mem_ker p B x a) (coeff_mem_ker p B y b)) i
  rw [← map_add, TruncWitt.coeff_map, TruncWitt.coeff_map, TruncWitt.coeff_map] at hA
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, AddSubgroup.coe_add, hA, sub_self]

noncomputable def thetaLevel : (n : ℕ) →
    (wittHom (ZMod p) p n B →+ (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent)
  | 0 => 0
  | (m + 1) =>
    { toFun := fun x => (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent
        ⟨(x : TruncatedWittVector p (m + 1) B).coeff (Fin.last m), coeff_mem_ker p B x _⟩
      map_zero' := by
        rw [Ideal.toCotangent_eq_zero]
        change ((0 : wittHom (ZMod p) p (m + 1) B) : TruncatedWittVector p (m + 1) B).coeff
          (Fin.last m) ∈ _
        rw [ZeroMemClass.coe_zero, TruncatedWittVector.coeff_zero]
        exact zero_mem _
      map_add' := fun x y => by
        rw [← map_add, Ideal.toCotangent_eq]
        exact coeff_add_sub_mem_sq p B x y (Fin.last m) }

theorem thetaLevel_succ_apply (m : ℕ) (x : wittHom (ZMod p) p (m + 1) B) :
    thetaLevel p B (m + 1) x = (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent
      ⟨(x : TruncatedWittVector p (m + 1) B).coeff (Fin.last m), coeff_mem_ker p B x _⟩ := rfl

theorem thetaLevel_shift (n : ℕ) (x : wittHom (ZMod p) p n B) :
    thetaLevel p B (n + 1) (wittHomShift (ZMod p) p n B x) = thetaLevel p B n x := by
  cases n with
  | zero =>
    rw [thetaLevel_succ_apply]
    change _ = (0 : (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent)
    rw [Ideal.toCotangent_eq_zero]
    change (TruncWitt.shift (x : TruncatedWittVector p 0 B)).coeff (Fin.last 0) ∈ _
    rw [Fin.last_zero, TruncWitt.coeff_shift_zero]
    exact zero_mem _
  | succ m =>
    rw [thetaLevel_succ_apply, thetaLevel_succ_apply]
    congr 2
    change (TruncWitt.shift (x : TruncatedWittVector p (m + 1) B)).coeff (Fin.last (m + 1)) = _
    rw [← Fin.succ_last, TruncWitt.coeff_shift_succ]

noncomputable def theta :
    DieudonneModule (ZMod p) p B →+ (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent :=
  DieudonneModule.lift (ZMod p) p B (thetaLevel p B) (thetaLevel_shift p B)

theorem theta_of {n : ℕ} (x : wittHom (ZMod p) p n B) :
    theta p B (DieudonneModule.of (ZMod p) p B n x) = thetaLevel p B n x :=
  DieudonneModule.lift_of _ _ _

theorem theta_of_succ {m : ℕ} (x : wittHom (ZMod p) p (m + 1) B) :
    theta p B (DieudonneModule.of (ZMod p) p B (m + 1) x) =
      (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent
        ⟨(x : TruncatedWittVector p (m + 1) B).coeff (Fin.last m), coeff_mem_ker p B x _⟩ := by
  rw [theta_of, thetaLevel_succ_apply]

theorem theta_frobenius (z : DieudonneModule (ZMod p) p B) :
    theta p B (DieudonneModule.frobenius (ZMod p) p B z) = 0 := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [DieudonneModule.frobenius_of, theta_of]
    cases n with
    | zero => rfl
    | succ m =>
      rw [thetaLevel_succ_apply, Ideal.toCotangent_eq_zero]
      change (TruncWitt.frobeniusFun (x : TruncatedWittVector p (m + 1) B)).coeff (Fin.last m) ∈ _
      rw [TruncWitt.coeff_frobeniusFun]
      exact Ideal.pow_le_pow_right hp.out.two_le (Ideal.pow_mem_pow (coeff_mem_ker p B x _) p)

end Theta

end CotangentAux
end Deformation

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.verschiebung TruncWitt.coeff_verschiebung_zero TruncWitt.coeff_verschiebung_succ TruncWitt.frobeniusFun TruncWitt.coeff_frobeniusFun TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung wittHomFrobenius wittHomFrobenius_verschiebung wittHomVerschiebung_frobenius wittHomShift wittHomRestrict wittHomShift_verschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.of_shift DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.lift DieudonneModule.lift_of DieudonneModule.hom_ext DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.frobenius_verschiebung TruncWitt.eq_zero_of_length_zero UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shift UnipotentWittCovector.of_injective UnipotentWittCovector.verschiebung UnipotentWittCovector.verschiebung_of UnipotentWittCovector.frobenius UnipotentWittCovector.frobenius_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convOne DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual"
p2m_open "Deformation"
namespace CotangentAux

section Points

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B]

theorem algHom_apply_eq_counit (hBloc : IsLocalRing B) (χ : B →ₐ[ZMod p] ZMod p) (b : B) :
    χ b = Coalgebra.counit b := by
  have h1 : RingHom.ker χ = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective χ fun r => ⟨algebraMap (ZMod p) B r, by simp⟩)
  have h2 : RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom (ZMod p) B)
        fun r => ⟨algebraMap (ZMod p) B r, by simp⟩)
  have hb : b - algebraMap (ZMod p) B (Coalgebra.counit b) ∈ RingHom.ker χ := by
    rw [h1, ← h2, RingHom.mem_ker]
    simp
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hb
  exact hb

end Points

section Phi

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B]

local notation "𝕊" => DualNumber (ZMod p)

variable (lam : DieudonneModule (ZMod p) p B →+ ZMod p)

noncomputable def lamVec (n : ℕ) (x : wittHom (ZMod p) p n B) : TruncatedWittVector p n 𝕊 :=
  TruncatedWittVector.mk p fun i : Fin n =>
    TrivSqZeroExt.inr (lam (DieudonneModule.of (ZMod p) p B n
      ((wittHomVerschiebung (ZMod p) p n B)^[n - 1 - i] x)))

@[scoped simp] theorem coeff_lamVec (n : ℕ) (x : wittHom (ZMod p) p n B) (i : Fin n) :
    (lamVec lam n x).coeff i = TrivSqZeroExt.inr (lam (DieudonneModule.of (ZMod p) p B n
      ((wittHomVerschiebung (ZMod p) p n B)^[n - 1 - i] x))) :=
  TruncatedWittVector.coeff_mk _ _

theorem lamVec_add (n : ℕ) (x y : wittHom (ZMod p) p n B) :
    lamVec lam n (x + y) = lamVec lam n x + lamVec lam n y := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_add_of_forall_mul_eq_zero _ _ (fun a b => by
    rw [coeff_lamVec, coeff_lamVec, TrivSqZeroExt.inr_mul_inr])]
  rw [coeff_lamVec, coeff_lamVec, coeff_lamVec, iterate_map_add, map_add, map_add,
    TrivSqZeroExt.inr_add]

noncomputable def phiLevel (n : ℕ) : wittHom (ZMod p) p n B →+ UnipotentWittCovector p 𝕊 :=
  AddMonoidHom.mk' (fun x => UnipotentWittCovector.of p 𝕊 n (lamVec lam n x)) fun x y => by
    simp only [lamVec_add, map_add]

theorem phiLevel_apply (n : ℕ) (x : wittHom (ZMod p) p n B) :
    phiLevel lam n x = UnipotentWittCovector.of p 𝕊 n (lamVec lam n x) := rfl

theorem iterate_verschiebung_shift (n k : ℕ) (x : wittHom (ZMod p) p n B) :
    (wittHomVerschiebung (ZMod p) p (n + 1) B)^[k] (wittHomShift (ZMod p) p n B x) =
      wittHomShift (ZMod p) p n B ((wittHomVerschiebung (ZMod p) p n B)^[k] x) :=
  (Function.Semiconj.iterate_right (f := wittHomShift (ZMod p) p n B)
    (ga := wittHomVerschiebung (ZMod p) p n B) (gb := wittHomVerschiebung (ZMod p) p (n + 1) B)
    (fun y => wittHomShift_verschiebung y) k x).symm

theorem lamVec_shift (n : ℕ) (x : wittHom (ZMod p) p n B) :
    lamVec lam (n + 1) (wittHomShift (ZMod p) p n B x) = TruncWitt.shift (lamVec lam n x) := by
  refine TruncatedWittVector.ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [coeff_lamVec, TruncWitt.coeff_shift_zero, iterate_verschiebung_shift,
      DieudonneModule.of_shift]
    have : n + 1 - 1 - ((0 : Fin (n + 1)) : ℕ) = n := by simp
    rw [this, wittHomVerschiebung_iterate_eq_zero, map_zero, map_zero, TrivSqZeroExt.inr_zero]
  · rw [coeff_lamVec, TruncWitt.coeff_shift_succ, coeff_lamVec, iterate_verschiebung_shift,
      DieudonneModule.of_shift]
    have : n + 1 - 1 - (j.succ : ℕ) = n - 1 - j := by simp; omega
    rw [this]

noncomputable def phi : DieudonneModule (ZMod p) p B →+ UnipotentWittCovector p 𝕊 :=
  DieudonneModule.lift (ZMod p) p B (phiLevel lam) fun n x => by
    rw [phiLevel_apply, phiLevel_apply, lamVec_shift, UnipotentWittCovector.of_shift]

theorem phi_of (n : ℕ) (x : wittHom (ZMod p) p n B) :
    phi lam (DieudonneModule.of (ZMod p) p B n x) =
      UnipotentWittCovector.of p 𝕊 n (lamVec lam n x) := by
  rw [phi, DieudonneModule.lift_of, phiLevel_apply]

theorem coeff_verschiebung_succ' {R : Type*} [CommRing R] {n : ℕ}
    (v : TruncatedWittVector p (n + 1) R) (j : Fin n) :
    (TruncWitt.verschiebung v).coeff j.succ = v.coeff j.castSucc :=
  TruncWitt.coeff_verschiebung_succ v j j.succ.isLt

theorem lamVec_verschiebung (n : ℕ) (x : wittHom (ZMod p) p n B) :
    lamVec lam n (wittHomVerschiebung (ZMod p) p n B x) = TruncWitt.verschiebung (lamVec lam n x) := by
  cases n with
  | zero => exact TruncatedWittVector.ext fun i => i.elim0
  | succ m =>
    refine TruncatedWittVector.ext fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [coeff_lamVec, ← Function.iterate_succ_apply, TruncWitt.coeff_verschiebung_zero]
      have e : (m + 1 - 1 - ((0 : Fin (m + 1)) : ℕ)).succ = m + 1 := by simp
      rw [e, wittHomVerschiebung_iterate_eq_zero, map_zero, map_zero, TrivSqZeroExt.inr_zero]
    · rw [coeff_lamVec, ← Function.iterate_succ_apply, coeff_verschiebung_succ', coeff_lamVec]
      have hj := j.isLt
      have e : (m + 1 - 1 - (j.succ : ℕ)).succ = m + 1 - 1 - (j.castSucc : ℕ) := by
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.succ_eq_add_one]
        omega
      rw [e]

theorem phi_verschiebung (z : DieudonneModule (ZMod p) p B) :
    phi lam (DieudonneModule.verschiebung (ZMod p) p B z) =
      UnipotentWittCovector.verschiebung p 𝕊 (phi lam z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [DieudonneModule.verschiebung_of, phi_of, phi_of, UnipotentWittCovector.verschiebung_of,
      lamVec_verschiebung]

theorem frobenius_verschiebung_comm (n : ℕ) (x : wittHom (ZMod p) p n B) :
    wittHomFrobenius (ZMod p) p n B (wittHomVerschiebung (ZMod p) p n B x) =
      wittHomVerschiebung (ZMod p) p n B (wittHomFrobenius (ZMod p) p n B x) := by
  rw [wittHomFrobenius_verschiebung, wittHomVerschiebung_frobenius]

theorem lamVec_frobenius (hlam : ∀ w, lam (DieudonneModule.frobenius (ZMod p) p B w) = 0)
    (n : ℕ) (x : wittHom (ZMod p) p n B) :
    lamVec lam n (wittHomFrobenius (ZMod p) p n B x) = 0 := by
  refine TruncatedWittVector.ext fun i => ?_
  have hc : (wittHomVerschiebung (ZMod p) p n B)^[n - 1 - i] (wittHomFrobenius (ZMod p) p n B x) =
      wittHomFrobenius (ZMod p) p n B ((wittHomVerschiebung (ZMod p) p n B)^[n - 1 - i] x) :=
    (Function.Commute.iterate_right (f := wittHomFrobenius (ZMod p) p n B)
      (g := wittHomVerschiebung (ZMod p) p n B) (frobenius_verschiebung_comm n) (n - 1 - i) x).symm
  rw [coeff_lamVec, TruncatedWittVector.coeff_zero, hc, ← DieudonneModule.frobenius_of, hlam,
    TrivSqZeroExt.inr_zero]

theorem frobeniusFun_lamVec (n : ℕ) (x : wittHom (ZMod p) p n B) :
    TruncWitt.frobeniusFun (lamVec lam n x) = 0 := by
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncWitt.coeff_frobeniusFun, coeff_lamVec, TruncatedWittVector.coeff_zero]
  exact pow_eq_zero_of_le hp.out.two_le (by rw [pow_two, TrivSqZeroExt.inr_mul_inr])

theorem phi_frobenius (hlam : ∀ w, lam (DieudonneModule.frobenius (ZMod p) p B w) = 0)
    (z : DieudonneModule (ZMod p) p B) :
    phi lam (DieudonneModule.frobenius (ZMod p) p B z) =
      UnipotentWittCovector.frobenius (ZMod p) p 𝕊 (phi lam z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [DieudonneModule.frobenius_of, phi_of, phi_of, UnipotentWittCovector.frobenius_of,
      lamVec_frobenius lam hlam, frobeniusFun_lamVec]

theorem apply_coeff_last_eq_of_eval_eq_phi (f : B →ₐ[ZMod p] 𝕊)
    (hf : DieudonneModule.eval (ZMod p) p f = phi lam) (m : ℕ)
    (x : wittHom (ZMod p) p (m + 1) B) :
    f ((x : TruncatedWittVector p (m + 1) B).coeff (Fin.last m)) =
      TrivSqZeroExt.inr (lam (DieudonneModule.of (ZMod p) p B (m + 1) x)) := by
  have h := DFunLike.congr_fun hf (DieudonneModule.of (ZMod p) p B (m + 1) x)
  rw [DieudonneModule.eval_of, phi_of] at h
  have h' := congrArg (TruncatedWittVector.coeff (Fin.last m))
    (UnipotentWittCovector.of_injective (m + 1) h)
  rw [TruncWitt.coeff_map, coeff_lamVec] at h'
  have e : m + 1 - 1 - ((Fin.last m : Fin (m + 1)) : ℕ) = 0 := by simp
  rw [e, Function.iterate_zero_apply] at h'
  exact h'

end Phi

end CotangentAux
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux"
end Deformation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.verschiebung TruncWitt.coeff_verschiebung_zero TruncWitt.coeff_verschiebung_succ TruncWitt.frobeniusFun TruncWitt.coeff_frobeniusFun TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung wittHomFrobenius wittHomFrobenius_verschiebung wittHomVerschiebung_frobenius wittHomShift wittHomRestrict wittHomShift_verschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.of_shift DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.lift DieudonneModule.lift_of DieudonneModule.hom_ext DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.frobenius_verschiebung TruncWitt.eq_zero_of_length_zero UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shift UnipotentWittCovector.of_injective UnipotentWittCovector.verschiebung UnipotentWittCovector.verschiebung_of UnipotentWittCovector.frobenius UnipotentWittCovector.frobenius_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convOne DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual"
p2m_open "Deformation"
namespace CotangentAux

section DerivPoint

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B]

local notation "𝕊" => DualNumber (ZMod p)

variable (p) in

noncomputable def projKer : B →+ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) where
  toFun b := ⟨b - algebraMap (ZMod p) B (Coalgebra.counit b), by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    exact sub_self _⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by
    simp only [AddMemClass.coe_add, map_add]
    ring)

theorem coe_projKer (b : B) :
    (projKer p b : B) = b - algebraMap (ZMod p) B (Coalgebra.counit b) := rfl

theorem projKer_of_mem (b : B) (hb : b ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)) :
    projKer p b = ⟨b, hb⟩ :=
  Subtype.ext (by
    rw [coe_projKer, (mem_augIdeal_iff p B b).1 hb, map_zero, sub_zero])

variable (δ : (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent →ₗ[ZMod p] ZMod p)

noncomputable def derivOf : B →+ ZMod p :=
  δ.toAddMonoidHom.comp
    ((RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent.toAddMonoidHom.comp (projKer p))

theorem derivOf_apply (b : B) :
    derivOf δ b = δ ((RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent (projKer p b)) :=
  rfl

theorem derivOf_algebraMap (r : ZMod p) : derivOf δ (algebraMap (ZMod p) B r) = 0 := by
  have : projKer p (algebraMap (ZMod p) B r) = 0 :=
    Subtype.ext (by rw [coe_projKer, Bialgebra.counit_algebraMap, sub_self]; rfl)
  rw [derivOf_apply, this, map_zero, map_zero]

theorem derivOf_one : derivOf δ (1 : B) = 0 := by
  have := derivOf_algebraMap δ 1
  rwa [map_one] at this

theorem derivOf_mul (a b : B) :
    derivOf δ (a * b) =
      Coalgebra.counit (R := ZMod p) a * derivOf δ b + derivOf δ a * Coalgebra.counit (R := ZMod p) b := by
  set I := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)
  have key : projKer p (a * b) =
      Coalgebra.counit (R := ZMod p) a • projKer p b + Coalgebra.counit (R := ZMod p) b • projKer p a +
        ⟨(projKer p a : B) * projKer p b, I.mul_mem_left _ (projKer p b).2⟩ := by
    apply Subtype.ext
    simp only [coe_projKer, AddMemClass.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def,
      Bialgebra.counit_mul, map_mul]
    ring
  have hsq : I.toCotangent ⟨(projKer p a : B) * projKer p b, I.mul_mem_left _ (projKer p b).2⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (projKer p a).2 (projKer p b).2
  rw [derivOf_apply, key, map_add, map_add, hsq, map_zero, add_zero, map_add,
    LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, map_add, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, derivOf_apply, derivOf_apply]
  ring

noncomputable def pointOf : B →ₐ[ZMod p] 𝕊 where
  toFun b := TrivSqZeroExt.inl (Coalgebra.counit (R := ZMod p) b) + TrivSqZeroExt.inr (derivOf δ b)
  map_one' := TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.fst_add])
    (by simp [derivOf_one])
  map_mul' a b := TrivSqZeroExt.ext
    (by simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul])
    (by
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, derivOf_mul])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' a b := TrivSqZeroExt.ext
    (by simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero])
    (by simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        zero_add])
  commutes' r := TrivSqZeroExt.ext
    (by
      rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.fst_inl, Bialgebra.counit_algebraMap]
      rfl)
    (by
      rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_inl, derivOf_algebraMap])

theorem pointOf_apply (b : B) :
    pointOf δ b =
      TrivSqZeroExt.inl (Coalgebra.counit (R := ZMod p) b) + TrivSqZeroExt.inr (derivOf δ b) := rfl

theorem snd_pointOf (b : B) : (pointOf δ b).snd = derivOf δ b := by
  rw [pointOf_apply, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

end DerivPoint
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"

end CotangentAux
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"
end Deformation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map TruncWitt.verschiebung TruncWitt.coeff_verschiebung_zero TruncWitt.coeff_verschiebung_succ TruncWitt.frobeniusFun TruncWitt.coeff_frobeniusFun TruncWitt.shift TruncWitt.coeff_shift_zero TruncWitt.coeff_shift_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung wittHomFrobenius wittHomFrobenius_verschiebung wittHomVerschiebung_frobenius wittHomShift wittHomRestrict wittHomShift_verschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.of_shift DieudonneModule.induction_on DieudonneModule.exists_of DieudonneModule.lift DieudonneModule.lift_of DieudonneModule.hom_ext DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.frobenius_of DieudonneModule.frobenius_verschiebung TruncWitt.eq_zero_of_length_zero UnipotentWittCovector UnipotentWittCovector.of UnipotentWittCovector.of_shift UnipotentWittCovector.of_injective UnipotentWittCovector.verschiebung UnipotentWittCovector.verschiebung_of UnipotentWittCovector.frobenius UnipotentWittCovector.frobenius_of DieudonneModule.eval DieudonneModule.eval_of DieudonneModule.eval_convOne DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual"
p2m_open "Deformation"
namespace CotangentAux

section Main

theorem exists_linearMap_apply_ne_zero {K : Type*} [Field K] {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : Q) (hq : q ≠ 0) : ∃ ψ : Q →ₗ[K] K, ψ q ≠ 0 := by
  by_contra h
  push Not at h
  exact hq ((Module.forall_dual_apply_eq_zero_iff K q).1 h)

variable (p : ℕ) [hp : Fact p.Prime] (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B]
  [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]

local notation "𝕊" => DualNumber (ZMod p)

theorem theta_surjective (hB : IsLocalRing (CartierDual (ZMod p) B)) :
    Function.Surjective (theta p B) := by
  set I := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) with hI
  by_contra hsurj
  have hlt : AddSubgroup.toZModSubmodule p (theta p B).range < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hsurj
    intro c
    have hc : c ∈ AddSubgroup.toZModSubmodule p (theta p B).range := by
      rw [htop]; exact Submodule.mem_top
    exact AddMonoidHom.mem_range.1 ((AddSubgroup.mem_toZModSubmodule p).1 hc)
  obtain ⟨δ, hδ0, hδ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  apply hδ0

  have hcoeff : ∀ (n : ℕ) (x : wittHom (ZMod p) p n B) (i : Fin n),
      derivOf δ ((x : TruncatedWittVector p n B).coeff i) = 0 := by
    intro n x i
    rw [derivOf_apply, projKer_of_mem _ (coeff_mem_ker p B x i)]
    have hrange : I.toCotangent ⟨(x : TruncatedWittVector p n B).coeff i, coeff_mem_ker p B x i⟩ ∈
        (theta p B).range := by
      refine ⟨DieudonneModule.of (ZMod p) p B ((i : ℕ) + 1) (wittHomRestrict (ZMod p) p B i.isLt x),
        ?_⟩
      rw [theta_of_succ]
      congr 1
      apply Subtype.ext
      change (TruncatedWittVector.truncate _ (x : TruncatedWittVector p n B)).coeff (Fin.last i) = _
      rw [TruncatedWittVector.coeff_truncate]
      rfl
    exact (LinearMap.mem_ker).1 (hδ ((AddSubgroup.mem_toZModSubmodule p).2 hrange))

  have key : DieudonneModule.eval (ZMod p) p (pointOf δ) =
      DieudonneModule.eval (ZMod p) p (1 : WithConv (B →ₐ[ZMod p] 𝕊)).ofConv := by
    refine DieudonneModule.hom_ext fun n x => ?_
    rw [DieudonneModule.eval_convOne, DieudonneModule.eval_of]
    have h0 : TruncWitt.map (pointOf δ).toRingHom (x : TruncatedWittVector p n B) = 0 := by
      refine TruncatedWittVector.ext fun i => ?_
      rw [TruncWitt.coeff_map, TruncatedWittVector.coeff_zero]
      change pointOf δ ((x : TruncatedWittVector p n B).coeff i) = 0
      rw [pointOf_apply, hcoeff, counit_coeff_of_mem_wittHom x.2 i, TrivSqZeroExt.inl_zero,
        TrivSqZeroExt.inr_zero, add_zero]
    rw [h0, map_zero]
  have hf := (Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
    p B hB 𝕊).1 _ _ key
  refine LinearMap.ext fun c => ?_
  obtain ⟨m, rfl⟩ := I.toCotangent_surjective c
  have h1 := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hf (m : B))
  rw [snd_pointOf, derivOf_apply, projKer_of_mem _ m.2, AlgHom.convOne_apply,
    TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl] at h1
  rw [LinearMap.zero_apply]
  exact h1

theorem theta_eq_zero_iff (hB : IsLocalRing (CartierDual (ZMod p) B)) (hBloc : IsLocalRing B)
    (z : DieudonneModule (ZMod p) p B) :
    theta p B z = 0 ↔ z ∈ (DieudonneModule.frobenius (ZMod p) p B).range := by
  constructor
  · intro hz
    by_contra hzF
    set N := (DieudonneModule.frobenius (ZMod p) p B).range with hN
    letI : Module (ZMod p) (DieudonneModule (ZMod p) p B ⧸ N) :=
      QuotientAddGroup.zmodModule fun w => AddMonoidHom.mem_range.2
        ⟨DieudonneModule.verschiebung (ZMod p) p B w, by
          rw [DieudonneModule.frobenius_verschiebung, natCast_zsmul]⟩
    have hne : (QuotientAddGroup.mk z : DieudonneModule (ZMod p) p B ⧸ N) ≠ 0 := by
      rwa [Ne, QuotientAddGroup.eq_zero_iff]
    obtain ⟨ψ, hψ⟩ := exists_linearMap_apply_ne_zero (K := ZMod p) _ hne
    set lam : DieudonneModule (ZMod p) p B →+ ZMod p :=
      ψ.toAddMonoidHom.comp (QuotientAddGroup.mk' N) with hlam
    have hlamF : ∀ w, lam (DieudonneModule.frobenius (ZMod p) p B w) = 0 := by
      intro w
      rw [hlam, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        (QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨w, rfl⟩), map_zero]
    obtain ⟨f, hf⟩ :=
      (Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
        p B hB 𝕊).2 (phi lam) (phi_frobenius lam hlamF) (phi_verschiebung lam)

    have hfst : ∀ b, (f b).fst = Coalgebra.counit b := fun b =>
      algHom_apply_eq_counit hBloc ((TrivSqZeroExt.fstHom (ZMod p) (ZMod p) (ZMod p)).comp f) b

    have hsq : ∀ c ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) ^ 2, f c = 0 := by
      intro c hc
      rw [pow_two] at hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_)
        (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      have ha' : (f a).fst = 0 := by rw [hfst]; exact (mem_augIdeal_iff p B a).1 ha
      have hb' : (f b).fst = 0 := by rw [hfst]; exact (mem_augIdeal_iff p B b).1 hb
      rw [map_mul]
      exact TrivSqZeroExt.ext
        (by rw [TrivSqZeroExt.fst_mul, ha', zero_mul, TrivSqZeroExt.fst_zero])
        (by rw [DualNumber.snd_mul, ha', hb', zero_mul, mul_zero, add_zero, TrivSqZeroExt.snd_zero])
    obtain ⟨n, x, rfl⟩ := DieudonneModule.exists_of z
    cases n with
    | zero =>
      apply hzF
      have hx0 : x = 0 := Subtype.ext (by
        rw [TruncWitt.eq_zero_of_length_zero (x : TruncatedWittVector p 0 B), ZeroMemClass.coe_zero])
      rw [hx0, map_zero]
      exact zero_mem N
    | succ m =>
      apply hψ
      change lam (DieudonneModule.of (ZMod p) p B (m + 1) x) = 0
      rw [theta_of_succ, Ideal.toCotangent_eq_zero] at hz
      have h1 := apply_coeff_last_eq_of_eval_eq_phi lam f hf m x
      rw [hsq _ hz] at h1
      have h2 := congrArg TrivSqZeroExt.snd h1
      rw [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_inr] at h2
      exact h2.symm
  · rintro ⟨w, rfl⟩
    exact theta_frobenius p B w

end Main
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"

end CotangentAux
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"
end Deformation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation.CotangentAux P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual.Deformation"

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] (hB : IsLocalRing (CartierDual (ZMod p) B)) (hBloc : IsLocalRing B) :
    ∃ θ : Deformation.DieudonneModule (ZMod p) p B →+
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).Cotangent,
      (∀ (n : ℕ) (x : Deformation.wittHom (ZMod p) p (n + 1) B)
          (hx : (x : TruncatedWittVector p (n + 1) B).coeff (Fin.last n) ∈
            RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)),
        θ (Deformation.DieudonneModule.of (ZMod p) p B (n + 1) x) =
          (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)).toCotangent ⟨_, hx⟩) ∧
      Function.Surjective θ ∧
      ∀ z, θ z = 0 ↔ z ∈ (Deformation.DieudonneModule.frobenius (ZMod p) p B).range :=
  ⟨Deformation.CotangentAux.theta p B,
    fun n x hx => by rw [Deformation.CotangentAux.theta_of_succ],
    Deformation.CotangentAux.theta_surjective p B hB,
    Deformation.CotangentAux.theta_eq_zero_iff p B hB hBloc⟩

end S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual (solution)
