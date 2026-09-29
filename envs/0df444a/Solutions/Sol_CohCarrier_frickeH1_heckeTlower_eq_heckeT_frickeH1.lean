-- Prove2me | solution 1 for CohCarrier.frickeH1_heckeTlower_eq_heckeT_frickeH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/606d091e-807c-542b-ad0b-4d939ea068dc

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace FrickeHecke

section TransferNat

variable {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
  (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, e x ∈ K' ↔ x ∈ K)

def resK : K →* K' where
  toFun x := ⟨e x, (hK x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_resK (x : K) : ((resK e K K' hK x : K') : G') = e x := rfl

def quotEquiv : G ⧸ K ≃ G' ⧸ K' :=
  Quotient.congr e.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hK, map_mul, map_inv]
    rfl

theorem quotEquiv_mk (x : G) :
    quotEquiv e K K' hK (QuotientGroup.mk x) = QuotientGroup.mk (e x) := rfl

theorem quotEquiv_smul (g : G) (q : G ⧸ K) :
    quotEquiv e K K' hK (g • q) = e g • quotEquiv e K K' hK q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, quotEquiv_mk, quotEquiv_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

variable {C : Type*} [CommGroup C]

theorem transfer_comp_resK [K.FiniteIndex] [K'.FiniteIndex] (ψ : K' →* C) (g : G) :
    MonoidHom.transfer (ψ.comp (resK e K K' hK)) g = MonoidHom.transfer ψ (e g) := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  letI := K'.fintypeQuotientOfFiniteIndex

  set f : G ⧸ K → G := Quotient.out with hfdef
  have hf : ∀ q, (f q : G ⧸ K) = q := fun q => Quotient.out_eq q
  set ē := quotEquiv e K K' hK with hē
  set f' : G' ⧸ K' → G' := fun q' => e (f (ē.symm q')) with hf'def
  have hf' : ∀ q', (f' q' : G' ⧸ K') = q' := by
    intro q'
    show QuotientGroup.mk (e (f (ē.symm q'))) = q'
    rw [← quotEquiv_mk e K K' hK, hf, ← hē, Equiv.apply_symm_apply]
  let T : K.LeftTransversal := ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  let T' : K'.LeftTransversal := ⟨Set.range f', Subgroup.isComplement_range_left hf'⟩
  rw [MonoidHom.transfer_def _ T g, MonoidHom.transfer_def _ T' (e g)]
  simp only [Subgroup.leftTransversals.diff]
  refine Fintype.prod_equiv ē _ _ fun x => ?_
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  show e ((T.2.leftQuotientEquiv x : G)⁻¹ * ((g • T).2.leftQuotientEquiv x : G)) =
    (T'.2.leftQuotientEquiv (ē x) : G')⁻¹ * ((e g • T').2.leftQuotientEquiv (ē x) : G')
  rw [map_mul, map_inv, Subgroup.smul_apply_eq_smul_apply_inv_smul,
    Subgroup.smul_apply_eq_smul_apply_inv_smul]
  have e1 : (T.2.leftQuotientEquiv x : G) = f x := Subgroup.IsComplement.leftQuotientEquiv_apply hf x
  have e2 : (T.2.leftQuotientEquiv (g⁻¹ • x) : G) = f (g⁻¹ • x) := Subgroup.IsComplement.leftQuotientEquiv_apply hf _
  have e3 : (T'.2.leftQuotientEquiv (ē x) : G') = f' (ē x) := Subgroup.IsComplement.leftQuotientEquiv_apply hf' _
  have e4 : (T'.2.leftQuotientEquiv ((e g)⁻¹ • ē x) : G') = f' ((e g)⁻¹ • ē x) :=
    Subgroup.IsComplement.leftQuotientEquiv_apply hf' _
  rw [e1, e2, e3, e4]
  have hsm : (e g)⁻¹ • ē x = ē (g⁻¹ • x) := by rw [hē, quotEquiv_smul, map_inv]
  rw [hsm, hf'def]
  simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul]

end TransferNat

section Fricke

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (q : ℕ) [NeZero q]

open CohCarrier

omit [NeZero q] in

theorem frickeEquiv_mem_lower_iff (γ : ↥(GammaH N H)) :
    frickeEquiv N H γ ∈ GammaHLower N H q ↔ γ ∈ GammaHUpper N H q := by
  rw [GammaHLower, Subgroup.mem_subgroupOf, Gamma0_mem, GammaHUpper, Subgroup.mem_subgroupOf,
    mem_Gamma0Upper, frickeEquiv_apply, coe_frickeHom, frickeMat_apply_10, Int.cast_neg, neg_eq_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  rw [mul_comm (q : ℤ) (N : ℤ)]
  exact Int.mul_dvd_mul_iff_left hN

theorem frickeMat_conjUpperMat (A : SL(2, ℤ)) (hA : (N : ℤ) ∣ A 1 0) (hq : (q : ℤ) ∣ A 0 1)
    (h1 : (N : ℤ) ∣ (conjUpperMat q A hq) 1 0) (h2 : (q : ℤ) ∣ (frickeMat N A hA) 1 0) :
    frickeMat N (conjUpperMat q A hq) h1 = conjLowerMat q (frickeMat N A hA) h2 := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [frickeMat, conjUpperMat, conjLowerMat]
  ·
    obtain ⟨c, hc⟩ := hA
    rw [hc, mul_comm ((N : ℤ) * c) (q : ℤ), ← mul_assoc, mul_comm (q : ℤ) (N : ℤ), mul_assoc,
      Int.mul_ediv_cancel_left _ hN, Int.mul_ediv_cancel_left _ hN]
    ring
  ·
    obtain ⟨b, hb⟩ := hq
    rw [hb, Int.mul_ediv_cancel_left _ hq0, show (N : ℤ) * ((q : ℤ) * b) = (q : ℤ) * ((N : ℤ) * b) by ring,
      Int.neg_ediv_of_dvd (Dvd.intro _ rfl), Int.mul_ediv_cancel_left _ hq0]

theorem frickeEquiv_conjL (γ : ↥(GammaHUpper N H q)) :
    frickeEquiv N H (conjL N H q γ) =
      conjLowerL N H q (resK (frickeEquiv N H) (GammaHUpper N H q) (GammaHLower N H q)
        (frickeEquiv_mem_lower_iff N H q) γ) := by
  apply Subtype.ext
  exact frickeMat_conjUpperMat N q _ (N_dvd_of_mem_GammaH N H (γ : ↥(GammaH N H)))
    (dvd_of_mem_GammaHUpper N H q γ) (N_dvd_of_mem_GammaH N H (conjL N H q γ))
    (dvd_of_mem_GammaHLower N H q (resK (frickeEquiv N H) (GammaHUpper N H q) (GammaHLower N H q)
      (frickeEquiv_mem_lower_iff N H q) γ))

end Fricke

section Assembly

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]

open CohCarrier

omit [NeZero N] in
theorem heckeT_apply_ofMul (φ : H1 N H A) (g : ↥(GammaH N H)) :
    heckeT N H q A φ (Additive.ofMul g) =
      Multiplicative.toAdd (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H q)) g) := rfl

theorem heckeTlower_apply_ofMul (φ : H1 N H A) (g : ↥(GammaH N H)) :
    heckeTlower N H q A φ (Additive.ofMul g) =
      Multiplicative.toAdd (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjLowerL N H q)) g) := rfl

theorem comp_conjL_frickeH1 (φ : H1 N H A) :
    (AddMonoidHom.toMultiplicativeRight (frickeH1 N H A φ)).comp (conjL N H q) =
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjLowerL N H q)).comp
        (resK (frickeEquiv N H) (GammaHUpper N H q) (GammaHLower N H q)
          (frickeEquiv_mem_lower_iff N H q)) := by
  refine MonoidHom.ext fun γ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, frickeH1_apply]
  congr 2
  rw [← frickeEquiv_apply, frickeEquiv_conjL]

theorem main (φ : H1 N H A) :
    frickeH1 N H A (heckeTlower N H q A φ) = heckeT N H q A (frickeH1 N H A φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨g, rfl⟩ : ∃ g : ↥(GammaH N H), Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [frickeH1_apply, heckeTlower_apply_ofMul, heckeT_apply_ofMul, comp_conjL_frickeH1,
    transfer_comp_resK, frickeEquiv_apply]

end Assembly

end FrickeHecke
p2m_reactivate "P2MW.S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1.FrickeHecke"

theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (q : ℕ) [NeZero q]
    (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N H A) :
    CohCarrier.frickeH1 N H A (CohCarrier.heckeTlower N H q A φ) =
      CohCarrier.heckeT N H q A (CohCarrier.frickeH1 N H A φ) :=
  FrickeHecke.main N H q A φ

end S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1
end P2MW
export P2MW.S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1 (solution)
