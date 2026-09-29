-- Prove2me | solution 1 for GaloisRep.exists_ideal_le_comap_includeRight_eq_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ba27f067-7fd9-543d-9da5-79fdf677d2b7

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct
open ModularCurve.XHDRLevel

namespace GDTensor

variable {p : ℕ} [Fact p.Prime]

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : (R p) →+* P) : f = g := by
  haveI : IsLocalization.AtPrime (R p) (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem exists_le_comap_eq (κ : Type) [Field κ] [CharP κ p] [Algebra (R p) κ]
    (O : Type) [CommRing O] [Algebra (R p) O]
    (P 𝔮 : Ideal O) [P.IsPrime] [𝔮.IsPrime] (hP𝔮 : P ≤ 𝔮) (hpP : ((p : ℕ) : O) ∈ P)
    (𝔓 : Ideal (κ ⊗[(R p)] O)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeRight : O →ₐ[(R p)] κ ⊗[(R p)] O).toRingHom = 𝔮) :
    ∃ 𝔓' : Ideal (κ ⊗[(R p)] O), 𝔓' ≤ 𝔓 ∧ 𝔓'.IsPrime ∧
      𝔓'.comap (Algebra.TensorProduct.includeRight : O →ₐ[(R p)] κ ⊗[(R p)] O).toRingHom = P := by
  classical

  let S : Type := κ ⊗[(R p)] O
  let ι : O →+* S := (Algebra.TensorProduct.includeRight : O →ₐ[(R p)] S).toRingHom
  let I : Ideal O := Ideal.span {((p : ℕ) : O)}
  let A : Type := O ⧸ I
  let mk : O →+* A := Ideal.Quotient.mk I
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩

  have hpκ : ((p : ℕ) : κ) = 0 := CharP.cast_eq_zero κ p
  have hpS : ((p : ℕ) : S) = 0 := by
    have : ((p : ℕ) : S) = algebraMap κ S (p : κ) := by rw [map_natCast]
    rw [this, hpκ, map_zero]
  have hpA : ((p : ℕ) : A) = 0 := by
    show mk (p : O) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

  haveI : CharP A (ringChar A) := ringChar.charP A
  let fA : ZMod p →+* A := ZMod.castHom ((ringChar.spec A p).mp hpA) A
  letI algA : Algebra (ZMod p) A := fA.toAlgebra
  letI algκ : Algebra (ZMod p) κ := ZMod.algebra κ p
  haveI : SMulCommClass (R p) (ZMod p) κ :=
    ⟨fun r s x => by rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

  letI algS𝔽 : Algebra (ZMod p) S := Algebra.TensorProduct.leftAlgebra
  let T : Type := A ⊗[ZMod p] κ

  haveI : Module.Flat A T := inferInstance
  haveI : Algebra.HasGoingDown A T := inferInstance

  haveI : IsScalarTower (ZMod p) (ZMod p) S := IsScalarTower.left _
  haveI : IsScalarTower (ZMod p) (ZMod p) A := IsScalarTower.left _
  have hIker : ∀ a ∈ I, ι a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_natCast, hpS, zero_mul]
  let ιA : A →+* S := Ideal.Quotient.lift I ι hIker
  have hιA : ∀ b : O, ιA (mk b) = ι b := fun b => Ideal.Quotient.lift_mk I ι hIker
  have cA : (ιA.comp (algebraMap (ZMod p) A)) = algebraMap (ZMod p) S := Subsingleton.elim _ _
  let ιAalg : A →ₐ[ZMod p] S := { toRingHom := ιA, commutes' := fun r => RingHom.congr_fun cA r }
  have cκ : ((Algebra.TensorProduct.includeLeftRingHom : κ →+* S).comp (algebraMap (ZMod p) κ)) = algebraMap (ZMod p) S := Subsingleton.elim _ _
  let jκ : κ →ₐ[ZMod p] S := { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : κ →+* S), commutes' := fun r => RingHom.congr_fun cκ r }
  let h : T →ₐ[ZMod p] S := Algebra.TensorProduct.lift ιAalg jκ (fun _ _ => Commute.all _ _)
  have hh : ∀ (b : O) (x : κ), h (mk b ⊗ₜ[ZMod p] x) = x ⊗ₜ[(R p)] b := by
    intro b x
    show Algebra.TensorProduct.lift ιAalg jκ _ (mk b ⊗ₜ[ZMod p] x) = _
    rw [Algebra.TensorProduct.lift_tmul]
    show ιA (mk b) * (x ⊗ₜ[(R p)] (1 : O)) = x ⊗ₜ[(R p)] b
    rw [hιA]
    show ((1 : κ) ⊗ₜ[(R p)] b) * (x ⊗ₜ[(R p)] (1 : O)) = x ⊗ₜ[(R p)] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

  letI algT : Algebra (R p) T := ((algebraMap A T).comp (mk.comp (algebraMap (R p) O))).toAlgebra
  let eO : O →ₐ[(R p)] T := { toRingHom := (algebraMap A T).comp mk, commutes' := fun r => rfl }
  have cκ' : ((Algebra.TensorProduct.includeRight : κ →ₐ[ZMod p] T).toRingHom.comp (algebraMap (R p) κ)) = algebraMap (R p) T :=
    ringHom_ext_zp _ _
  let eκ : κ →ₐ[(R p)] T := { toRingHom := (Algebra.TensorProduct.includeRight : κ →ₐ[ZMod p] T).toRingHom, commutes' := fun r => RingHom.congr_fun cκ' r }
  let e : S →ₐ[(R p)] T := Algebra.TensorProduct.lift eκ eO (fun _ _ => Commute.all _ _)
  have he : ∀ (x : κ) (b : O), e (x ⊗ₜ[(R p)] b) = mk b ⊗ₜ[ZMod p] x := by
    intro x b
    show Algebra.TensorProduct.lift eκ eO _ (x ⊗ₜ[(R p)] b) = _
    rw [Algebra.TensorProduct.lift_tmul]
    show ((1 : A) ⊗ₜ[ZMod p] x) * (algebraMap A T (mk b)) = mk b ⊗ₜ[ZMod p] x
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

  have heh : ∀ t : T, e (h t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a x =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [show (Ideal.Quotient.mk I b) = mk b from rfl, hh, he]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  have hhe : ∀ s : S, h (e s) = s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul x b => rw [he, hh]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  let E : S ≃+* T := RingEquiv.ofRingHom (e : S →+* T) (h : T →+* S) (RingHom.ext fun t => heh t) (RingHom.ext fun s => hhe s)
  have hEι : ∀ b : O, E (ι b) = algebraMap A T (mk b) := by
    intro b
    show e ((1 : κ) ⊗ₜ[(R p)] b) = _
    rw [he, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  let Q : Ideal T := 𝔓.comap (E.symm : T →+* S)
  haveI hQ : Q.IsPrime := Ideal.comap_isPrime _ _
  have hmemQ : ∀ t : T, t ∈ Q ↔ E.symm t ∈ 𝔓 := fun t => Ideal.mem_comap
  let pA : Ideal A := P.map mk
  let qA : Ideal A := 𝔮.map mk
  have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hpP
  have hI𝔮 : I ≤ 𝔮 := hIP.trans hP𝔮
  haveI hpA' : pA.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  haveI hqA' : qA.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomapP : pA.comap mk = P := by
    show (P.map mk).comap mk = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIP]
  have hcomap𝔮 : qA.comap mk = 𝔮 := by
    show (𝔮.map mk).comap mk = 𝔮
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI𝔮]

  have hQunder : Q.comap (algebraMap A T) = qA := by
    apply Ideal.comap_injective_of_surjective mk Ideal.Quotient.mk_surjective
    rw [Ideal.comap_comap, hcomap𝔮, ← h𝔓]
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.comp_apply, ← hEι]
    show E (ι b) ∈ Q ↔ ι b ∈ 𝔓
    rw [hmemQ, RingEquiv.symm_apply_apply]

  have hpq : pA ≤ qA := Ideal.map_mono hP𝔮
  haveI : Q.LiesOver qA := ⟨by rw [Ideal.under_def, hQunder]⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := pA) (q := qA) Q hpq

  refine ⟨Q'.comap (E : S →+* T), ?_, Ideal.comap_isPrime _ _, ?_⟩
  · intro s hs
    rw [Ideal.mem_comap] at hs
    have := (hmemQ _).mp (hQ'Q hs)
    rwa [show E.symm ((E : S →+* T) s) = s from E.symm_apply_apply s] at this
  · rw [← hcomapP, hQ'over.over, Ideal.under_def, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    ext b
    show E (ι b) = algebraMap A T (mk b)
    exact hEι b

end GDTensor

open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]
    (O : Type) [CommRing O] [Algebra ↥(GaloisRep.ratLocalizedAt p) O]
    (P 𝔮 : Ideal O) [P.IsPrime] [𝔮.IsPrime] (hP𝔮 : P ≤ 𝔮) (hpP : ((p : ℕ) : O) ∈ P)
    (𝔓 : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeRight :
        O →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O).toRingHom = 𝔮) :
    ∃ 𝔓' : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O), 𝔓' ≤ 𝔓 ∧ 𝔓'.IsPrime ∧
      𝔓'.comap (Algebra.TensorProduct.includeRight :
        O →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] O).toRingHom = P :=
  GDTensor.exists_le_comap_eq (p := p) κ O P 𝔮 hP𝔮 hpP 𝔓 h𝔓

end S_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem
end P2MW
export P2MW.S_GaloisRep_exists_ideal_le_comap_includeRight_eq_of_natCast_mem (solution)
