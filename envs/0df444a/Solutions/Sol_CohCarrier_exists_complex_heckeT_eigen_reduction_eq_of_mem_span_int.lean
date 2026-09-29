-- Prove2me | solution 1 for CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a462462a-168b-5f36-9f59-a74570cb789d

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_DeligneSerre_exists_eigencharacter_of_annihilator_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeLatticeLift

open Polynomial

section FiniteFieldExtension

variable {κ : Type} [Field κ] (φ : integralClosure ℤ ℂ →+* κ)

theorem ker_isMaximal (p : ℕ) [Fact p.Prime] [CharP κ p] : (RingHom.ker φ).IsMaximal := by
  have hp : p.Prime := Fact.out
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) (RingHom.ker φ) ?_
  have hcomap : (RingHom.ker φ).comap (algebraMap ℤ (integralClosure ℤ ℂ)) = Ideal.span {(p : ℤ)} := by
    ext n
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, map_intCast,
      CharP.intCast_eq_zero_iff κ p]
  rw [hcomap]
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  exact IsPrime.to_maximal_ideal (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero)

variable [hmax : (RingHom.ker φ).IsMaximal]

abbrev ImageField : Type := integralClosure ℤ ℂ ⧸ RingHom.ker φ

noncomputable scoped instance instFieldImageField : Field (ImageField φ) := Ideal.Quotient.field _

noncomputable def imageMk : integralClosure ℤ ℂ →+* ImageField φ := Ideal.Quotient.mk (RingHom.ker φ)

omit hmax in
theorem imageMk_surjective : Function.Surjective (imageMk φ) := Ideal.Quotient.mk_surjective

noncomputable def imageEmb : ImageField φ →+* κ := RingHom.kerLift φ

omit hmax in
theorem imageEmb_injective : Function.Injective (imageEmb φ) := RingHom.kerLift_injective φ

scoped instance isAlgClosed_imageField : IsAlgClosed (ImageField φ) := by
  refine IsAlgClosed.of_exists_root _ fun q hqm hqi => ?_
  have hlifts : q ∈ Polynomial.lifts (imageMk φ) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun n => imageMk_surjective φ (q.coeff n)
  obtain ⟨Q, hQq, hQdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hqm
  have hdeg : (Q.map (algebraMap (integralClosure ℤ ℂ) ℂ)).degree ≠ 0 := by
    rw [hQm.degree_map, hQdeg]
    exact (Polynomial.degree_pos_of_irreducible hqi).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  have hzint : IsIntegral (integralClosure ℤ ℂ) z :=
    ⟨Q, hQm, by rw [← Polynomial.eval_map]; exact hz.eq_zero⟩
  have hzint' : IsIntegral ℤ z := isIntegral_trans z hzint
  refine ⟨imageMk φ ⟨z, hzint'⟩, ?_⟩
  have hQz : Q.eval ⟨z, hzint'⟩ = 0 := by
    have hinj : Function.Injective (algebraMap (integralClosure ℤ ℂ) ℂ) := Subtype.val_injective
    apply hinj
    have hz' : (algebraMap (integralClosure ℤ ℂ) ℂ) ⟨z, hzint'⟩ = z := rfl
    rw [map_zero, ← Polynomial.eval₂_hom, hz', ← Polynomial.eval_map]
    exact hz.eq_zero
  rw [← hQq, Polynomial.eval_map, Polynomial.eval₂_hom, hQz, map_zero]

variable {k₀ : Type} [Field k₀] [Finite k₀]

theorem exists_imageEmb_eq (g : k₀ →+* κ) (a : k₀) : ∃ m : ImageField φ, imageEmb φ m = g a := by
  classical
  haveI := Fintype.ofFinite k₀
  set q : ℕ := Fintype.card k₀ with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  set P : (ImageField φ)[X] := X ^ q - X with hP
  have hPsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.roots.card = P.natDegree := Polynomial.splits_iff_card_roots.mp hPsplit
  have hroots := Polynomial.roots_map_of_injective_of_card_eq_natDegree (imageEmb_injective φ) hcard
  have hPmap : P.map (imageEmb φ) = X ^ q - X := by
    rw [hP, Polynomial.map_sub, Polynomial.map_pow, map_X]
  have hne : (X ^ q - X : κ[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hq1
  have hga : g a ∈ (P.map (imageEmb φ)).roots := by
    rw [hPmap, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow, FiniteField.pow_card,
      sub_self]
  rw [← hroots, Multiset.mem_map] at hga
  obtain ⟨m, -, hm⟩ := hga
  exact ⟨m, hm⟩

noncomputable def descend (g : k₀ →+* κ) : k₀ →+* ImageField φ where
  toFun a := (exists_imageEmb_eq φ g a).choose
  map_one' := by
    apply imageEmb_injective φ
    rw [(exists_imageEmb_eq φ g 1).choose_spec, g.map_one, (imageEmb φ).map_one]
  map_mul' a b := by
    apply imageEmb_injective φ
    rw [(exists_imageEmb_eq φ g (a * b)).choose_spec, g.map_mul, (imageEmb φ).map_mul,
      (exists_imageEmb_eq φ g a).choose_spec, (exists_imageEmb_eq φ g b).choose_spec]
  map_zero' := by
    apply imageEmb_injective φ
    rw [(exists_imageEmb_eq φ g 0).choose_spec, g.map_zero, (imageEmb φ).map_zero]
  map_add' a b := by
    apply imageEmb_injective φ
    rw [(exists_imageEmb_eq φ g (a + b)).choose_spec, g.map_add, (imageEmb φ).map_add,
      (exists_imageEmb_eq φ g a).choose_spec, (exists_imageEmb_eq φ g b).choose_spec]

theorem imageEmb_descend (g : k₀ →+* κ) (a : k₀) : imageEmb φ (descend φ g a) = g a :=
  (exists_imageEmb_eq φ g a).choose_spec

include φ hmax in

theorem exists_ringHom_comp_algebraMap_eq (E : Type*) [Field E] [Algebra k₀ E] [Algebra.IsAlgebraic k₀ E]
    (g : k₀ →+* κ) : ∃ e : E →+* κ, e.comp (algebraMap k₀ E) = g := by
  letI : Algebra k₀ (ImageField φ) := (descend φ g).toAlgebra
  haveI : Module.IsTorsionFree k₀ (ImageField φ) := ⟨fun r hr m₁ m₂ h => by
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    have h' : algebraMap k₀ (ImageField φ) r * m₁ = algebraMap k₀ (ImageField φ) r * m₂ := by
      simpa only [Algebra.smul_def] using h
    exact mul_left_cancel₀ ((map_ne_zero (algebraMap k₀ (ImageField φ))).mpr hr0) h'⟩
  haveI : Module.IsTorsionFree k₀ E := ⟨fun r hr m₁ m₂ h => by
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    have h' : algebraMap k₀ E r * m₁ = algebraMap k₀ E r * m₂ := by
      simpa only [Algebra.smul_def] using h
    exact mul_left_cancel₀ ((map_ne_zero (algebraMap k₀ E)).mpr hr0) h'⟩
  let f : E →ₐ[k₀] ImageField φ := IsAlgClosed.lift
  refine ⟨(imageEmb φ).comp f.toRingHom, ?_⟩
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact imageEmb_descend φ g a

end FiniteFieldExtension

section Kernel

variable {T : Type*} [CommRing T] [Module.Finite ℤ T] {κ : Type} [Field κ]

omit [Module.Finite ℤ T] in
theorem natCast_mem_ker (p : ℕ) [CharP κ p] (χ : T →+* κ) : ((p : ℕ) : T) ∈ RingHom.ker χ := by
  rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

theorem finite_quotient_ker (p : ℕ) [Fact p.Prime] [CharP κ p] (χ : T →+* κ) : Finite (T ⧸ RingHom.ker χ) := by
  haveI : Module.Finite ℤ (T ⧸ RingHom.ker χ) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk (RingHom.ker χ)).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  refine Module.finite_of_fg_torsion (T ⧸ RingHom.ker χ) fun x => ?_
  refine ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)⟩, ?_⟩
  change ((p : ℤ)) • x = 0
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [zsmul_eq_mul, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk (RingHom.ker χ)) p, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (natCast_mem_ker p χ)

theorem ker_isMaximal' (p : ℕ) [Fact p.Prime] [CharP κ p] (χ : T →+* κ) : (RingHom.ker χ).IsMaximal := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  haveI : IsDomain (T ⧸ RingHom.ker χ) := Ideal.Quotient.isDomain _
  haveI : Finite (T ⧸ RingHom.ker χ) := finite_quotient_ker p χ
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (T ⧸ RingHom.ker χ))

end Kernel

section Operators

open CohCarrier

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S₀ : Set ℕ)

def GoodPrime : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀}

noncomputable def Tgen (A : Type) [CommRing A] (ℓ : GoodPrime N S₀) : Module.End A (H1 N H A) :=
  haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
  heckeTL N H A ℓ.1

theorem Tgen_apply (A : Type) [CommRing A] (ℓ : GoodPrime N S₀) (F : H1 N H A) :
    Tgen N H S₀ A ℓ F = (haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩; heckeT N H ℓ.1 A F) := rfl

theorem Tgen_comm (A : Type) [CommRing A] (ℓ ℓ' : GoodPrime N S₀) :
    Tgen N H S₀ A ℓ * Tgen N H S₀ A ℓ' = Tgen N H S₀ A ℓ' * Tgen N H S₀ A ℓ := by
  refine LinearMap.ext fun F => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Tgen_apply, Tgen_apply, Tgen_apply, Tgen_apply]
  haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
  haveI : NeZero ℓ'.1 := ⟨ℓ'.2.1.ne_zero⟩
  by_cases h : ℓ.1 = ℓ'.1
  ·
    have : ℓ = ℓ' := Subtype.ext h
    subst this
    rfl
  · exact heckeT_comm_of_prime N H ℓ.1 ℓ'.1 ℓ.2.1 ((Nat.coprime_primes ℓ.2.1 ℓ'.2.1).mpr h) F

theorem Tgen_comp {A B : Type} [CommRing A] [CommRing B] (g : A →+ B) (ℓ : GoodPrime N S₀) (F : H1 N H A) :
    Tgen N H S₀ B ℓ (g.comp F) = g.comp (Tgen N H S₀ A ℓ F) := by
  rw [Tgen_apply, Tgen_apply]
  haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
  exact heckeT_comp_coeff N H ℓ.1 g F

abbrev R : Type := FreeAlgebra ℤ (GoodPrime N S₀)

noncomputable def ev (A : Type) [CommRing A] : R N S₀ →ₐ[ℤ] Module.End A (H1 N H A) :=
  FreeAlgebra.lift ℤ (Tgen N H S₀ A)

theorem ev_ι (A : Type) [CommRing A] (ℓ : GoodPrime N S₀) :
    ev N H S₀ A (FreeAlgebra.ι ℤ ℓ) = Tgen N H S₀ A ℓ :=
  FreeAlgebra.lift_ι_apply _ _

theorem ev_comp {A B : Type} [CommRing A] [CommRing B] (g : A →+ B) (P : R N S₀) (F : H1 N H A) :
    ev N H S₀ B P (g.comp F) = g.comp (ev N H S₀ A P F) := by
  induction P using FreeAlgebra.induction generalizing F with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply]
    refine AddMonoidHom.ext fun γ => ?_
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.coe_comp, Function.comp_apply, ← map_zsmul g]
  | grade1 ℓ => rw [ev_ι, ev_ι, Tgen_comp]
  | mul a b iha ihb =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ihb, iha]
  | add a b iha ihb =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, iha, ihb, AddMonoidHom.comp_add]

theorem ev_commute (A : Type) [CommRing A] (P Q : R N S₀) : Commute (ev N H S₀ A P) (ev N H S₀ A Q) := by
  induction P using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left r _
  | grade1 ℓ =>
    induction Q using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_right r _
    | grade1 ℓ' => rw [ev_ι, ev_ι]; exact Tgen_comm N H S₀ A ℓ ℓ'
    | mul a b iha ihb => rw [map_mul]; exact iha.mul_right ihb
    | add a b iha ihb => rw [map_add]; exact iha.add_right ihb
  | mul a b iha ihb => rw [map_mul]; exact iha.mul_left ihb
  | add a b iha ihb => rw [map_add]; exact iha.add_left ihb

def coe (A : Type) [CommRing A] : H1 N H ℤ →+ H1 N H A where
  toFun G := (Int.castAddHom A).comp G
  map_zero' := by ext; simp
  map_add' G G' := by ext; simp

theorem coe_apply (A : Type) [CommRing A] (G : H1 N H ℤ) : coe N H A G = (Int.castAddHom A).comp G := rfl

theorem ev_coe (A : Type) [CommRing A] (P : R N S₀) (G : H1 N H ℤ) :
    ev N H S₀ A P (coe N H A G) = coe N H A (ev N H S₀ ℤ P G) := by
  rw [coe_apply, coe_apply, ev_comp]

theorem coe_injective_complex : Function.Injective (coe N H ℂ) := by
  intro G G' h
  refine AddMonoidHom.ext fun γ => ?_
  have := congrArg (fun F : H1 N H ℂ => F γ) h
  simpa [coe_apply] using this

end Operators

section Order

open CohCarrier

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S₀ : Set ℕ)

noncomputable def Vp : Submodule ℂ (H1 N H ℂ) := Submodule.span ℂ (Set.range (coe N H ℂ))

theorem coe_mem_Vp (G : H1 N H ℤ) : coe N H ℂ G ∈ Vp N H := Submodule.subset_span ⟨G, rfl⟩

theorem ev_mem_Vp (P : R N S₀) {v : H1 N H ℂ} (hv : v ∈ Vp N H) : ev N H S₀ ℂ P v ∈ Vp N H := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨G, rfl⟩ := hw
    rw [ev_coe]
    exact coe_mem_Vp N H _
  | zero => rw [map_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
  | smul c w _ hw => rw [map_smul]; exact Submodule.smul_mem _ c hw

noncomputable def evV : R N S₀ →+* Module.End ℂ (Vp N H) where
  toFun P := (ev N H S₀ ℂ P).restrict (fun _ hv => ev_mem_Vp N H S₀ P hv)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' P Q := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_zero' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_add' P Q := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp [LinearMap.restrict_apply]

theorem coe_evV (P : R N S₀) (v : Vp N H) : ((evV N H S₀ P v : Vp N H) : H1 N H ℂ) = ev N H S₀ ℂ P v := rfl

noncomputable abbrev I : Ideal (R N S₀) := RingHom.ker (evV N H S₀)

def T : Type := R N S₀ ⧸ I N H S₀

noncomputable scoped instance instCommRingT : CommRing (T N H S₀) :=
  { (inferInstanceAs (Ring (R N S₀ ⧸ I N H S₀)) : Ring (T N H S₀)) with
    mul_comm := fun a b => by
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := I N H S₀) a
      obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective (I := I N H S₀) b
      change Ideal.Quotient.mk (I N H S₀) P * Ideal.Quotient.mk (I N H S₀) Q =
        Ideal.Quotient.mk (I N H S₀) Q * Ideal.Quotient.mk (I N H S₀) P
      rw [← map_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      change P * Q - Q * P ∈ RingHom.ker (evV N H S₀)
      rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero]
      refine LinearMap.ext fun v => Subtype.ext ?_
      change ev N H S₀ ℂ P (ev N H S₀ ℂ Q v) = ev N H S₀ ℂ Q (ev N H S₀ ℂ P v)
      exact congrArg (fun f : Module.End ℂ (H1 N H ℂ) => f v) (ev_commute N H S₀ ℂ P Q).eq }

noncomputable def mkT : R N S₀ →+* T N H S₀ := Ideal.Quotient.mk (I N H S₀)

theorem mkT_surjective : Function.Surjective (mkT N H S₀) := Ideal.Quotient.mk_surjective

noncomputable def act : T N H S₀ →+* Module.End ℂ (Vp N H) := RingHom.kerLift (evV N H S₀)

theorem act_injective : Function.Injective (act N H S₀) := RingHom.kerLift_injective (evV N H S₀)

theorem act_mkT (P : R N S₀) : act N H S₀ (mkT N H S₀ P) = evV N H S₀ P := RingHom.kerLift_mk (evV N H S₀) P

noncomputable def liftT {κ : Type} [Field κ] (χ₀ : R N S₀ →+* κ) (h : ∀ P, evV N H S₀ P = 0 → χ₀ P = 0) :
    T N H S₀ →+* κ :=
  Ideal.Quotient.lift (I N H S₀) χ₀ (fun P hP => h P (by rwa [I, RingHom.mem_ker] at hP))

theorem liftT_mkT {κ : Type} [Field κ] (χ₀ : R N S₀ →+* κ) (h : ∀ P, evV N H S₀ P = 0 → χ₀ P = 0)
    (P : R N S₀) : liftT N H S₀ χ₀ h (mkT N H S₀ P) = χ₀ P :=
  Ideal.Quotient.lift_mk _ _ _

noncomputable scoped instance instModuleT : Module (T N H S₀) (Vp N H) := Module.compHom (Vp N H) (act N H S₀)

private theorem _root_.HeckeLatticeLift.smul_def (t : T N H S₀) (v : Vp N H) : t • v = act N H S₀ t v := rfl

p2m_export "HeckeLatticeLift" "smul_def"
scoped instance instSMulCommClassT : SMulCommClass (T N H S₀) ℂ (Vp N H) :=
  ⟨fun t c v => by rw [smul_def, smul_def, map_smul]⟩

theorem ev_eq_smul_of_mkT_smul (P : R N S₀) (X : Vp N H) (a : ℂ) (h : mkT N H S₀ P • X = a • X) :
    ev N H S₀ ℂ P (X : H1 N H ℂ) = a • (X : H1 N H ℂ) := by
  have e1 : ((mkT N H S₀ P • X : Vp N H) : H1 N H ℂ) = ev N H S₀ ℂ P (X : H1 N H ℂ) := by
    rw [smul_def, act_mkT]; rfl
  have e2 : ((a • X : Vp N H) : H1 N H ℂ) = a • (X : H1 N H ℂ) := rfl
  rw [← e1, ← e2, h]

scoped instance instModuleFiniteLattice : Module.Finite ℤ (H1 N H ℤ) := CohCarrier.H1_moduleFinite N H ℤ ℤ

scoped instance instModuleFiniteComplex : Module.Finite ℂ (H1 N H ℂ) := CohCarrier.H1_moduleFinite N H ℂ ℂ

noncomputable def coeV : H1 N H ℤ →ₗ[ℤ] Vp N H where
  toFun G := ⟨coe N H ℂ G, coe_mem_Vp N H G⟩
  map_add' G G' := Subtype.ext (by simp [map_add])
  map_smul' n G := Subtype.ext (by simp [map_zsmul])

theorem coe_coeV (G : H1 N H ℤ) : ((coeV N H G : Vp N H) : H1 N H ℂ) = coe N H ℂ G := rfl

theorem exists_act_coeV (t : T N H S₀) (G : H1 N H ℤ) : ∃ G' : H1 N H ℤ, act N H S₀ t (coeV N H G) = coeV N H G' := by
  obtain ⟨P, rfl⟩ := mkT_surjective N H S₀ t
  refine ⟨ev N H S₀ ℤ P G, Subtype.ext ?_⟩
  rw [act_mkT, coe_evV, coe_coeV, coe_coeV, ev_coe]

noncomputable def Lat : Submodule ℤ (Vp N H) := LinearMap.range (coeV N H)

scoped instance instModuleFiniteLat : Module.Finite ℤ (Lat N H) := Module.Finite.range (coeV N H)

noncomputable def ψ (s : Finset (H1 N H ℤ)) : T N H S₀ →ₗ[ℤ] (↥s → Lat N H) where
  toFun t i := ⟨act N H S₀ t (coeV N H (i : H1 N H ℤ)), by
    obtain ⟨G', hG'⟩ := exists_act_coeV N H S₀ t i
    exact ⟨G', hG'.symm⟩⟩
  map_add' t t' := by
    funext i
    apply Subtype.ext
    change act N H S₀ (t + t') (coeV N H (i : H1 N H ℤ)) = act N H S₀ t (coeV N H i) + act N H S₀ t' (coeV N H i)
    rw [map_add, LinearMap.add_apply]
  map_smul' n t := by
    funext i
    apply Subtype.ext
    change act N H S₀ (n • t) (coeV N H (i : H1 N H ℤ)) = n • act N H S₀ t (coeV N H i)
    rw [map_zsmul, LinearMap.smul_apply]

theorem coe_ψ_apply (s : Finset (H1 N H ℤ)) (t : T N H S₀) (i : ↥s) :
    ((ψ N H S₀ s t i : Lat N H) : Vp N H) = act N H S₀ t (coeV N H (i : H1 N H ℤ)) := rfl

theorem ψ_injective (s : Finset (H1 N H ℤ)) (hs : Submodule.span ℤ (s : Set (H1 N H ℤ)) = ⊤) :
    Function.Injective (ψ N H S₀ s) := by
  intro t t' htt'
  rw [← sub_eq_zero]
  apply act_injective N H S₀
  rw [map_zero]
  have hzero : ∀ i : ↥s, act N H S₀ (t - t') (coeV N H (i : H1 N H ℤ)) = 0 := by
    intro i
    have := congrArg (fun f : ↥s → Lat N H => ((f i : Lat N H) : Vp N H)) htt'
    simp only [coe_ψ_apply] at this
    rw [map_sub, LinearMap.sub_apply, this, sub_self]

  have hlat : ∀ G : H1 N H ℤ, act N H S₀ (t - t') (coeV N H G) = 0 := by
    intro G
    have hG : G ∈ Submodule.span ℤ (s : Set (H1 N H ℤ)) := by rw [hs]; exact Submodule.mem_top
    induction hG using Submodule.span_induction with
    | mem w hw => exact hzero ⟨w, hw⟩
    | zero => rw [map_zero, map_zero]
    | add u w _ _ hu hw => rw [map_add, map_add, hu, hw, add_zero]
    | smul n w _ hw => rw [map_zsmul, map_zsmul, hw, smul_zero]

  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨G, rfl⟩ := hw
    exact hlat G
  | zero =>
    have : (⟨0, Submodule.zero_mem (Vp N H)⟩ : Vp N H) = 0 := rfl
    rw [this, map_zero]
  | add u w hu hw ihu ihw =>
    have : (⟨u + w, add_mem hu hw⟩ : Vp N H) = ⟨u, hu⟩ + ⟨w, hw⟩ := rfl
    rw [this, map_add, ihu, ihw, add_zero]
  | smul c' w hw ihw =>
    have : (⟨c' • w, Submodule.smul_mem (Vp N H) c' hw⟩ : Vp N H) = c' • ⟨w, hw⟩ := rfl
    rw [this, map_smul, ihw, smul_zero]

theorem moduleFinite_T : Module.Finite ℤ (T N H S₀) := by
  obtain ⟨s, hs⟩ := (instModuleFiniteLattice N H).fg_top
  exact Module.Finite.of_injective (ψ N H S₀ s) (ψ_injective N H S₀ s hs)

noncomputable def chiOf {κ : Type} [Field κ] {x : H1 N H κ} (c : R N S₀ → κ)
    (hc : ∀ P, ev N H S₀ κ P x = c P • x) (hcancel : ∀ {a b : κ}, a • x = b • x → a = b) : R N S₀ →+* κ where
  toFun := c
  map_one' := by
    apply hcancel
    rw [← hc 1, map_one, Module.End.one_apply, one_smul]
  map_mul' P Q := by
    apply hcancel
    rw [← hc (P * Q), map_mul, Module.End.mul_apply, hc Q, map_smul, hc P, smul_smul, mul_comm]
  map_zero' := by
    apply hcancel
    rw [← hc 0, map_zero, LinearMap.zero_apply, zero_smul]
  map_add' P Q := by
    apply hcancel
    rw [← hc (P + Q), map_add, LinearMap.add_apply, hc P, hc Q, add_smul]

theorem chiOf_apply {κ : Type} [Field κ] {x : H1 N H κ} (c : R N S₀ → κ)
    (hc : ∀ P, ev N H S₀ κ P x = c P • x) (hcancel : ∀ {a b : κ}, a • x = b • x → a = b) (P : R N S₀) :
    chiOf N H S₀ c hc hcancel P = c P := rfl

end Order

end HeckeLatticeLift
p2m_reactivate "P2MW.S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int.HeckeLatticeLift"

open HeckeLatticeLift CohCarrier in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S₀ : Set ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (x : CohCarrier.H1 N H κ) (hx0 : x ≠ 0)
    (hx : x ∈ Submodule.span κ
      (Set.range fun G : CohCarrier.H1 N H ℤ => (Int.castAddHom κ).comp G))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ κ x) = lam ℓ • x) :
    ∃ (X : CohCarrier.H1 N H ℂ) (θ : ℕ → integralClosure ℤ ℂ) (φ' : integralClosure ℤ ℂ →+* κ),
      X ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N H ℓ ℂ X) =
          ((θ ℓ : integralClosure ℤ ℂ) : ℂ) • X) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → φ' (θ ℓ) = lam ℓ) := by
  classical

  have heigen : ∀ P : R N S₀, ∃ c : κ, ev N H S₀ κ P x = c • x := by
    intro P
    induction P using FreeAlgebra.induction with
    | grade0 r =>
      refine ⟨(r : κ), ?_⟩
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
        Int.cast_smul_eq_zsmul]
    | grade1 ℓ =>
      refine ⟨lam ℓ.1, ?_⟩
      rw [ev_ι, Tgen_apply]
      exact hT ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2
    | mul a b iha ihb =>
      obtain ⟨ca, ha⟩ := iha
      obtain ⟨cb, hb⟩ := ihb
      refine ⟨ca * cb, ?_⟩
      rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
    | add a b iha ihb =>
      obtain ⟨ca, ha⟩ := iha
      obtain ⟨cb, hb⟩ := ihb
      refine ⟨ca + cb, ?_⟩
      rw [map_add, LinearMap.add_apply, ha, hb, add_smul]
  have hcancel : ∀ {a b : κ}, a • x = b • x → a = b := by
    intro a b h
    by_contra hab
    apply hx0
    have h2 : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hab)
  obtain ⟨c, hc⟩ : ∃ c : R N S₀ → κ, ∀ P, ev N H S₀ κ P x = c P • x :=
    ⟨fun P => (heigen P).choose, fun P => (heigen P).choose_spec⟩
  let χ₀ : R N S₀ →+* κ := chiOf N H S₀ c hc hcancel
  have hχ₀ : ∀ P : R N S₀, ev N H S₀ κ P x = χ₀ P • x := fun P => by rw [chiOf_apply]; exact hc P
  have hχ₀ι : ∀ ℓ : GoodPrime N S₀, χ₀ (FreeAlgebra.ι ℤ ℓ) = lam ℓ.1 := by
    intro ℓ
    apply hcancel
    rw [← hχ₀, ev_ι, Tgen_apply]
    exact hT ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2

  haveI hTfin : Module.Finite ℤ (T N H S₀) := moduleFinite_T N H S₀

  have hker : ∀ P : R N S₀, evV N H S₀ P = 0 → χ₀ P = 0 := by
    intro P hP

    have hlat : ∀ G : H1 N H ℤ, ev N H S₀ ℤ P G = 0 := by
      intro G
      apply coe_injective_complex N H
      rw [map_zero, ← ev_coe, ← coe_coeV, ← coe_evV N H S₀ P, hP]
      rfl

    have hspan : ∀ v ∈ Submodule.span κ (Set.range fun G : H1 N H ℤ => (Int.castAddHom κ).comp G),
        ev N H S₀ κ P v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨G, rfl⟩ := hw
        change ev N H S₀ κ P (coe N H κ G) = 0
        rw [ev_coe, hlat, map_zero]
      | zero => rw [map_zero]
      | add u w _ _ hu hw => rw [map_add, hu, hw, add_zero]
      | smul c' w _ hw => rw [map_smul, hw, smul_zero]
    apply hcancel
    rw [← hχ₀, hspan x hx, zero_smul]
  let χT : T N H S₀ →+* κ := liftT N H S₀ χ₀ hker
  have hχT : ∀ P : R N S₀, χT (mkT N H S₀ P) = χ₀ P := fun P => liftT_mkT N H S₀ χ₀ hker P
  set 𝔪 : Ideal (T N H S₀) := RingHom.ker χT with h𝔪def
  haveI h𝔪max : 𝔪.IsMaximal := ker_isMaximal' p χT
  have hsupp : Module.annihilator (T N H S₀) (Vp N H) ≤ 𝔪 := by
    intro t ht
    rw [Module.mem_annihilator] at ht
    have : t = 0 := by
      apply act_injective N H S₀
      rw [map_zero]
      exact LinearMap.ext fun v => ht v
    rw [this]
    exact zero_mem 𝔪

  obtain ⟨χ, 𝔪', h𝔪', hcomap, X, hX0, hXeig⟩ :=
    DeligneSerre.exists_eigencharacter_of_annihilator_le (V := Vp N H) (T := T N H S₀) 𝔪 hsupp

  haveI : Finite (T N H S₀ ⧸ 𝔪) := finite_quotient_ker p χT
  letI : Field (T N H S₀ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : 𝔪'.IsMaximal := h𝔪'
  letI : Field (integralClosure ℤ ℂ ⧸ 𝔪') := Ideal.Quotient.field 𝔪'
  have hle : 𝔪 ≤ 𝔪'.comap χ := hcomap ▸ le_rfl
  let j₁ : T N H S₀ ⧸ 𝔪 →+* integralClosure ℤ ℂ ⧸ 𝔪' := Ideal.quotientMap 𝔪' χ hle
  letI : Algebra (T N H S₀ ⧸ 𝔪) (integralClosure ℤ ℂ ⧸ 𝔪') := j₁.toAlgebra
  haveI : Algebra.IsIntegral (T N H S₀ ⧸ 𝔪) (integralClosure ℤ ℂ ⧸ 𝔪') := ⟨fun y => by
    haveI : Algebra.IsIntegral ℤ (integralClosure ℤ ℂ ⧸ 𝔪') := inferInstance
    obtain ⟨P, hPm, hPy⟩ : IsIntegral ℤ y := Algebra.IsIntegral.isIntegral y
    refine ⟨P.map (algebraMap ℤ (T N H S₀ ⧸ 𝔪)), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (T N H S₀ ⧸ 𝔪) (integralClosure ℤ ℂ ⧸ 𝔪')).comp
        (algebraMap ℤ (T N H S₀ ⧸ 𝔪))) (algebraMap ℤ (integralClosure ℤ ℂ ⧸ 𝔪'))]
    exact hPy⟩
  haveI : Algebra.IsAlgebraic (T N H S₀ ⧸ 𝔪) (integralClosure ℤ ℂ ⧸ 𝔪') := Algebra.IsIntegral.isAlgebraic
  let g : T N H S₀ ⧸ 𝔪 →+* κ := RingHom.kerLift χT
  have hg : ∀ t : T N H S₀, g (Ideal.Quotient.mk 𝔪 t) = χT t := fun t => RingHom.kerLift_mk χT t
  haveI : (RingHom.ker φ).IsMaximal := ker_isMaximal φ p
  obtain ⟨e, he⟩ := exists_ringHom_comp_algebraMap_eq φ (integralClosure ℤ ℂ ⧸ 𝔪') g
  have hej : ∀ y : T N H S₀ ⧸ 𝔪, e (j₁ y) = g y := fun y => by
    have := congrArg (fun f => f y) he
    simp only [RingHom.comp_apply] at this
    exact this
  set φ' : integralClosure ℤ ℂ →+* κ := e.comp (Ideal.Quotient.mk 𝔪') with hφ'def
  have hφ'χ : ∀ t : T N H S₀, φ' (χ t) = χT t := by
    intro t
    rw [hφ'def, RingHom.comp_apply, ← hg, ← hej]
    exact congrArg e ((Ideal.quotientMap_mk (I := 𝔪') (f := χ) (H := hle) (x := t)).symm)

  let θ : ℕ → integralClosure ℤ ℂ := fun ℓ =>
    if h : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀ then χ (mkT N H S₀ (FreeAlgebra.ι ℤ (⟨ℓ, h⟩ : GoodPrime N S₀)))
    else 0
  refine ⟨(X : H1 N H ℂ), θ, φ', ?_, ?_, ?_⟩
  · exact fun h => hX0 (Subtype.ext h)
  · intro ℓ hℓ hℓN hℓS
    have hgood : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀ := ⟨hℓ, hℓN, hℓS⟩
    have hθ : θ ℓ = χ (mkT N H S₀ (FreeAlgebra.ι ℤ (⟨ℓ, hgood⟩ : GoodPrime N S₀))) := dif_pos hgood
    have h1 := hXeig (mkT N H S₀ (FreeAlgebra.ι ℤ (⟨ℓ, hgood⟩ : GoodPrime N S₀)))
    have h2 := ev_eq_smul_of_mkT_smul N H S₀ _ X _ h1
    rw [ev_ι, Tgen_apply] at h2
    rw [hθ]
    exact h2
  · intro ℓ hℓ hℓN hℓS
    have hgood : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀ := ⟨hℓ, hℓN, hℓS⟩
    have hθ : θ ℓ = χ (mkT N H S₀ (FreeAlgebra.ι ℤ (⟨ℓ, hgood⟩ : GoodPrime N S₀))) := dif_pos hgood
    rw [hθ, hφ'χ, hχT, hχ₀ι]

end S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
end P2MW
export P2MW.S_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int (solution)
