-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.quotient_generic_section_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:32.944994+00:00
-- url     : https://prove2.me/submissions/746f925f-bf04-46e6-9225-1dd07f724404

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC
import Theorems.Thm_Formalism_L2_Pj_GenSect_algKTR_apply
import Theorems.Thm_Formalism_L2_Pj_GenSect_Phi_algebraMap
import Theorems.Thm_P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
import Theorems.Thm_Formalism_L2_Pj_GenSect_ker_Phi
import Theorems.Thm_Formalism_L2_Pj_GenSect_gs_alg
import Theorems.Thm_Formalism_L2_Pj_GenSect_gs_indep
import Theorems.Thm_Formalism_L2_Pj_GenSect_halg_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (KTf K D m) E), FiniteDimensional (KTf K D m) E ∧
      Nonempty ((RS K Ω D m ⧸ Is K x) ≃ₐ[KTf K D m] E) := by
  classical
  have halg := halg_of x j₀ htr hbig
  have hind := gs_indep x j₀ hx₀ htr halg
  have hal := gs_alg x j₀ hx₀ htr halg
  have hI : Function.Injective (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀) := hind
  have hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0 := fun q hq h =>
    hq (hI (h.trans (map_zero _).symm))
  let χ : KT K D m →+* FractionRing (CT Ω D j₀) :=
    (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
      (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀).toRingHom
  have hχ : Function.Injective χ :=
    (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp hI
  letI : Algebra (KT K D m) (FractionRing (CT Ω D j₀)) := χ.toAlgebra
  letI : Algebra (KTf K D m) (FractionRing (CT Ω D j₀)) := (IsFractionRing.lift hχ).toAlgebra
  haveI : IsScalarTower (KT K D m) (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    IsScalarTower.of_algebraMap_eq fun q => (IsFractionRing.lift_algebraMap hχ q).symm
  have key : ∀ r : KTf K D m, Phi x j₀ hinj (algebraMap (KTf K D m) (RS K Ω D m) r) =
      IsFractionRing.lift hχ r := by
    have h : (Phi x j₀ hinj).comp (algebraMap (KTf K D m) (RS K Ω D m)) = IsFractionRing.lift hχ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [algKTR_apply, Phi_algebraMap, psi_kt, IsFractionRing.lift_algebraMap]
      rfl
    exact fun r => RingHom.congr_fun h r
  let ΦK : RS K Ω D m →ₐ[KTf K D m] FractionRing (CT Ω D j₀) :=
    { Phi x j₀ hinj with commutes' := key }
  have hint : ∀ c : CT Ω D j₀,
      IsIntegral (KTf K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
    intro c
    haveI := hal
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range (gs (D := D) x j₀))) c
    let e := hind.aevalEquiv
    have hKT : IsAlgebraic (KT K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
      refine ⟨p.map (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff e.symm.injective).2 hp0
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap (KT K D m) (FractionRing (CT Ω D j₀))).comp
              (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m) =
            (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
              (algebraMap (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀)) := by
          refine RingHom.ext fun a => ?_
          simp only [RingHom.comp_apply]
          show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (e.symm a)) = _
          rw [← hind.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
        rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
    exact (hKT.extendScalars (IsFractionRing.injective (KT K D m) (KTf K D m))).isIntegral
  obtain ⟨t, ht⟩ := hfg
  let G : Set (FractionRing (CT Ω D j₀)) :=
    Set.range (fun v => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (X v)) ∪
      (fun ω => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω)) '' (t : Set Ω)
  haveI : Finite G := ((Set.finite_range _).union (t.finite_toSet.image _)).to_subtype
  let E' := IntermediateField.adjoin (KTf K D m) G
  haveI hfd : FiniteDimensional (KTf K D m) E' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ (⟨v, rfl⟩ | ⟨ω, _, rfl⟩) <;> exact hint _)
  have hK : ∀ k : K, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))
      (MvPolynomial.C (algebraMap K Ω k)) ∈ E' := by
    intro k
    have e1 : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) =
        algebraMap (KTf K D m) (FractionRing (CT Ω D j₀))
          (algebraMap (KT K D m) (KTf K D m) (MvPolynomial.C k)) := by
      rw [← IsScalarTower.algebraMap_apply]
      show _ = algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (MvPolynomial.C k))
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]
    rw [e1]
    exact E'.algebraMap_mem _
  have hΩ : ∀ ω : Ω, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω) ∈ E' := by
    let θ : Ω →+* FractionRing (CT Ω D j₀) :=
      (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp MvPolynomial.C
    let Si : IntermediateField K Ω := Subfield.toIntermediateField (E'.toSubfield.comap θ) (fun k => hK k)
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ Si := by
      rw [IntermediateField.adjoin_le_iff]
      intro ω hω
      exact IntermediateField.subset_adjoin (KTf K D m) G (Or.inr ⟨ω, hω, rfl⟩)
    intro ω
    have hω : ω ∈ IntermediateField.adjoin K (t : Set Ω) := by
      rw [ht]
      exact IntermediateField.mem_top
    exact hle hω
  have hmemC : ∀ c : CT Ω D j₀, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c ∈ E' := by
    intro c
    apply MvPolynomial.induction_on c
    · intro ω
      exact hΩ ω
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro p v hp
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin (KTf K D m) G (Or.inl ⟨v, rfl⟩))
  have hrange : ∀ r : RS K Ω D m, Phi x j₀ hinj r ∈ E' := by
    intro r
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, Phi_algebraMap]
    refine mul_mem (hmemC _) ?_
    have hy : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) ≠ 0 := by
      obtain ⟨q, hq, hqy⟩ := y.2
      rw [← hqy, psi_kt]
      intro h
      exact hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm))
    have h1 : Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) (1 : ΩT Ω D m) y) =
        (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y))⁻¹ := by
      rw [Phi_mk'_spec, map_one, map_one, mul_inv_cancel₀ hy]
    rw [h1]
    exact inv_mem (hmemC _)
  let S := ΦK.range
  let L : S →ₗ[KTf K D m] E' :=
    { toFun := fun s => ⟨s.1, by
        obtain ⟨r, hr⟩ := (AlgHom.mem_range ΦK).1 s.2
        rw [← hr]
        exact hrange r⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional (KTf K D m) S :=
    FiniteDimensional.of_injective L (by
      intro a b h
      have h' := congrArg (fun e : E' => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')
  have hSf : IsField S :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap (KTf K D m) S).injective).1 (Field.toIsField _)
  let E := S.toIntermediateField' hSf
  let g : RS K Ω D m →ₐ[KTf K D m] E :=
    { toFun := fun r => ⟨ΦK r, ΦK.mem_range_self r⟩
      map_one' := Subtype.ext (map_one ΦK)
      map_mul' := fun a b => Subtype.ext (map_mul ΦK a b)
      map_zero' := Subtype.ext (map_zero ΦK)
      map_add' := fun a b => Subtype.ext (map_add ΦK a b)
      commutes' := fun r => Subtype.ext (ΦK.commutes r) }
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨r, rfl⟩ := (AlgHom.mem_range ΦK).1 (show v ∈ S from hv)
    exact ⟨r, rfl⟩
  have hker : RingHom.ker g = Is K x := by
    rw [ker_Phi x j₀ hx₀ hinj]
    ext r
    simp only [RingHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨E, inferInstance, inferInstance, ?_, ⟨(Ideal.quotientEquivAlgOfEq (KTf K D m) hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)⟩⟩
  exact FiniteDimensional.of_injective
    ({ toFun := fun e => (⟨e.1, e.2⟩ : S), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      E →ₗ[KTf K D m] S)
    (by
      intro a b h
      have h' := congrArg (fun e : S => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')
end Formalism.L2.Pj.GenSect
