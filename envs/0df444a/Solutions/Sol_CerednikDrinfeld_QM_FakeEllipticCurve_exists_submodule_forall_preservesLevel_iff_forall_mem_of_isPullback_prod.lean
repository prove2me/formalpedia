-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/31dcbc21-9844-5224-8d4d-d15b457770b1

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_iff_forall_factorsThrough_geomPoint_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM

namespace S1Asm

variable {R : Type} [CommRing R]

theorem mapPt_one {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  letI := L'.pointGroup t
  have h := hhom t (L.one t) (L.one t)
  rw [L.one_mul] at h
  have h2 : (mapPt φ hφ (L.one t)) * (mapPt φ hφ (L.one t)) = (mapPt φ hφ (L.one t)) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem mapPt_nsmulPt {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hhom t
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hhom, ih]

theorem equiv_zero_eq_one {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) {V : Type} [AddCommGroup V] {p : SchemeHomOver t f → Prop}
    (e : V ≃ {Q : SchemeHomOver t f // p Q})
    (he : ∀ v w : V, ((e (v + w)) : SchemeHomOver t f) = L.mul t (e v) (e w)) :
    ((e 0) : SchemeHomOver t f) = L.one t := by
  letI := L.pointGroup t
  have h := he 0 0
  rw [add_zero] at h
  have h2 : ((e 0 : SchemeHomOver t f)) * (e 0 : SchemeHomOver t f) = (e 0 : SchemeHomOver t f) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

end S1Asm

open S1Asm in
theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)
    (hN : Squarefree N)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (hNk : (N : k₀) ≠ 0)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (A₀ : FakeEllipticCurve Λ N k₀)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k₀)) (L : RelativeGroupLaw k₀ f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))
    (hH' : IsDefiniteRamifiedExactlyAt c d r) (hOmax : IsMaximalOrder O)

    (eN : (Fin 2 → ZMod N) ≃
        {Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f //
          nsmulPt L (geomPoint k₀ (RingHom.id k₀)) N Q = L.one (geomPoint k₀ (RingHom.id k₀))})
    (μ : ↥O → Matrix (Fin 2) (Fin 2) (ZMod N))
    (heN_add : ∀ v w : Fin 2 → ZMod N,
      ((eN (v + w)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) = L.mul (geomPoint k₀ (RingHom.id k₀)) (eN v) (eN w))
    (heN_act : ∀ (x : ↥O) (v : Fin 2 → ZMod N),
      pushPt (ε x) (hε x) ((eN v) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) = eN (Matrix.mulVec (μ x) v))
    (hμ_surj : Function.Surjective μ)
    (hμ_ker : ∀ x : ↥O, μ x = 0 ↔ ∃ y : ↥O, (x : ℍ[ℚ, c, d]) = (N : ℚ) • (y : ℍ[ℚ, c, d]))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    ∃ W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N),

      (∀ (Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f) (w : Fin 2 → Fin 2 → ZMod N),
          mapPt p₁ hp₁ Q = ((eN (w 0)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) →
          mapPt p₂ hp₂ Q = ((eN (w 1)) : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f) →
          (w ∈ W ↔ FactorsThrough A₀.lev Q)) ∧

      (∀ (m : ↥Λ) (w : Fin 2 → Fin 2 → ZMod N), w ∈ W →
          (fun i => ∑ l, Matrix.mulVec (μ ⟨j (m : ℍ[ℚ, a, b]) i l, hj m i l⟩) (w l)) ∈ W) ∧
      Nat.card ↥W = N ^ 2 ∧

      (∀ (x : ℍ[ℚ, a₁, b₁]) (hx : x ∈ R),
          FakeEllipticCurve.PreservesLevel A₀ A₀ (E (τ x) ((hRiff x).1 hx)) (hE _ ((hRiff x).1 hx)) ↔
            ∀ w : Fin 2 → Fin 2 → ZMod N, w ∈ W → (fun i => ∑ l, Matrix.mulVec (μ ⟨τ x i l, (hRiff x).1 hx i l⟩) (w l)) ∈ W) := by
  classical

  have hw : ∀ (P Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) f), P.1 ≫ f = Q.1 ≫ f := fun P Q => P.2.trans Q.2.symm
  let pt : (Fin 2 → Fin 2 → ZMod N) → SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f := fun w =>
    ⟨hpb.lift (eN (w 0)).1.1 (eN (w 1)).1.1 (hw _ _), by
      rw [← hp₁, ← Category.assoc, hpb.lift_fst]; exact (eN (w 0)).1.2⟩
  have pt_fst : ∀ w, mapPt p₁ hp₁ (pt w) = (eN (w 0)).1 := fun w => Subtype.ext (hpb.lift_fst _ _ _)
  have pt_snd : ∀ w, mapPt p₂ hp₂ (pt w) = (eN (w 1)).1 := fun w => Subtype.ext (hpb.lift_snd _ _ _)
  have pt_ext : ∀ (Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f) (w : Fin 2 → Fin 2 → ZMod N),
      mapPt p₁ hp₁ Q = (eN (w 0)).1 → mapPt p₂ hp₂ Q = (eN (w 1)).1 → Q = pt w := by
    intro Q w h1 h2
    apply Subtype.ext
    apply hpb.hom_ext
    · rw [hpb.lift_fst]; exact congrArg Subtype.val h1
    · rw [hpb.lift_snd]; exact congrArg Subtype.val h2

  have pt_add : ∀ w w', pt (w + w') = A₀.L.mul (geomPoint k₀ (RingHom.id k₀)) (pt w) (pt w') := by
    intro w w'
    refine (pt_ext _ _ ?_ ?_).symm
    · rw [(hp_hom (geomPoint k₀ (RingHom.id k₀)) _ _).1, pt_fst, pt_fst]; exact (heN_add _ _).symm
    · rw [(hp_hom (geomPoint k₀ (RingHom.id k₀)) _ _).2, pt_snd, pt_snd]; exact (heN_add _ _).symm

  have pt_blk : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (w : Fin 2 → Fin 2 → ZMod N),
      mapPt (E y hy) (hE y hy) (pt w) = pt (fun i => ∑ l, Matrix.mulVec (μ ⟨y i l, hy i l⟩) (w l)) := by
    intro y hy w
    have hm := hE_mat y hy (geomPoint k₀ (RingHom.id k₀)) (pt w)
    refine pt_ext (mapPt (E y hy) (hE y hy) (pt w)) (fun i => ∑ l, Matrix.mulVec (μ ⟨y i l, hy i l⟩) (w l)) ?_ ?_
    · rw [show mapPt p₁ hp₁ (mapPt (E y hy) (hE y hy) (pt w)) = _ from hm.1, pt_fst, pt_snd]
      show L.mul (geomPoint k₀ (RingHom.id k₀)) (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (eN (w 0)).1) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (eN (w 1)).1) = _
      rw [heN_act, heN_act, ← heN_add]
      simp only [Fin.sum_univ_two]
    · rw [show mapPt p₂ hp₂ (mapPt (E y hy) (hE y hy) (pt w)) = _ from hm.2, pt_fst, pt_snd]
      show L.mul (geomPoint k₀ (RingHom.id k₀)) (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (eN (w 0)).1) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (eN (w 1)).1) = _
      rw [heN_act, heN_act, ← heN_add]
      simp only [Fin.sum_univ_two]

  have pt_zero : pt 0 = A₀.L.one (geomPoint k₀ (RingHom.id k₀)) := by
    refine (pt_ext _ _ ?_ ?_).symm
    · rw [mapPt_one A₀.L L p₁ hp₁ (fun t P Q => (hp_hom t P Q).1)]
      exact (equiv_zero_eq_one L (geomPoint k₀ (RingHom.id k₀)) eN heN_add).symm
    · rw [mapPt_one A₀.L L p₂ hp₂ (fun t P Q => (hp_hom t P Q).2)]
      exact (equiv_zero_eq_one L (geomPoint k₀ (RingHom.id k₀)) eN heN_add).symm

  have hNsmul : ∀ w : Fin 2 → Fin 2 → ZMod N, N • w = 0 := fun w =>
    calc N • w = ((N : ℕ) : ZMod N) • w := (Nat.cast_smul_eq_nsmul (ZMod N) N w).symm
      _ = 0 := by
        have h0 : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
        simp only [h0, zero_smul]
  let W₀ : AddSubgroup (Fin 2 → Fin 2 → ZMod N) :=
    { carrier := {w | FactorsThrough A₀.lev (pt w)}
      zero_mem' := by
        show FactorsThrough A₀.lev (pt 0)
        rw [pt_zero]; exact A₀.lev_one (geomPoint k₀ (RingHom.id k₀))
      add_mem' := fun {w w'} hw hw' => by
        show FactorsThrough A₀.lev (pt (w + w'))
        rw [pt_add]; exact (A₀.lev_sub (geomPoint k₀ (RingHom.id k₀)) _ _ hw hw').1
      neg_mem' := fun {w} hw => by
        show FactorsThrough A₀.lev (pt (-w))
        have hN1 : -w = (N - 1) • w := by
          have h2 : (N - 1) • w + w = 0 := by
            rw [← succ_nsmul, Nat.sub_add_cancel (NeZero.one_le (n := N))]
            exact hNsmul w
          exact neg_eq_of_add_eq_zero_left h2
        rw [hN1]
        induction (N - 1) with
        | zero => show FactorsThrough A₀.lev (pt ((0 : ℕ) • w)); rw [zero_nsmul, pt_zero]; exact A₀.lev_one (geomPoint k₀ (RingHom.id k₀))
        | succ n ih => rw [succ_nsmul, pt_add]; exact (A₀.lev_sub (geomPoint k₀ (RingHom.id k₀)) _ _ ih hw).1 }
  let W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N) := AddSubgroup.toZModSubmodule N W₀
  have mem_W : ∀ w, w ∈ W ↔ FactorsThrough A₀.lev (pt w) := by
    intro w
    show w ∈ ((AddSubgroup.toZModSubmodule N W₀ : Submodule (ZMod N) _) : Set _) ↔ _
    rw [AddSubgroup.coe_toZModSubmodule]; rfl

  have tors₁ : ∀ Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f, FactorsThrough A₀.lev Q → nsmulPt L (geomPoint k₀ (RingHom.id k₀)) N (mapPt p₁ hp₁ Q) = L.one (geomPoint k₀ (RingHom.id k₀)) := by
    intro Q hQ
    rw [← mapPt_nsmulPt A₀.L L p₁ hp₁ (fun t P Q => (hp_hom t P Q).1), A₀.lev_torsion (geomPoint k₀ (RingHom.id k₀)) Q hQ]
    exact mapPt_one A₀.L L p₁ hp₁ (fun t P Q => (hp_hom t P Q).1) (geomPoint k₀ (RingHom.id k₀))
  have tors₂ : ∀ Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f, FactorsThrough A₀.lev Q → nsmulPt L (geomPoint k₀ (RingHom.id k₀)) N (mapPt p₂ hp₂ Q) = L.one (geomPoint k₀ (RingHom.id k₀)) := by
    intro Q hQ
    rw [← mapPt_nsmulPt A₀.L L p₂ hp₂ (fun t P Q => (hp_hom t P Q).2), A₀.lev_torsion (geomPoint k₀ (RingHom.id k₀)) Q hQ]
    exact mapPt_one A₀.L L p₂ hp₂ (fun t P Q => (hp_hom t P Q).2) (geomPoint k₀ (RingHom.id k₀))
  let wOf : ∀ Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f, FactorsThrough A₀.lev Q → (Fin 2 → Fin 2 → ZMod N) := fun Q hQ =>
    ![eN.symm ⟨mapPt p₁ hp₁ Q, tors₁ Q hQ⟩, eN.symm ⟨mapPt p₂ hp₂ Q, tors₂ Q hQ⟩]
  have pt_wOf : ∀ (Q : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f) (hQ : FactorsThrough A₀.lev Q), pt (wOf Q hQ) = Q := by
    intro Q hQ
    refine (pt_ext _ _ ?_ ?_).symm
    · show mapPt p₁ hp₁ Q = (eN (eN.symm ⟨mapPt p₁ hp₁ Q, tors₁ Q hQ⟩)).1
      rw [Equiv.apply_symm_apply]
    · show mapPt p₂ hp₂ Q = (eN (eN.symm ⟨mapPt p₂ hp₂ Q, tors₂ Q hQ⟩)).1
      rw [Equiv.apply_symm_apply]

  have hcard : Nat.card ↥W = N ^ 2 := by
    obtain ⟨e, -⟩ := A₀.lev_fibre k₀ (RingHom.id k₀) hNk
    have h1 : Nat.card ↥W = Nat.card {P : SchemeHomOver (geomPoint k₀ (RingHom.id k₀)) A₀.f // FactorsThrough A₀.lev P} := by
      refine Nat.card_congr
        { toFun := fun w => ⟨pt w.1, (mem_W _).1 w.2⟩
          invFun := fun Q => ⟨wOf Q.1 Q.2, (mem_W _).2 (by rw [pt_wOf Q.1 Q.2]; exact Q.2)⟩
          left_inv := ?_
          right_inv := fun Q => Subtype.ext (pt_wOf Q.1 Q.2) }
      intro w
      apply Subtype.ext
      funext i
      show (![eN.symm ⟨mapPt p₁ hp₁ (pt w.1), _⟩, eN.symm ⟨mapPt p₂ hp₂ (pt w.1), _⟩] : Fin 2 → Fin 2 → ZMod N) i = w.1 i
      fin_cases i
      · show eN.symm ⟨mapPt p₁ hp₁ (pt w.1), _⟩ = w.1 0
        apply eN.injective; rw [Equiv.apply_symm_apply]; exact Subtype.ext (pt_fst _)
      · show eN.symm ⟨mapPt p₂ hp₂ (pt w.1), _⟩ = w.1 1
        apply eN.injective; rw [Equiv.apply_symm_apply]; exact Subtype.ext (pt_snd _)
    rw [h1, ← Nat.card_congr e, Nat.card_prod, Nat.card_zmod, pow_two]
  refine ⟨W, ?_, ?_, hcard, ?_⟩
  ·
    intro Q w h1 h2
    rw [mem_W, ← pt_ext Q w h1 h2]
  ·
    intro m w hw
    rw [mem_W] at hw ⊢
    rw [← pt_blk (j (m : ℍ[ℚ, a, b])) (hj m) w]
    have hs := A₀.lev_stable m (geomPoint k₀ (RingHom.id k₀)) (pt w) hw
    have heq : pushPt (A₀.act m) (A₀.act_over m) (pt w) = mapPt (E (j (m : ℍ[ℚ, a, b])) (hj m)) (hE _ (hj m)) (pt w) := by
      apply Subtype.ext
      show (pt w).1 ≫ A₀.act m = (pt w).1 ≫ E (j (m : ℍ[ℚ, a, b])) (hj m)
      rw [hact]
    rwa [heq] at hs
  ·
    intro x hx
    rw [FakeEllipticCurve.preservesLevel_iff_forall_factorsThrough_geomPoint_of_isAlgClosed k₀ hNk A₀ A₀]
    constructor
    · intro H w hw
      rw [mem_W] at hw ⊢
      rw [← pt_blk]
      exact H (pt w) hw
    · intro H Q hQ
      obtain ⟨w, hQw⟩ : ∃ w, Q = pt w := ⟨wOf Q hQ, (pt_wOf Q hQ).symm⟩
      rw [hQw] at hQ ⊢
      rw [pt_blk]
      exact (mem_W _).1 (H w ((mem_W _).2 hQ))

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_preservesLevel_iff_forall_mem_of_isPullback_prod (solution)
