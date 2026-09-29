-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_lift_of_forall_isNoetherianRing_existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/229ee361-778a-5ba9-af7e-4efaae749aa1

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst

import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_lift_of_forall_isNoetherianRing_existsUnique_lift
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace EtExist

p2m_open "CerednikDrinfeld.FormalOmega.AlgFunctor"

variable {𝒪 : Type} [CommRing 𝒪]

theorem isNilpotent_subalgebra (π : 𝒪) {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (S : Subalgebra 𝒪 B) : IsNilpotent (algebraMap 𝒪 ↥S π) := by
  obtain ⟨n, hn⟩ := hB
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : (S.val (algebraMap 𝒪 ↥S π ^ n) : B) = algebraMap 𝒪 B π ^ n := by
    rw [map_pow, AlgHom.commutes]
  rw [Subalgebra.coe_val] at h1
  rw [h1, hn]
  rfl

noncomputable def restr {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (S : Subalgebra 𝒪 B) : ↥S →ₐ[𝒪] ↥(S.map φ) :=
  (φ.comp S.val).codRestrict (S.map φ) (fun y => Subalgebra.mem_map.2 ⟨y.1, y.2, rfl⟩)

theorem val_comp_restr {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (S : Subalgebra 𝒪 B) : (S.map φ).val.comp (restr φ S) = φ.comp S.val :=
  AlgHom.ext fun _ => rfl

theorem restr_surjective {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (S : Subalgebra 𝒪 B) : Function.Surjective (restr φ S) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.1 hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem restr_sqzero {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (hsq : ∀ s t : B, φ s = 0 → φ t = 0 → s * t = 0) (S : Subalgebra 𝒪 B) :
    ∀ s t : ↥S, restr φ S s = 0 → restr φ S t = 0 → s * t = 0 := by
  intro s t hs ht
  apply Subtype.ext
  exact hsq s.1 t.1 (congrArg Subtype.val hs) (congrArg Subtype.val ht)

theorem restr_comp_inclusion {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') {S S' : Subalgebra 𝒪 B} (h : S ≤ S') :
    (restr φ S').comp (Subalgebra.inclusion h) = (Subalgebra.inclusion (Subalgebra.map_mono h)).comp (restr φ S) :=
  AlgHom.ext fun _ => rfl

section src

variable {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] {B : Type} [CommRing B] [Algebra 𝒪 B]

def Src (ψ : Onr →ₐ[𝒪] B) (s : Finset B) : Subalgebra 𝒪 B := Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B))

theorem Src_mono (ψ : Onr →ₐ[𝒪] B) {s t : Finset B} (h : s ⊆ t) : Src ψ s ≤ Src ψ t :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))

theorem map_Src [DecidableEq B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] [DecidableEq B'] (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (s : Finset B) :
    (Src ψ s).map φ = Src (φ.comp ψ) (s.image φ) := by
  rw [Src, Src, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image]
  rfl

theorem restrictScalars_adjoin_range (ψ : Onr →ₐ[𝒪] B) (t : Finset B) :
    (Algebra.adjoin (↥ψ.range) (↑t : Set B)).restrictScalars 𝒪 = Src ψ t := by
  rw [Algebra.restrictScalars_adjoin, AlgHom.coe_range]
  rfl

theorem le_Src_of_subset (ψ : Onr →ₐ[𝒪] B) {S : Subalgebra 𝒪 B} {t s : Finset B} (hS : S = Src ψ t) (h : t ⊆ s) :
    S ≤ Src ψ s := hS ▸ Src_mono ψ h

end src

end EtExist

open EtExist in
theorem solution
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (G : Type)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType fN]
    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fN).obj B)
    (hnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fN).map φ (Θ B hB x))

    (het : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
      Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
      ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fN).obj B), (Scheme.nilpPoints fN).map p y = Θ B₀ hB₀ x₀ →
        ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θ B hB x = y)

    (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π))
    (hp : Function.Surjective p) (hsq : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fN).obj B)
    (hy : (Scheme.nilpPoints fN).map p y = Θ B₀ hB₀ x₀) :
    ∃ x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θ B hB x = y := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsNoetherianRing 𝒪 := inferInstance

  obtain ⟨ψ, hψ, -⟩ :=
    CerednikDrinfeld.FormalOmega.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
      𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B B₀ p hB hB₀ hp hsq x₀.1.1

  have NP := AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType (↥ψ.range) fN
  obtain ⟨Ty, fgTy, y₀, hy₀⟩ := NP.1 B y
  obtain ⟨ty, hty⟩ := fgTy
  have hTy : Ty.restrictScalars 𝒪 = Src ψ ty := by rw [← hty]; exact restrictScalars_adjoin_range _ _

  have SRC := CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB
  have SRC₀ := CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B₀ hB₀
  obtain ⟨s₀, S₀, hS₀, a₀, ha₀⟩ := SRC₀.1 x₀.1

  let σ : B₀ → B := Function.surjInv hp
  have hσ : ∀ b, p (σ b) = b := Function.surjInv_eq hp
  let s : Finset B := ty ∪ s₀.image σ
  set S : Subalgebra 𝒪 B := Src ψ s with hSdef
  have hTyS : Ty.restrictScalars 𝒪 ≤ S := by rw [hTy, hSdef]; exact Src_mono _ Finset.subset_union_left
  have hSp : S.map p = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B₀ from x₀.1.1) ∪ (↑(s.image p) : Set B₀)) := by
    rw [hSdef, Src, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image, ← hψ]
    rfl
  have hS₀Sp : S₀ ≤ S.map p := by
    rw [hS₀, hSp]
    refine Algebra.adjoin_mono (Set.union_subset_union_right _ ?_)
    intro b hb
    rw [Finset.coe_image]
    exact ⟨σ b, Finset.mem_union_right _ (Finset.mem_image_of_mem σ hb), hσ b⟩
  have hSn : IsNilpotent (algebraMap 𝒪 ↥S π) := isNilpotent_subalgebra π hB S
  have hSpn : IsNilpotent (algebraMap 𝒪 ↥(S.map p) π) := isNilpotent_subalgebra π hB₀ (S.map p)

  let X₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥(S.map p) :=
    ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hS₀Sp) a₀, x₀.2)
  let Y : (Scheme.nilpPoints fN).obj ↥S := (Scheme.nilpPoints fN).map (Subalgebra.inclusion hTyS) y₀
  have hX₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (S.map p).val X₀ = x₀ := by
    have h1 : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (S.map p).val
        ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hS₀Sp) a₀) = x₀.1 := by
      rw [← AlgFunctor.map_comp]; exact ha₀
    exact Prod.ext h1 rfl
  have hY : (Scheme.nilpPoints fN).map S.val Y = y := by
    have hval : S.val.comp (Subalgebra.inclusion hTyS) = Ty.val.restrictScalars 𝒪 := AlgHom.ext fun _ => rfl
    have c := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hTyS) S.val y₀
    show (Scheme.nilpPoints fN).map S.val ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hTyS) y₀) = y
    rw [← c, hval]
    exact hy₀

  let w₁ : (Scheme.nilpPoints fN).obj ↥(S.map p) := (Scheme.nilpPoints fN).map (restr p S) Y
  let w₂ : (Scheme.nilpPoints fN).obj ↥(S.map p) := Θ ↥(S.map p) hSpn X₀
  have hw₁ : (Scheme.nilpPoints fN).map (S.map p).val w₁ = Θ B₀ hB₀ x₀ := by
    have c := (Scheme.nilpPoints fN).map_comp (restr p S) (S.map p).val Y
    show (Scheme.nilpPoints fN).map (S.map p).val ((Scheme.nilpPoints fN).map (restr p S) Y) = _
    rw [← c, val_comp_restr, (Scheme.nilpPoints fN).map_comp, hY, hy]
  have hw₂ : (Scheme.nilpPoints fN).map (S.map p).val w₂ = Θ B₀ hB₀ x₀ := by
    show (Scheme.nilpPoints fN).map (S.map p).val (Θ ↥(S.map p) hSpn X₀) = _
    rw [← hnat _ _ hSpn hB₀, hX₀]

  let T' : Subalgebra ↥(x₀.1.1).range B₀ := Algebra.adjoin (↥(x₀.1.1).range) (↑(s.image p) : Set B₀)
  have fgT' : T'.FG := ⟨s.image p, rfl⟩
  have hT' : T'.restrictScalars 𝒪 = S.map p := by
    rw [hSp]; exact restrictScalars_adjoin_range _ _
  have hSpT' : S.map p ≤ T'.restrictScalars 𝒪 := le_of_eq hT'.symm
  have hvalT' : (T'.val.restrictScalars 𝒪).comp (Subalgebra.inclusion hSpT') = (S.map p).val := AlgHom.ext fun _ => rfl
  have hw : ∀ w : (Scheme.nilpPoints fN).obj ↥(S.map p), (Scheme.nilpPoints fN).map (S.map p).val w = Θ B₀ hB₀ x₀ →
      (Scheme.nilpPoints fN).map (T'.val.restrictScalars 𝒪) ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpT') w) = Θ B₀ hB₀ x₀ := by
    intro w hw0
    have c := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hSpT') (T'.val.restrictScalars 𝒪) w
    exact c.symm.trans ((congrArg (fun φ => (Scheme.nilpPoints fN).map φ w) hvalT').trans hw0)
  have NP₀ := AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType (↥(x₀.1.1).range) fN
  obtain ⟨T₃, fg₃, h13, h23, heqT⟩ :=
    NP₀.2 B₀ T' T' fgT' fgT' ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpT') w₁)
      ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpT') w₂) ((hw w₁ hw₁).trans (hw w₂ hw₂).symm)
  obtain ⟨t₃, ht₃⟩ := fg₃
  have hT₃ : T₃.restrictScalars 𝒪 = Src x₀.1.1 t₃ := by rw [← ht₃]; exact restrictScalars_adjoin_range _ _

  let s' : Finset B := s ∪ t₃.image σ
  set S' : Subalgebra 𝒪 B := Src ψ s' with hS'def
  have hSS' : S ≤ S' := by rw [hSdef, hS'def]; exact Src_mono _ Finset.subset_union_left
  have hS'p : S'.map p = Src x₀.1.1 (s'.image p) := by
    rw [hS'def, Src, Src, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image, ← hψ]
    rfl
  have hT₃S'p : T₃.restrictScalars 𝒪 ≤ S'.map p := by
    rw [hT₃, hS'p]
    refine Src_mono _ ?_
    intro b hb
    exact Finset.mem_image.2 ⟨σ b, Finset.mem_union_right _ (Finset.mem_image_of_mem σ hb), hσ b⟩
  have hSpS'p : S.map p ≤ S'.map p := Subalgebra.map_mono hSS'
  haveI : IsNoetherianRing ↥S' := SRC.2.2 ψ s' S' hS'def
  have hS'n : IsNilpotent (algebraMap 𝒪 ↥S' π) := isNilpotent_subalgebra π hB S'
  have hS'pn : IsNilpotent (algebraMap 𝒪 ↥(S'.map p) π) := isNilpotent_subalgebra π hB₀ (S'.map p)

  let X₀' : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥(S'.map p) :=
    (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSpS'p) X₀
  let Y' : (Scheme.nilpPoints fN).obj ↥S' := (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSS') Y

  have hincl : (Subalgebra.inclusion hSpS'p : ↥(S.map p) →ₐ[𝒪] ↥(S'.map p)) =
      (Subalgebra.inclusion hT₃S'p).comp (((Subalgebra.inclusion h13).restrictScalars 𝒪).comp (Subalgebra.inclusion hSpT')) :=
    AlgHom.ext fun _ => rfl
  have hincl' : (Subalgebra.inclusion hSpS'p : ↥(S.map p) →ₐ[𝒪] ↥(S'.map p)) =
      (Subalgebra.inclusion hT₃S'p).comp (((Subalgebra.inclusion h23).restrictScalars 𝒪).comp (Subalgebra.inclusion hSpT')) :=
    AlgHom.ext fun _ => rfl
  have hagree : (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) w₁ = (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) w₂ := by
    have c₁ := (Scheme.nilpPoints fN).map_comp (((Subalgebra.inclusion h13).restrictScalars 𝒪).comp (Subalgebra.inclusion hSpT'))
      (Subalgebra.inclusion hT₃S'p) w₁
    have c₁' := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hSpT') ((Subalgebra.inclusion h13).restrictScalars 𝒪) w₁
    have c₂ := (Scheme.nilpPoints fN).map_comp (((Subalgebra.inclusion h23).restrictScalars 𝒪).comp (Subalgebra.inclusion hSpT'))
      (Subalgebra.inclusion hT₃S'p) w₂
    have c₂' := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hSpT') ((Subalgebra.inclusion h23).restrictScalars 𝒪) w₂
    have e₁ := (congrArg (fun φ => (Scheme.nilpPoints fN).map φ w₁) hincl).trans (c₁.trans (congrArg _ c₁'))
    have e₂ := (congrArg (fun φ => (Scheme.nilpPoints fN).map φ w₂) hincl').trans (c₂.trans (congrArg _ c₂'))
    exact e₁.trans ((congrArg _ heqT).trans e₂.symm)
  have hcompat : (Scheme.nilpPoints fN).map (restr p S') Y' = Θ ↥(S'.map p) hS'pn X₀' := by

    have cL := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hSS') (restr p S') Y
    have cL' := (Scheme.nilpPoints fN).map_comp (restr p S) (Subalgebra.inclusion (Subalgebra.map_mono (f := p) hSS')) Y
    have hL : (Scheme.nilpPoints fN).map (restr p S') Y' = (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) w₁ := by
      show (Scheme.nilpPoints fN).map (restr p S') ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hSS') Y) =
        (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) ((Scheme.nilpPoints fN).map (restr p S) Y)
      rw [← cL, restr_comp_inclusion, cL']

    have hR : Θ ↥(S'.map p) hS'pn X₀' = (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) w₂ := by
      show Θ ↥(S'.map p) hS'pn ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map
        (Subalgebra.inclusion hSpS'p) X₀) = (Scheme.nilpPoints fN).map (Subalgebra.inclusion hSpS'p) (Θ ↥(S.map p) hSpn X₀)
      exact hnat _ _ hSpn hS'pn _ X₀
    rw [hL, hR]
    exact hagree

  obtain ⟨x', ⟨hx'₁, hx'₂⟩, -⟩ := het ↥S' ↥(S'.map p) (restr p S') hS'n hS'pn (restr_surjective p S') (restr_sqzero p hsq S') X₀' Y' hcompat
  refine ⟨(AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map S'.val x', ?_, ?_⟩
  ·
    rw [← AlgFunctor.map_comp, ← val_comp_restr, AlgFunctor.map_comp, hx'₁]
    show (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (S'.map p).val
      ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSpS'p) X₀) = x₀
    rw [← AlgFunctor.map_comp]
    have hv : (S'.map p).val.comp (Subalgebra.inclusion hSpS'p) = (S.map p).val := AlgHom.ext fun _ => rfl
    rw [hv]
    exact hX₀
  ·
    rw [hnat _ _ hS'n hB, hx'₂]
    show (Scheme.nilpPoints fN).map S'.val ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hSS') Y) = y
    have c := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hSS') S'.val Y
    have hv : S'.val.comp (Subalgebra.inclusion hSS') = S.val := AlgHom.ext fun _ => rfl
    rw [← c, hv]
    exact hY

end S_CerednikDrinfeld_FormalOmega_exists_lift_of_forall_isNoetherianRing_existsUnique_lift
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_lift_of_forall_isNoetherianRing_existsUnique_lift (solution)
