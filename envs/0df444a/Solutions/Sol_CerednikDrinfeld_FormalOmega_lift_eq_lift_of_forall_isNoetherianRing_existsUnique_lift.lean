-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.lift_eq_lift_of_forall_isNoetherianRing_existsUnique_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/28a82dc5-d958-5f96-be84-66ef043f6bbf

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

namespace P2MW.S_CerednikDrinfeld_FormalOmega_lift_eq_lift_of_forall_isNoetherianRing_existsUnique_lift
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace EtUnique

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

end EtUnique

open EtUnique in
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
    ∀ (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x₁ = x₀ → Θ B hB x₁ = y → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x₂ = x₀ → Θ B hB x₂ = y → x₁ = x₂ := by
  classical
  intro x₁ x₂ h₁ e₁ h₂ e₂
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsNoetherianRing 𝒪 := inferInstance

  have hψ₁ : p.comp x₁.1.1 = x₀.1.1 := congrArg (fun z => z.1.1) h₁
  have hψ₂ : p.comp x₂.1.1 = x₀.1.1 := congrArg (fun z => z.1.1) h₂
  have hψ : x₁.1.1 = x₂.1.1 :=
    (CerednikDrinfeld.FormalOmega.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
      𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B B₀ p hB hB₀ hp hsq x₀.1.1).unique hψ₁ hψ₂
  have hg₁ : x₁.2 = x₀.2 := congrArg (fun z => z.2) h₁
  have hg₂ : x₂.2 = x₀.2 := congrArg (fun z => z.2) h₂

  have SRC := CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB
  have SRC₀ := CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B₀ hB₀
  obtain ⟨s₁, S₁, hS₁, a₁, ha₁⟩ := SRC.1 x₁.1
  obtain ⟨s₂, S₂, hS₂, a₂, ha₂⟩ := SRC.1 x₂.1
  rw [← hψ] at hS₂
  have h1S : S₁ ≤ Src x₁.1.1 (s₁ ∪ s₂) := le_Src_of_subset _ hS₁ Finset.subset_union_left
  have h2S : S₂ ≤ Src x₁.1.1 (s₁ ∪ s₂) := le_Src_of_subset _ hS₂ Finset.subset_union_right
  set S : Subalgebra 𝒪 B := Src x₁.1.1 (s₁ ∪ s₂) with hSdef

  let xh₁ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S :=
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h1S) a₁
  let xh₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S :=
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h2S) a₂
  have hxh₁ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val xh₁ = x₁.1 := by
    show (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val
      ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h1S) a₁) = x₁.1
    rw [← AlgFunctor.map_comp]; exact ha₁
  have hxh₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val xh₂ = x₂.1 := by
    show (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val
      ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h2S) a₂) = x₂.1
    rw [← AlgFunctor.map_comp]; exact ha₂

  let z₁ := (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S) xh₁
  let z₂ := (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S) xh₂
  have hz : ∀ (xh : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val xh = x.1 →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (S.map p).val
        ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S) xh) = x₀.1 := by
    intro xh x hxh hx
    rw [← AlgFunctor.map_comp, val_comp_restr, AlgFunctor.map_comp, hxh]
    exact congrArg (fun z => z.1) hx
  have hSp : S.map p = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B₀ from x₀.1.1) ∪ (↑((s₁ ∪ s₂).image p) : Set B₀)) := by
    rw [hSdef, Src, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image, ← hψ₁]
    rfl
  obtain ⟨s₃, S₃, hS₃, h13, h23, heq3⟩ :=
    SRC₀.2.1 x₀.1 _ _ (S.map p) (S.map p) hSp hSp z₁ z₂ (hz xh₁ x₁ hxh₁ h₁) (hz xh₂ x₂ hxh₂ h₂)

  let T : Subalgebra ↥(x₁.1.1).range B := Algebra.adjoin ↥(x₁.1.1).range (↑(s₁ ∪ s₂) : Set B)
  have hT : T.restrictScalars 𝒪 = S := by rw [hSdef]; exact restrictScalars_adjoin_range _ _
  have fgT : T.FG := ⟨s₁ ∪ s₂, rfl⟩
  have hST : S ≤ T.restrictScalars 𝒪 := le_of_eq hT.symm
  let X₁ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S := (xh₁, x₀.2)
  let X₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S := (xh₂, x₀.2)
  have hSn : IsNilpotent (algebraMap 𝒪 ↥S π) := isNilpotent_subalgebra π hB S
  have hX : ∀ (xh : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S)
      (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val xh = x.1 → x.2 = x₀.2 →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map S.val ((xh, x₀.2) :
        (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S) = x := by
    intro xh x hxh hx2
    exact Prod.ext hxh hx2.symm
  let w₁ : (Scheme.nilpPoints fN).obj ↥T := (Scheme.nilpPoints fN).map (Subalgebra.inclusion hST) (Θ ↥S hSn X₁)
  let w₂ : (Scheme.nilpPoints fN).obj ↥T := (Scheme.nilpPoints fN).map (Subalgebra.inclusion hST) (Θ ↥S hSn X₂)
  have hval : (T.val.restrictScalars 𝒪).comp (Subalgebra.inclusion hST) = S.val := AlgHom.ext fun _ => rfl
  have hw : ∀ (X : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S)
      (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map S.val X = x → Θ B hB x = y →
      (Scheme.nilpPoints fN).map (T.val.restrictScalars 𝒪) ((Scheme.nilpPoints fN).map (Subalgebra.inclusion hST) (Θ ↥S hSn X)) = y := by
    intro X x hX hy'
    rw [← AlgFunctor.map_comp, hval, ← hnat _ _ hSn hB S.val X, hX, hy']
  obtain ⟨T₃, fg₃, hT13, hT23, heqT⟩ :=
    (AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType (↥(x₁.1.1).range) fN).2 B T T fgT fgT
      w₁ w₂ ((hw X₁ x₁ (hX xh₁ x₁ hxh₁ hg₁) e₁).trans (hw X₂ x₂ (hX xh₂ x₂ hxh₂ hg₂) e₂).symm)
  obtain ⟨t₃, ht₃⟩ := fg₃
  have hT₃ : T₃.restrictScalars 𝒪 = Src x₁.1.1 t₃ := by rw [← ht₃]; exact restrictScalars_adjoin_range _ _

  let σ : B₀ → B := Function.surjInv hp
  have hσ : ∀ b, p (σ b) = b := Function.surjInv_eq hp
  let s' : Finset B := s₁ ∪ s₂ ∪ t₃ ∪ s₃.image σ
  set S' : Subalgebra 𝒪 B := Src x₁.1.1 s' with hS'def
  have hSS' : S ≤ S' := by
    rw [hSdef, hS'def]; exact Src_mono _ (Finset.union_subset_left (Finset.subset_union_left))
  have hT₃S' : T₃.restrictScalars 𝒪 ≤ S' := by
    rw [hT₃, hS'def]; exact Src_mono _ ((Finset.subset_union_right).trans Finset.subset_union_left)
  have hS'p : S'.map p = Algebra.adjoin 𝒪 (Set.range (show Onr →ₐ[𝒪] B₀ from x₀.1.1) ∪ (↑(s'.image p) : Set B₀)) := by
    rw [hS'def, Src, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image, ← hψ₁]
    rfl
  have hS₃S'p : S₃ ≤ S'.map p := by
    rw [hS₃, hS'p]
    refine Algebra.adjoin_mono (Set.union_subset_union_right _ ?_)
    intro b hb
    rw [Finset.coe_image]
    exact ⟨σ b, Finset.mem_union_right _ (Finset.mem_image_of_mem σ hb), hσ b⟩
  haveI : IsNoetherianRing ↥S' := SRC.2.2 x₁.1.1 s' S' hS'def
  have hS'n : IsNilpotent (algebraMap 𝒪 ↥S' π) := isNilpotent_subalgebra π hB S'
  have hS'pn : IsNilpotent (algebraMap 𝒪 ↥(S'.map p) π) := isNilpotent_subalgebra π hB₀ (S'.map p)

  let Y₁ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S' :=
    (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSS') X₁
  let Y₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S' :=
    (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSS') X₂

  have hinclp : (Subalgebra.inclusion (Subalgebra.map_mono (f := p) hSS')) =
      (Subalgebra.inclusion hS₃S'p).comp (Subalgebra.inclusion h13) := AlgHom.ext fun _ => rfl
  have hA : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (restr p S') Y₁ =
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (restr p S') Y₂ := by
    have hpush : ∀ xh : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S,
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S')
          ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hSS') xh) =
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hS₃S'p)
          ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion h13)
            ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S) xh)) := by
      intro xh
      rw [← AlgFunctor.map_comp, restr_comp_inclusion, hinclp, AlgFunctor.map_comp, AlgFunctor.map_comp]
    have hA1 : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S')
        ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hSS') xh₁) =
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (restr p S')
        ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (Subalgebra.inclusion hSS') xh₂) := by
      rw [hpush, hpush]
      exact congrArg _ heq3
    exact Prod.ext hA1 rfl

  have hincl : (Subalgebra.inclusion hSS' : ↥S →ₐ[𝒪] ↥S') =
      (Subalgebra.inclusion hT₃S').comp (((Subalgebra.inclusion hT13).restrictScalars 𝒪).comp (Subalgebra.inclusion hST)) :=
    AlgHom.ext fun _ => rfl
  have hB' : Θ ↥S' hS'n Y₁ = Θ ↥S' hS'n Y₂ := by
    show Θ ↥S' hS'n ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSS') X₁) =
      Θ ↥S' hS'n ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSS') X₂)
    rw [hnat _ _ hSn hS'n, hnat _ _ hSn hS'n, hincl]
    have c₁ := (Scheme.nilpPoints fN).map_comp (((Subalgebra.inclusion hT13).restrictScalars 𝒪).comp (Subalgebra.inclusion hST))
      (Subalgebra.inclusion hT₃S') (Θ ↥S hSn X₁)
    have c₁' := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hST) ((Subalgebra.inclusion hT13).restrictScalars 𝒪) (Θ ↥S hSn X₁)
    have c₂ := (Scheme.nilpPoints fN).map_comp (((Subalgebra.inclusion hT13).restrictScalars 𝒪).comp (Subalgebra.inclusion hST))
      (Subalgebra.inclusion hT₃S') (Θ ↥S hSn X₂)
    have c₂' := (Scheme.nilpPoints fN).map_comp (Subalgebra.inclusion hST) ((Subalgebra.inclusion hT13).restrictScalars 𝒪) (Θ ↥S hSn X₂)
    refine c₁.trans (Eq.trans ?_ c₂.symm)
    apply congrArg
    exact c₁'.trans (heqT.trans c₂'.symm)

  have key := het ↥S' ↥(S'.map p) (restr p S') hS'n hS'pn (restr_surjective p S') (restr_sqzero p hsq S')
    ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (restr p S') Y₁)
    (Θ ↥S' hS'n Y₁) (hnat _ _ hS'n hS'pn (restr p S') Y₁).symm
  have hY : Y₁ = Y₂ := key.unique ⟨rfl, rfl⟩ ⟨hA.symm, hB'.symm⟩

  have fin : ∀ (xh : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S)
      (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val xh = x.1 → x.2 = x₀.2 →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map S'.val
        ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (Subalgebra.inclusion hSS')
          ((xh, x₀.2) : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj ↥S)) = x := by
    intro xh x hxh hx2
    rw [← AlgFunctor.map_comp]
    exact Prod.ext hxh hx2.symm
  rw [← fin xh₁ x₁ hxh₁ hg₁, ← fin xh₂ x₂ hxh₂ hg₂]
  exact congrArg _ hY

end S_CerednikDrinfeld_FormalOmega_lift_eq_lift_of_forall_isNoetherianRing_existsUnique_lift
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_lift_eq_lift_of_forall_isNoetherianRing_existsUnique_lift (solution)
