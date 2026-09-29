-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e590daa2-0aa7-519b-9fef-4065dfbafcf4

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst

import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
import Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace ExtendDef

p2m_open "CerednikDrinfeld.FormalOmega.AlgFunctor"

section engine

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (G : AlgFunctor 𝒪)
  {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

abbrev FF : AlgFunctor 𝒪 := AlgFunctor.prod (AlgFunctor.corep Onr) G

def IsSrc {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (S : Subalgebra 𝒪 B) : Prop :=
  ∃ s : Finset B, S = Algebra.adjoin 𝒪 (Set.range ψ ∪ (↑s : Set B))

theorem isNilpotent_subalgebra {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
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

theorem val_comp_inclusion {B : Type} [CommRing B] [Algebra 𝒪 B] {S₁ S₃ : Subalgebra 𝒪 B} (h : S₁ ≤ S₃) :
    S₃.val.comp (Subalgebra.inclusion h) = S₁.val :=
  AlgHom.ext fun _ => rfl

theorem isSrc_map {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') {ψ : Onr →ₐ[𝒪] B} {S : Subalgebra 𝒪 B} (h : IsSrc Onr ψ S) : IsSrc Onr (φ.comp ψ) (S.map φ) := by
  classical
  obtain ⟨s, rfl⟩ := h
  refine ⟨s.image φ, ?_⟩
  rw [AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, Finset.coe_image]
  rfl

variable (UN : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B],
    IsNilpotent (algebraMap 𝒪 B π) → (FF Onr G).obj B → (Scheme.nilpPoints fN).obj B)
  (hUN : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (FF Onr G).obj B),
    UN B' hB' ((FF Onr G).map φ x) = (Scheme.nilpPoints fN).map φ (UN B hB x))
  (H1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ x : (FF Onr G).obj B,
    ∃ S : Subalgebra 𝒪 B, IsSrc Onr x.1 S ∧ ∃ x₀ : (FF Onr G).obj ↥S, (FF Onr G).map S.val x₀ = x)
  (H2 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ (x : (FF Onr G).obj B)
    (S₁ S₂ : Subalgebra 𝒪 B), IsSrc Onr x.1 S₁ → IsSrc Onr x.1 S₂ →
    ∀ (x₁ : (FF Onr G).obj ↥S₁) (x₂ : (FF Onr G).obj ↥S₂), (FF Onr G).map S₁.val x₁ = x → (FF Onr G).map S₂.val x₂ = x →
    ∃ S₃ : Subalgebra 𝒪 B, IsSrc Onr x.1 S₃ ∧ ∃ (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
      (FF Onr G).map (Subalgebra.inclusion h₁) x₁ = (FF Onr G).map (Subalgebra.inclusion h₂) x₂)
  (H3 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    ∀ (ψ : Onr →ₐ[𝒪] B) (S : Subalgebra 𝒪 B), IsSrc Onr ψ S → IsNoetherianRing ↥S)

structure Src {B : Type} [CommRing B] [Algebra 𝒪 B] (x : (FF Onr G).obj B) : Type where
  S : Subalgebra 𝒪 B
  hS : IsSrc Onr x.1 S
  x₀ : (FF Onr G).obj ↥S
  hx₀ : (FF Onr G).map S.val x₀ = x

include H1 in
theorem nonempty_src {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (FF Onr G).obj B) :
    Nonempty (Src Onr G x) := by
  obtain ⟨S, hS, x₀, hx₀⟩ := H1 B hB x
  exact ⟨⟨S, hS, x₀, hx₀⟩⟩

private noncomputable def _root_.ExtendDef.val {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) {x : (FF Onr G).obj B}
    (σ : Src Onr G x) : (Scheme.nilpPoints fN).obj B :=
  haveI : IsNoetherianRing ↥σ.S := H3 B hB x.1 σ.S σ.hS
  (Scheme.nilpPoints fN).map σ.S.val (UN ↥σ.S (isNilpotent_subalgebra π hB σ.S) σ.x₀)

p2m_export "ExtendDef" "val"
include hUN H2 in
theorem val_eq {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) {x : (FF Onr G).obj B}
    (σ₁ σ₂ : Src Onr G x) : val π Onr G fN UN H3 hB σ₁ = val π Onr G fN UN H3 hB σ₂ := by
  obtain ⟨S₃, hS₃, h₁, h₂, heq⟩ := H2 B hB x σ₁.S σ₂.S σ₁.hS σ₂.hS σ₁.x₀ σ₂.x₀ σ₁.hx₀ σ₂.hx₀
  haveI i₁ : IsNoetherianRing ↥σ₁.S := H3 B hB x.1 σ₁.S σ₁.hS
  haveI i₂ : IsNoetherianRing ↥σ₂.S := H3 B hB x.1 σ₂.S σ₂.hS
  haveI i₃ : IsNoetherianRing ↥S₃ := H3 B hB x.1 S₃ hS₃
  have e₁ : val π Onr G fN UN H3 hB σ₁ = (Scheme.nilpPoints fN).map S₃.val
      (UN ↥S₃ (isNilpotent_subalgebra π hB S₃) ((FF Onr G).map (Subalgebra.inclusion h₁) σ₁.x₀)) := by
    rw [hUN _ _ (isNilpotent_subalgebra π hB σ₁.S) (isNilpotent_subalgebra π hB S₃), ← (Scheme.nilpPoints fN).map_comp,
      val_comp_inclusion]
    rfl
  have e₂ : val π Onr G fN UN H3 hB σ₂ = (Scheme.nilpPoints fN).map S₃.val
      (UN ↥S₃ (isNilpotent_subalgebra π hB S₃) ((FF Onr G).map (Subalgebra.inclusion h₂) σ₂.x₀)) := by
    rw [hUN _ _ (isNilpotent_subalgebra π hB σ₂.S) (isNilpotent_subalgebra π hB S₃), ← (Scheme.nilpPoints fN).map_comp,
      val_comp_inclusion]
    rfl
  rw [e₁, e₂, heq]

noncomputable def Src.map {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') {x : (FF Onr G).obj B} (σ : Src Onr G x) : Src Onr G ((FF Onr G).map φ x) where
  S := σ.S.map φ
  hS := isSrc_map Onr φ σ.hS
  x₀ := (FF Onr G).map (restr φ σ.S) σ.x₀
  hx₀ := by rw [← (FF Onr G).map_comp, val_comp_restr, (FF Onr G).map_comp, σ.hx₀]

include hUN in
theorem val_map {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (φ : B →ₐ[𝒪] B') {x : (FF Onr G).obj B} (σ : Src Onr G x) :
    val π Onr G fN UN H3 hB' (σ.map Onr G φ) = (Scheme.nilpPoints fN).map φ (val π Onr G fN UN H3 hB σ) := by
  haveI i₁ : IsNoetherianRing ↥σ.S := H3 B hB x.1 σ.S σ.hS
  haveI i₂ : IsNoetherianRing ↥(σ.S.map φ) := H3 B' hB' (φ.comp x.1) (σ.S.map φ) (isSrc_map Onr φ σ.hS)
  show (Scheme.nilpPoints fN).map (σ.S.map φ).val
      (UN ↥(σ.S.map φ) (isNilpotent_subalgebra π hB' (σ.S.map φ)) ((FF Onr G).map (restr φ σ.S) σ.x₀)) = _
  rw [hUN _ _ (isNilpotent_subalgebra π hB σ.S) (isNilpotent_subalgebra π hB' (σ.S.map φ)),
    ← (Scheme.nilpPoints fN).map_comp, val_comp_restr, (Scheme.nilpPoints fN).map_comp]
  rfl

include hUN in
theorem val_eq_UN {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {x : (FF Onr G).obj B} (σ : Src Onr G x) : val π Onr G fN UN H3 hB σ = UN B hB x := by
  haveI i₁ : IsNoetherianRing ↥σ.S := H3 B hB x.1 σ.S σ.hS
  show (Scheme.nilpPoints fN).map σ.S.val (UN ↥σ.S (isNilpotent_subalgebra π hB σ.S) σ.x₀) = _
  rw [← hUN _ _ (isNilpotent_subalgebra π hB σ.S) hB, σ.hx₀]

noncomputable def U (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (FF Onr G).obj B) :
    (Scheme.nilpPoints fN).obj B :=
  val π Onr G fN UN H3 hB (Classical.choice (nonempty_src π Onr G H1 hB x))

include hUN H2 in
theorem U_nat {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (FF Onr G).obj B) :
    U π Onr G fN UN H1 H3 B' hB' ((FF Onr G).map φ x) = (Scheme.nilpPoints fN).map φ (U π Onr G fN UN H1 H3 B hB x) := by
  unfold U
  rw [val_eq π Onr G fN UN hUN H2 H3 hB' _ ((Classical.choice (nonempty_src π Onr G H1 hB x)).map Onr G φ),
    val_map π Onr G fN UN hUN H3 hB hB' φ]

include hUN in
theorem U_eq {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : (FF Onr G).obj B) : U π Onr G fN UN H1 H3 B hB x = UN B hB x :=
  val_eq_UN π Onr G fN UN hUN H3 hB _

end engine

end ExtendDef

open ExtendDef in
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
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u B' hB' hc' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x)) :
    ∃! U : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
          U B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), U B hB x = u B hB hc x) := by
  classical
  let F : AlgFunctor 𝒪 := AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)

  obtain ⟨UN, ⟨hUN, hUNu⟩, -⟩ :=
    AlgebraicGeometry.Scheme.nilpPoints.existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem π F fN u hu

  have SRC := fun (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) =>
    CerednikDrinfeld.FormalOmega.exists_finset_map_adjoin_eq_prod_corep_omega_of_irreducible
      𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed B hB
  have H1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ x : F.obj B,
      ∃ S : Subalgebra 𝒪 B, IsSrc Onr x.1 S ∧ ∃ x₀ : F.obj ↥S, F.map S.val x₀ = x := by
    intro B _ _ hB x
    obtain ⟨s, S, hS, x₀, hx₀⟩ := (SRC B hB).1 x
    exact ⟨S, ⟨s, hS⟩, x₀, hx₀⟩
  have H2 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → ∀ (x : F.obj B)
      (S₁ S₂ : Subalgebra 𝒪 B), IsSrc Onr x.1 S₁ → IsSrc Onr x.1 S₂ →
      ∀ (x₁ : F.obj ↥S₁) (x₂ : F.obj ↥S₂), F.map S₁.val x₁ = x → F.map S₂.val x₂ = x →
      ∃ S₃ : Subalgebra 𝒪 B, IsSrc Onr x.1 S₃ ∧ ∃ (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
        F.map (Subalgebra.inclusion h₁) x₁ = F.map (Subalgebra.inclusion h₂) x₂ := by
    intro B _ _ hB x S₁ S₂ hS₁ hS₂ x₁ x₂ hx₁ hx₂
    obtain ⟨s₁, hs₁⟩ := hS₁
    obtain ⟨s₂, hs₂⟩ := hS₂
    obtain ⟨s₃, S₃, hS₃, h₁, h₂, heq⟩ := (SRC B hB).2.1 x s₁ s₂ S₁ S₂ hs₁ hs₂ x₁ x₂ hx₁ hx₂
    exact ⟨S₃, ⟨s₃, hS₃⟩, h₁, h₂, heq⟩
  have H3 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      ∀ (ψ : Onr →ₐ[𝒪] B) (S : Subalgebra 𝒪 B), IsSrc Onr ψ S → IsNoetherianRing ↥S := by
    intro B _ _ hB ψ S hS
    obtain ⟨s, hs⟩ := hS
    exact (SRC B hB).2.2 ψ s S hs

  refine ⟨U π Onr (Omega K₀ π) fN UN H1 H3, ⟨?_, ?_⟩, ?_⟩
  · intro B _ _ B' _ _ hB hB' φ x
    exact U_nat π Onr (Omega K₀ π) fN UN hUN H1 H2 H3 hB hB' φ x
  · intro B _ _ _ hB hc x
    rw [U_eq π Onr (Omega K₀ π) fN UN hUN H1 H3 hB x, hUNu B hB hc x]
  ·
    rintro U' ⟨hU'nat, hU'u⟩
    funext B instB instA hB x
    refine AlgebraicGeometry.Scheme.nilpPoints.forall_eq_of_forall_eq_of_isNoetherianRing_of_forall_isIdempotentElem π F fN
      ?_ U' (U π Onr (Omega K₀ π) fN UN H1 H3) hU'nat
      (fun B _ _ B' _ _ hB hB' φ x => U_nat π Onr (Omega K₀ π) fN UN hUN H1 H2 H3 hB hB' φ x) ?_ B hB x
    · intro B _ _ hB x
      obtain ⟨S, hS, x₀, hx₀⟩ := H1 B hB x
      exact ⟨S, H3 B hB x.1 S hS, x₀, hx₀⟩
    · intro B _ _ _ hB hc x
      rw [hU'u B hB hc x, U_eq π Onr (Omega K₀ π) fN UN hUN H1 H3 hB x, hUNu B hB hc x]

end S_CerednikDrinfeld_FormalOmega_existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem (solution)
