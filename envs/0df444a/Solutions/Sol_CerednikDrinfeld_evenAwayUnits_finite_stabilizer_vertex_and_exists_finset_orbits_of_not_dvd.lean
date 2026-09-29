-- Prove2me | solution 1 for CerednikDrinfeld.evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/02803ac1-ba58-562a-8688-f952f87af9d8

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq
import Theorems.Thm_CerednikDrinfeld_exists_forall_finiteAdeleEvalAt_eq_one_and_mem_primeHeckeSet_and_isEichlerOrder_meetOrder_of_not_dvd
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_iso_tree_mulEquiv_projGenLinGroup_baseChange
import Theorems.Thm_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder
import Theorems.Thm_CerednikDrinfeld_CosetGraph_finite_quotVert_projAwayUnits_of_isOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

namespace TreeFeedAbs

theorem set_finite_stabilizer_of_subset {P X : Type*} [Group P] [MulAction P X] {Δ Δ' : Set P} (hle : Δ' ⊆ Δ)
    (x : X) (hfin : Set.Finite {g : P | g ∈ Δ ∧ g • x = x}) :
    Set.Finite {g : P | g ∈ Δ' ∧ g • x = x} :=
  hfin.subset fun g hg => ⟨hle hg.1, hg.2⟩

theorem exists_finset_forall_exists_smul_mem_of_finiteIndex {G X : Type*} [Group G] [MulAction G X]
    (Γ Γ' : Subgroup G) (hfin : (Γ'.subgroupOf Γ).FiniteIndex)
    (hquot : Finite (MulAction.orbitRel.Quotient ↥Γ X)) :
    ∃ S : Finset X, ∀ x : X, ∃ h ∈ Γ', h • x ∈ S := by
  classical
  haveI := hquot
  haveI := hfin
  haveI : Fintype (MulAction.orbitRel.Quotient ↥Γ X) := Fintype.ofFinite _
  haveI : Fintype (↥Γ ⧸ Γ'.subgroupOf Γ) := Fintype.ofFinite _
  let S₀ : Finset X := Finset.univ.image (fun c : MulAction.orbitRel.Quotient ↥Γ X => c.out)
  have hS₀ : ∀ x : X, ∃ γ : ↥Γ, γ • x ∈ S₀ := by
    intro x
    have hx : (Quotient.mk (MulAction.orbitRel ↥Γ X) x).out ∈ MulAction.orbit ↥Γ x :=
      MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq _))
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨γ, hγ ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  refine ⟨Finset.univ.biUnion fun c : ↥Γ ⧸ Γ'.subgroupOf Γ => S₀.image fun y => ((c.out : ↥Γ) : G)⁻¹ • y, ?_⟩
  intro x
  obtain ⟨γ, hγ⟩ := hS₀ x
  set c : ↥Γ ⧸ Γ'.subgroupOf Γ := QuotientGroup.mk γ with hc
  have hmem : (c.out)⁻¹ * γ ∈ Γ'.subgroupOf Γ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨((c.out : ↥Γ) : G)⁻¹ * (γ : G), by simpa [Subgroup.mem_subgroupOf] using hmem, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨(γ : G) • x, ?_, ?_⟩⟩
  · simpa [Subgroup.smul_def] using hγ
  · rw [mul_smul]

end TreeFeedAbs

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {rbar N : ℕ} [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsEichlerOrder R₁ N)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (ρ₀ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, K₀))
    (hρ₀ : ∀ g : (ℍ[ℚ, a₁, b₁])ˣ, ρ₀ g = Matrix.ProjGenLinGroup.mk ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) g))
    (Γt' : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓt' : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt' ↔ x ∈ Γt ∧ Even (Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) x)))) :
    (∀ w : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γt'.map ρ₀ ∧ g • w = w}) ∧
    (∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ w : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γt'.map ρ₀, g • w ∈ S) := by
  classical
  haveI hdvrI : IsDiscreteValuationRing 𝒪 := hdvr
  letI instHV : MulAction (ℍ[ℚ, a₁, b₁])ˣ (CerednikDrinfeld.CosetGraph.Vert R₁ v) := CerednikDrinfeld.CosetGraph.vertMulAction R₁ v
  letI instPV : MulAction (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v) (CerednikDrinfeld.CosetGraph.Vert R₁ v) :=
    CerednikDrinfeld.CosetGraph.projVertMulAction R₁ v

  have hΓteq : Γt = CerednikDrinfeld.CosetGraph.awayUnits R₁ v := Subgroup.ext hΓt
  have hle' : Γt' ≤ Γt := fun x hx => ((hΓt' x).1 hx).1

  obtain ⟨A, hA, e, hrange⟩ :=
    CerednikDrinfeld.exists_liesOverPrime_ringEquiv_ratClosure_range_iff_of_isAdicComplete_of_natCard_quotient_eq r 𝒪 hdvr π hπ
      hcomplete hres hunr K₀
  letI algA : Algebra 𝒪 ↥(ValuationSubring.ratClosure A) := (e.toRingHom.comp (algebraMap 𝒪 K₀)).toAlgebra
  have halgA : ∀ x : 𝒪, algebraMap 𝒪 ↥(ValuationSubring.ratClosure A) x = e (algebraMap 𝒪 K₀ x) := fun _ => rfl
  let eA : K₀ ≃ₐ[𝒪] ↥(ValuationSubring.ratClosure A) := AlgEquiv.ofRingEquiv (f := e) (fun x => (halgA x).symm)
  haveI : IsFractionRing 𝒪 ↥(ValuationSubring.ratClosure A) := IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors 𝒪) eA
  have hR₀ : ∀ x : ↥(ValuationSubring.ratClosure A), x ∈ Set.range (algebraMap 𝒪 ↥(ValuationSubring.ratClosure A)) ↔
      Valued.v (algebraMap ↥(ValuationSubring.ratClosure A) A.valuation.Completion x) ≤ 1 := fun x => hrange x

  let ι : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A) := (e.toRingHom.toRatAlgHom.mapMatrix).comp ι₀
  have hιapp : ∀ x : ℍ[ℚ, a₁, b₁], ι x = (ι₀ x).map e := fun x => AlgHom.mapMatrix_apply _ _
  have hι : Function.Injective ι := by
    intro x y h
    apply hι₀
    rw [hιapp, hιapp] at h
    exact Matrix.map_injective e.injective h
  let ρ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A)) :=
    Matrix.ProjGenLinGroup.mk.comp (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A)))
  have hρ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ x = Matrix.ProjGenLinGroup.mk
      (Units.map (ι : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A)) x) := fun _ => rfl

  obtain ⟨n, -, hn, -⟩ :=
    CerednikDrinfeld.exists_forall_finiteAdeleEvalAt_eq_one_and_mem_primeHeckeSet_and_isEichlerOrder_meetOrder_of_not_dvd
      (Fact.out : rbar.Prime) hdef hR₁ r hrr.symm hrN
  obtain ⟨eT, ψ, hequivH, hψ, -, -⟩ :=
    CerednikDrinfeld.CosetGraph.exists_iso_tree_ratClosure_smul_eq_and_natCard_stabilizer_mapDart_eq hdef hR₁ hrr.symm hrN v hv hn A hA
      𝒪 hR₀ ι hι ρ hρ

  let IH : LT.LatticeTree.IntegralHom 𝒪 ↥(ValuationSubring.ratClosure A) 𝒪 K₀ :=
    { toField := e.symm.toRingHom, toBase := RingHom.id 𝒪, commutes := fun x => by
        show e.symm (algebraMap 𝒪 ↥(ValuationSubring.ratClosure A) x) = algebraMap 𝒪 K₀ x
        rw [halgA, RingEquiv.symm_apply_apply] }
  let IH' : LT.LatticeTree.IntegralHom 𝒪 K₀ 𝒪 ↥(ValuationSubring.ratClosure A) :=
    { toField := e.toRingHom, toBase := RingHom.id 𝒪, commutes := fun x => by
        show e (algebraMap 𝒪 K₀ x) = algebraMap 𝒪 ↥(ValuationSubring.ratClosure A) x
        rw [halgA] }
  obtain ⟨e₂, ψ₂, -, hψ₂, he₂smul, -, -⟩ :=
    CerednikDrinfeld.BruhatTits.exists_iso_tree_mulEquiv_projGenLinGroup_baseChange 𝒪 ↥(ValuationSubring.ratClosure A) 𝒪 K₀ IH IH'
      (fun x => e.symm_apply_apply x) (fun x => e.apply_symm_apply x)

  have hψρ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ψ₂ (ρ x) = ρ₀ x := by
    intro x
    rw [hρ, hψ₂, hρ₀]
    congr 1
    ext i j
    rw [LT.LatticeTree.IntegralHom.mapGL_coe]
    show e.symm ((ι (x : ℍ[ℚ, a₁, b₁])) i j) = (ι₀ (x : ℍ[ℚ, a₁, b₁])) i j
    rw [hιapp, Matrix.map_apply, RingEquiv.symm_apply_apply]

  let E : CerednikDrinfeld.CosetGraph.Vert R₁ v → LT.LatticeTree.Vertex 𝒪 K₀ := fun x => e₂ (eT x)
  have hEsurj : Function.Surjective E := e₂.surjective.comp eT.surjective
  have hEinj : Function.Injective E := e₂.injective.comp eT.injective
  have hEsmul : ∀ (g : (ℍ[ℚ, a₁, b₁])ˣ) (x : CerednikDrinfeld.CosetGraph.Vert R₁ v), E (g • x) = ρ₀ g • E x := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H y =>
      show e₂ (eT (g • ((y : (CerednikDrinfeld.CosetGraph.Loc a₁ b₁ v)ˣ) : CerednikDrinfeld.CosetGraph.Vert R₁ v))) = ρ₀ g • e₂ (eT _)
      rw [CerednikDrinfeld.CosetGraph.smul_vert_mk, hequivH g y, he₂smul, hψρ]

  have hstabΓ : ∀ w : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γt.map ρ₀ ∧ g • w = w} := by
    intro w
    obtain ⟨x, rfl⟩ := hEsurj w
    haveI := CerednikDrinfeld.CosetGraph.finite_stabilizer_projAwayUnits_vert_of_isOrder hdef.1 hdef.2.1 hR₁.isOrder v x
    have hfinx : Set.Finite ((MulAction.stabilizer (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v) x : Subgroup (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v)) : Set (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v)) := Set.toFinite _
    refine (hfinx.image (fun γ : CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v =>
      ψ₂ ((ψ γ : ↥((CerednikDrinfeld.CosetGraph.awayUnits R₁ v).map ρ)) : PGL(2, ↥(ValuationSubring.ratClosure A))))).subset ?_
    rintro g ⟨hg, hgx⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    have hγ' : γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v := hΓteq ▸ hγ
    refine ⟨QuotientGroup.mk (⟨γ, hγ'⟩ : ↥(CerednikDrinfeld.CosetGraph.awayUnits R₁ v)), ?_, ?_⟩
    · show QuotientGroup.mk (⟨γ, hγ'⟩ : ↥(CerednikDrinfeld.CosetGraph.awayUnits R₁ v)) • x = x
      rw [CerednikDrinfeld.CosetGraph.mk_smul_vert]
      apply hEinj
      exact (hEsmul γ x).trans hgx
    · show ψ₂ ((ψ (QuotientGroup.mk (⟨γ, hγ'⟩ : ↥(CerednikDrinfeld.CosetGraph.awayUnits R₁ v))) :
          ↥((CerednikDrinfeld.CosetGraph.awayUnits R₁ v).map ρ)) : PGL(2, ↥(ValuationSubring.ratClosure A))) = ρ₀ γ
      rw [hψ ⟨γ, hγ'⟩, hψρ]

  letI actH : MulAction (ℍ[ℚ, a₁, b₁])ˣ (LT.LatticeTree.Vertex 𝒪 K₀) := MulAction.compHom _ ρ₀
  have hact : ∀ (g : (ℍ[ℚ, a₁, b₁])ˣ) (w : LT.LatticeTree.Vertex 𝒪 K₀), g • w = ρ₀ g • w := fun _ _ => rfl
  have hquot : Finite (MulAction.orbitRel.Quotient ↥Γt (LT.LatticeTree.Vertex 𝒪 K₀)) := by
    haveI hQ := CerednikDrinfeld.CosetGraph.finite_quotVert_projAwayUnits_of_isOrder hdef.1 hdef.2.1 hR₁.isOrder v
    have hErel : ∀ x y : CerednikDrinfeld.CosetGraph.Vert R₁ v,
        (MulAction.orbitRel (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v) _) x y →
        (MulAction.orbitRel ↥Γt (LT.LatticeTree.Vertex 𝒪 K₀)) (E x) (E y) := by
      intro x y hxy
      obtain ⟨γbar, hγbar⟩ := MulAction.orbitRel_apply.mp hxy
      induction γbar using QuotientGroup.induction_on with
      | H γ =>
        refine MulAction.orbitRel_apply.mpr ⟨⟨(γ : (ℍ[ℚ, a₁, b₁])ˣ), hΓteq.symm ▸ γ.2⟩, ?_⟩
        show ρ₀ (γ : (ℍ[ℚ, a₁, b₁])ˣ) • E y = E x
        rw [← hEsmul, ← hγbar]
        rfl
    refine Finite.of_surjective
      (fun c : Mumford.QuotVert (CerednikDrinfeld.CosetGraph.ProjAwayUnits R₁ v) (CerednikDrinfeld.CosetGraph.Vert R₁ v) =>
        (Quotient.mk (MulAction.orbitRel ↥Γt (LT.LatticeTree.Vertex 𝒪 K₀)) (E c.out))) ?_
    intro d
    induction d using Quotient.inductionOn with
    | h w =>
      obtain ⟨x, rfl⟩ := hEsurj w
      refine ⟨Quotient.mk _ x, Quotient.sound (hErel _ _ (Quotient.mk_out x))⟩

  have hfinIdx : (Γt'.subgroupOf Γt).FiniteIndex := by
    let P : (ℍ[ℚ, a₁, b₁])ˣ →* Multiplicative (ZMod 2) :=
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp
        (vdet.comp (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)))
    have hP : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, P x = 1 ↔
        Even (Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) x))) := by
      intro x
      show Multiplicative.ofAdd (Int.castAddHom (ZMod 2)
        (Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) x)))) = 1 ↔ _
      rw [ofAdd_eq_one, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ZMod.intCast_zmod_eq_zero_iff_dvd,
        even_iff_two_dvd]
      norm_num
    have hker : Γt'.subgroupOf Γt = (P.comp Γt.subtype).ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hP, hΓt']
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [hker]
    infer_instance

  refine ⟨fun w => (hstabΓ w).subset fun g hg => ⟨Subgroup.map_mono hle' hg.1, hg.2⟩, ?_⟩
  obtain ⟨S, hS⟩ := TreeFeedAbs.exists_finset_forall_exists_smul_mem_of_finiteIndex Γt Γt' hfinIdx hquot
  refine ⟨S, fun w => ?_⟩
  obtain ⟨h, hh, hhS⟩ := hS w
  exact ⟨ρ₀ h, Subgroup.mem_map_of_mem ρ₀ hh, by rw [← hact]; exact hhS⟩

end S_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd (solution)
