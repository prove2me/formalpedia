-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/80124169-7034-50ee-9652-97a1a0de2a5c

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace F3dNTransversalExtraLevelSol

theorem mem_inv_smul_iff {c : ℂ} (hc : c ≠ 0) (S : Submodule ℤ (Fin 2 → ℂ)) (v : Fin 2 → ℂ) :
    v ∈ c⁻¹ • S ↔ c • v ∈ S := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · intro h
    exact ⟨c • v, h, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem relIndex_smul {c : ℂ} (hc : c ≠ 0) (H K : Submodule ℤ (Fin 2 → ℂ)) :
    (c • H).toAddSubgroup.relIndex (c • K).toAddSubgroup = H.toAddSubgroup.relIndex K.toAddSubgroup := by
  let f : (Fin 2 → ℂ) →+ (Fin 2 → ℂ) := DistribSMul.toAddMonoidHom (Fin 2 → ℂ) c
  have hmap : ∀ S : Submodule ℤ (Fin 2 → ℂ), (c • S).toAddSubgroup = S.toAddSubgroup.map f := by
    intro S
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists, AddSubgroup.mem_map,
      DistribSMul.toAddMonoidHom_apply, f]
  rw [hmap H, hmap K]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (smul_right_injective (Fin 2 → ℂ) hc)

theorem relIndex_natCast_smul_span (b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ)) (n : ℕ) [NeZero n] :
    (((n : ℂ)) • Submodule.span ℤ (Set.range b₀)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range b₀)).toAddSubgroup = n ^ 4 := by
  set L : Submodule ℤ (Fin 2 → ℂ) := Submodule.span ℤ (Set.range b₀) with hL
  let bZ : Module.Basis (Fin 4) ℤ ↥L := Module.Basis.restrictScalars ℤ b₀
  let crd : ↥L ≃ₗ[ℤ] (Fin 4 → ℤ) := bZ.equivFun

  let g : ↥L.toAddSubgroup →+ (Fin 4 → ZMod n) :=
    { toFun := fun x i => ((crd x i : ℤ) : ZMod n)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  have hsurj : Function.Surjective g := by
    intro y
    refine ⟨crd.symm (fun i => (y i).cast), ?_⟩
    ext i
    simp [g]
  have hker : g.ker = ((n : ℂ) • L).toAddSubgroup.addSubgroupOf L.toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    constructor
    · intro hx
      have hdvd : ∀ i, (n : ℤ) ∣ crd x i := fun i => by
        have := congrFun hx i
        simpa [g, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      choose k hk using hdvd
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(crd.symm k : ↥L), (crd.symm k).2, ?_⟩
      have hx' : x = (n : ℤ) • crd.symm k := by
        apply crd.injective
        rw [map_zsmul, LinearEquiv.apply_symm_apply]
        ext i; simp [hk i]
      have := congrArg (fun z : ↥L => (z : Fin 2 → ℂ)) hx'
      simp only [Submodule.coe_smul_of_tower] at this
      rw [this, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast]
    · intro hx
      obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      have hx' : x = (n : ℤ) • (⟨y, hy⟩ : ↥L) := by
        apply Subtype.ext
        simp only [Submodule.coe_smul_of_tower]
        rw [← hyx, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast]
      rw [hx', map_zsmul]
      ext i
      simp [g]
  change (((n : ℂ) • L).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index = n ^ 4
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem nonempty_addEquiv_of_natCard_eq_sq {ℓ : ℕ} [Fact ℓ.Prime] (G : Type) [AddCommGroup G]
    [Module (ZMod ℓ) G] [Finite G] (hcard : Nat.card G = ℓ ^ 2) : Nonempty (ZMod ℓ × ZMod ℓ ≃+ G) := by
  have hℓ : ℓ.Prime := Fact.out
  have h : Nat.card G = Nat.card (ZMod ℓ) ^ Module.finrank (ZMod ℓ) G := Module.natCard_eq_pow_finrank
  rw [hcard, Nat.card_zmod] at h
  have hrk : Module.finrank (ZMod ℓ) G = Module.finrank (ZMod ℓ) (ZMod ℓ × ZMod ℓ) := by
    rw [Module.finrank_prod, Module.finrank_self]
    exact (Nat.pow_right_injective hℓ.two_le h).symm
  exact ⟨(LinearEquiv.ofFinrankEq G (ZMod ℓ × ZMod ℓ) hrk).symm.toAddEquiv⟩

section NoLevelZero

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem level_ne_zero (E : FakeEllipticCurve Λ N ℂ) : N ≠ 0 := by
  intro hN
  obtain ⟨P₀, -⟩ := E.lev_one (𝟙 (Spec (CommRingCat.of ℂ)))
  haveI : Flat (E.lev ≫ E.f) := E.lev_flat
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  have hpt : Nonempty ↥(Spec (CommRingCat.of ℂ)) := ⟨(⊥ : PrimeSpectrum ℂ)⟩
  obtain ⟨s⟩ := hpt
  let x : ↥E.C := P₀.base s
  have h1 := Scheme.Hom.one_le_finrank_map (E.lev ≫ E.f) x
  rw [E.lev_rank, hN] at h1
  simp at h1

end NoLevelZero

section Points

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

local notation "specOne" => (𝟙 (Spec (CommRingCat.of ℂ)) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))

variable (E : FakeEllipticCurve Λ N ℂ) (L : Submodule ℤ (Fin 2 → ℂ))
  (eE : SchemeHomOver specOne E.f ≃ ((Fin 2 → ℂ) ⧸ L.toAddSubgroup))
  (heE : ∀ P Q : SchemeHomOver specOne E.f, eE (E.L.mul specOne P Q) = eE P + eE Q)

include heE in

theorem equiv_one : eE (E.L.one specOne) = 0 := by
  have h := heE (E.L.one specOne) (E.L.one specOne)
  rw [E.L.one_mul] at h
  have := congrArg (fun z => z - eE (E.L.one specOne)) h
  simpa using this.symm

include heE in

theorem equiv_symm_zero : eE.symm 0 = E.L.one specOne := by
  rw [Equiv.symm_apply_eq]; exact (equiv_one E L eE heE).symm

include heE in

theorem equiv_symm_add (x y : (Fin 2 → ℂ) ⧸ L.toAddSubgroup) :
    eE.symm (x + y) = E.L.mul specOne (eE.symm x) (eE.symm y) := by
  apply eE.injective
  rw [heE, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem geomPoint_id : geomPoint (S := ℂ) ℂ (RingHom.id ℂ) = specOne := by
  unfold geomPoint
  have : CommRingCat.ofHom (RingHom.id ℂ) = 𝟙 (CommRingCat.of ℂ) := rfl
  rw [this, Spec.map_id]

def ptCast {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℂ))
    {t t' : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ)} (h : t = t') :
    SchemeHomOver t f ≃ SchemeHomOver t' f :=
  Equiv.subtypeEquivRight (fun φ => by rw [h])

@[scoped simp] theorem ptCast_coe {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℂ))
    {t t' : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ)} (h : t = t') (P : SchemeHomOver t f) :
    (ptCast f h P).1 = P.1 := rfl

set_option maxHeartbeats 6400000 in

def ptsGeomIdEquiv {C : Scheme.{0}} (lev' : C ⟶ E.A) :
    {P : SchemeHomOver (geomPoint (S := ℂ) ℂ (RingHom.id ℂ)) E.f // FactorsThrough lev' P} ≃
      {x : SchemeHomOver specOne E.f // FactorsThrough lev' x} where
  toFun P := ⟨ptCast E.f geomPoint_id P.1, by
    obtain ⟨P₀, hP₀⟩ := P.2
    exact ⟨P₀, by rw [hP₀]; rfl⟩⟩
  invFun Q := ⟨(ptCast E.f geomPoint_id).symm Q.1, by
    obtain ⟨Q₀, hQ₀⟩ := Q.2
    exact ⟨Q₀, by rw [hQ₀]; rfl⟩⟩
  left_inv P := by ext1; simp
  right_inv Q := by ext1; simp

theorem natCard_pts_lev :
    Nat.card {x : SchemeHomOver specOne E.f // FactorsThrough E.lev x} = N ^ 2 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast level_ne_zero E
  obtain ⟨eC, -⟩ := E.lev_fibre ℂ (RingHom.id ℂ) hN
  rw [← Nat.card_congr (eC.trans (ptsGeomIdEquiv E E.lev)), Nat.card_prod, Nat.card_zmod, pow_two]

section Geom

variable {k : Type} [Field k] (sk : ℂ →+* k)

theorem flat_geomPoint : Flat (geomPoint (S := ℂ) k sk) := by
  unfold geomPoint
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  unfold RingHom.Flat
  infer_instance

theorem surjective_geomPoint : Surjective (geomPoint (S := ℂ) k sk) :=
  ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩

theorem epi_geomPoint : Epi (geomPoint (S := ℂ) k sk) := by
  haveI := flat_geomPoint sk
  haveI := surjective_geomPoint sk
  exact Flat.epi_of_flat_of_surjective _

theorem sectionAt_injective (P Q : SchemeHomOver specOne E.f)
    (h : FakeEllipticCurve.sectionAt P k sk = FakeEllipticCurve.sectionAt Q k sk) : P = Q := by
  haveI := epi_geomPoint sk
  have h1 : geomPoint k sk ≫ P.1 = geomPoint k sk ≫ Q.1 := congrArg Subtype.val h
  exact Subtype.ext ((cancel_epi (geomPoint (S := ℂ) k sk)).1 h1)

theorem factorsThrough_sectionAt {C : Scheme.{0}} (lev' : C ⟶ E.A) (P : SchemeHomOver specOne E.f)
    (h : FactorsThrough lev' P) : FactorsThrough lev' (FakeEllipticCurve.sectionAt P k sk) := by
  obtain ⟨P₀, hP₀⟩ := h
  exact ⟨geomPoint k sk ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩

theorem exists_factorsThrough_lev_sectionAt_eq [IsAlgClosed k]
    (Q : SchemeHomOver (geomPoint k sk) E.f) (hQ : FactorsThrough E.lev Q) :
    ∃ P : SchemeHomOver specOne E.f, FactorsThrough E.lev P ∧ FakeEllipticCurve.sectionAt P k sk = Q := by
  have hN : N ≠ 0 := level_ne_zero E
  haveI : NeZero N := ⟨hN⟩
  have hNk : (N : k) ≠ 0 := by
    rw [← map_natCast sk]
    exact (map_ne_zero sk).2 (Nat.cast_ne_zero.2 hN)
  obtain ⟨ek, -⟩ := E.lev_fibre k sk hNk
  let F : {P : SchemeHomOver specOne E.f // FactorsThrough E.lev P} →
      {Q : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev Q} :=
    fun P => ⟨FakeEllipticCurve.sectionAt P.1 k sk, factorsThrough_sectionAt E sk E.lev P.1 P.2⟩
  have hFinj : Function.Injective F := fun P P' h =>
    Subtype.ext (sectionAt_injective E sk _ _ (congrArg Subtype.val h))
  haveI : Finite {Q : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev Q} := Finite.of_equiv _ ek
  have hcard : Nat.card {Q : SchemeHomOver (geomPoint k sk) E.f // FactorsThrough E.lev Q} ≤
      Nat.card {P : SchemeHomOver specOne E.f // FactorsThrough E.lev P} := by
    rw [← Nat.card_congr ek, natCard_pts_lev E, Nat.card_prod, Nat.card_zmod, pow_two]
  obtain ⟨P, hP⟩ := (hFinj.bijective_of_nat_card_le hcard).2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

end Geom

end Points

end F3dNTransversalExtraLevelSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv.F3dNTransversalExtraLevelSol"

local notation "specOne" => (𝟙 (Spec (CommRingCat.of ℂ)) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))

open F3dNTransversalExtraLevelSol in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) {N : ℕ}

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
      (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))
    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)
    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
      e E (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ N ℂ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ)

    (M' : Submodule ℤ (Fin 2 → ℂ))
    (hM' : M' ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M') ∧
      (∀ y ∈ Λ, ∀ v ∈ M', ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M') ∧
      M'.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
      (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ M' → v ∈ latt E)) :
    ∃ K : E.ExtraLevel ℓ, ∀ v : Fin 2 → ℂ,
      FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ↔ (c * ℓ) • v ∈ M' := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hcℓ : c * (ℓ : ℂ) ≠ 0 := mul_ne_zero hc hℓ0
  obtain ⟨hM'le, hM'ℓ, hM'stab, hM'idx, hM'trans⟩ := hM'
  obtain ⟨hLevE, hLE', -, -, -⟩ := hLev E

  have he0 : e E (E.L.one specOne) = 0 := equiv_one E (latt E) (e E) (hE1 E)
  have hsymm : ∀ x : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup, e E ((e E).symm x) = x :=
    fun x => Equiv.apply_symm_apply _ _

  let M'' : Submodule ℤ (Fin 2 → ℂ) := (c * (ℓ : ℂ))⁻¹ • M'
  have hM'' : ∀ v : Fin 2 → ℂ, v ∈ M'' ↔ (c * (ℓ : ℂ)) • v ∈ M' := fun v => mem_inv_smul_iff hcℓ M' v

  have hLM : latt E ≤ M'' := by
    intro v hv
    rw [hM'']
    have hcv : c • v ∈ qmPeriodLattice ι Λ τ := by
      rw [← hcL]; exact Submodule.smul_mem_pointwise_smul v c _ hv
    have h := hM'ℓ _ hcv
    rwa [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul, mul_comm] at h

  have hℓM : ∀ v ∈ M'', ((ℓ : ℂ)) • v ∈ latt E := by
    intro v hv
    rw [hM''] at hv
    have h := hM'le hv
    rw [← hcL] at h
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c (latt E)).1 h
    have : u = (ℓ : ℂ) • v := by
      apply smul_right_injective (Fin 2 → ℂ) hc
      change c • u = c • ((ℓ : ℂ) • v)
      rw [hu', smul_smul]
    rw [← this]; exact hu

  have hstabM : ∀ y ∈ Λ, ∀ v ∈ M'', ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M'' := by
    intro y hy v hv
    rw [hM''] at hv ⊢
    rw [← Matrix.mulVec_smul]
    exact hM'stab y hy _ hv

  have hidx : (latt E).toAddSubgroup.relIndex M''.toAddSubgroup = ℓ ^ 2 := by
    obtain ⟨b₀, hb₀⟩ := (hL1 E).1

    have h4 : (((ℓ : ℂ)) • qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 4 := by
      rw [← hcL, smul_smul, mul_comm, ← smul_smul, relIndex_smul hc, hb₀]
      exact relIndex_natCast_smul_span b₀ ℓ
    have hle1 : ((ℓ : ℂ)) • qmPeriodLattice ι Λ τ ≤ M' := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v _ _).1 hv
      have h := hM'ℓ u hu
      rwa [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast] at h
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle1)
      ((Submodule.toAddSubgroup_le _ _).2 hM'le)
    rw [hM'idx, h4, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at hmul
    have h2 : (((ℓ : ℂ)) • qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex M'.toAddSubgroup = ℓ ^ 2 :=
      mul_right_cancel₀ (pow_ne_zero 2 hℓ.ne_zero) hmul

    have hcM : (c * (ℓ : ℂ)) • M'' = M' := smul_inv_smul₀ hcℓ M'
    have hcLℓ : (c * (ℓ : ℂ)) • latt E = ((ℓ : ℂ)) • qmPeriodLattice ι Λ τ := by
      rw [← hcL, smul_smul, mul_comm]
    rw [← relIndex_smul hcℓ, hcM, hcLℓ, h2]

  let Q : AddSubgroup ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) :=
    M''.toAddSubgroup.map (QuotientAddGroup.mk' (latt E).toAddSubgroup)
  have hQmem : ∀ v : Fin 2 → ℂ, (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) ∈ Q ↔ v ∈ M'' := by
    intro v
    constructor
    · intro h
      obtain ⟨u, hu, hu'⟩ := AddSubgroup.mem_map.1 h
      have huv : -u + v ∈ latt E := by
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq] at hu'
        exact hu'
      have := M''.add_mem hu (hLM huv)
      rwa [add_neg_cancel_left] at this
    · intro h
      exact AddSubgroup.mem_map.2 ⟨v, h, rfl⟩
  have hcardQ : Nat.card ↥Q = ℓ ^ 2 := by
    have h1 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
      (QuotientAddGroup.mk' (latt E).toAddSubgroup) M''.toAddSubgroup
    rw [AddMonoidHom.comap_bot, QuotientAddGroup.ker_mk', AddSubgroup.relIndex_bot_left] at h1
    rw [← h1, hidx]

  have hrep : ∀ x : ↥Q, ∃ v : Fin 2 → ℂ, v ∈ M'' ∧
      ((v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) = (x : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
    intro x
    obtain ⟨v, hv, h⟩ := AddSubgroup.mem_map.1 x.2
    exact ⟨v, hv, h⟩
  choose rep hrepM hrepQ using hrep

  have htorsQ : ∀ x : ↥Q, ℓ • x = 0 := by
    intro x
    apply Subtype.ext
    change ℓ • (x : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) = 0
    rw [← hrepQ x, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, ← Nat.cast_smul_eq_nsmul ℂ]
    exact hℓM _ (hrepM x)

  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero 2 hℓ.ne_zero)
  letI instQ : Module (ZMod ℓ) ↥Q := AddCommGroup.zmodModule htorsQ
  obtain ⟨θ⟩ := @nonempty_addEquiv_of_natCard_eq_sq ℓ _ ↥Q _ instQ _ hcardQ

  let W : ZMod ℓ × ZMod ℓ → SchemeHomOver specOne E.f :=
    fun i => (e E).symm ((θ i : ↥Q) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)
  have hWe : ∀ i, e E (W i) = ((rep (θ i) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
    intro i
    change e E ((e E).symm _) = _
    rw [hsymm, hrepQ]
  have hW_add : ∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = E.L.mul specOne (W i) (W j) := by
    intro i j
    change (e E).symm ((θ (i + j) : ↥Q) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) = _
    rw [map_add, AddSubgroup.coe_add, equiv_symm_add E (latt E) (e E) (hE1 E)]
  have hW_stable : ∀ (x : ↥Λ) (i : ZMod ℓ × ZMod ℓ),
      ∃ j : ZMod ℓ × ZMod ℓ, pushPt (E.act x) (E.act_over x) (W i) = W j := by
    intro x i
    have hmem : ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (rep (θ i)) : Fin 2 → ℂ) :
        (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) ∈ Q :=
      (hQmem _).2 (hstabM x x.2 _ (hrepM (θ i)))
    refine ⟨θ.symm ⟨_, hmem⟩, ?_⟩
    apply (e E).injective
    rw [hE2 E x (W i) (rep (θ i)) (hWe i)]
    change _ = e E ((e E).symm _)
    rw [hsymm, AddEquiv.apply_symm_apply]
  have hW_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (i j : ZMod ℓ × ZMod ℓ),
      FakeEllipticCurve.sectionAt (W i) k sk = FakeEllipticCurve.sectionAt (W j) k sk → i = j := by
    intro k _ _ sk i j h
    have h1 : W i = W j := sectionAt_injective E sk _ _ h
    have h2 : (θ i : ↥Q) = θ j := by
      apply Subtype.ext
      exact (e E).symm.injective h1
    exact θ.injective h2
  have hW_lev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (i : ZMod ℓ × ZMod ℓ),
      FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → i = 0 := by
    intro k _ _ sk i h
    obtain ⟨P, hPlev, hPeq⟩ := exists_factorsThrough_lev_sectionAt_eq E sk _ h
    have hPW : P = W i := sectionAt_injective E sk _ _ hPeq

    have hv : rep (θ i) ∈ lattLev E := (hLevE _).2 ⟨P, hPlev, by rw [hPW, hWe]⟩

    have hvM : ((ℓ : ℂ) * c) • rep (θ i) ∈ M' := by
      rw [mul_comm]; exact (hM'' _).1 (hrepM (θ i))
    have hvL : rep (θ i) ∈ latt E := hM'trans _ hv hvM
    have hθ : (θ i : ↥Q) = 0 := by
      apply Subtype.ext
      change ((θ i : ↥Q) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) = 0
      rw [← hrepQ, QuotientAddGroup.eq_zero_iff]
      exact hvL
    exact θ.injective (hθ.trans (map_zero θ).symm)

  obtain ⟨K, hKW, hKfib⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
      E ℓ W hW_add hW_stable hW_inj hW_lev
  refine ⟨K, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  ·
    set P : SchemeHomOver specOne E.f := (e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) with hP
    have hfac : FactorsThrough K.levK (FakeEllipticCurve.sectionAt P ℂ (RingHom.id ℂ)) :=
      factorsThrough_sectionAt E (RingHom.id ℂ) K.levK P hv
    obtain ⟨i, hi⟩ := (hKfib ℂ (RingHom.id ℂ) _).1 hfac
    have hWi : W i = P := sectionAt_injective E (RingHom.id ℂ) _ _ hi
    have h1 : ((rep (θ i) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) =
        (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
      rw [← hWe, hWi, hP, hsymm]
    have h2 : -rep (θ i) + v ∈ latt E := QuotientAddGroup.eq.1 h1
    have h3 : v ∈ M'' := by
      have := M''.add_mem (hrepM (θ i)) (hLM h2)
      rwa [add_neg_cancel_left] at this
    exact (hM'' v).1 h3
  ·
    have hvQ : (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) ∈ Q := (hQmem v).2 ((hM'' v).2 hv)
    have hW : W (θ.symm ⟨_, hvQ⟩) = (e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
      change (e E).symm _ = _
      rw [AddEquiv.apply_symm_apply]
    rw [← hW]
    exact hKW _

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv (solution)
