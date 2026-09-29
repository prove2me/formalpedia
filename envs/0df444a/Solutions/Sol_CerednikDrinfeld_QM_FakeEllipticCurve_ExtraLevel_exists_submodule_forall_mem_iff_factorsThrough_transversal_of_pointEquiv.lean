-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4994bf89-8b0d-5d33-be62-4795bbf22e4b

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace ExtraLevelLatticeSol

theorem eq_zero_of_forall_smul_mem_span (b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ)) (μ : ℂ)
    (h : ∀ v : Fin 2 → ℂ, μ • v ∈ Submodule.span ℤ (Set.range b₀)) : μ = 0 := by
  by_contra hμ

  have hmem := h (μ⁻¹ • (((1 : ℝ) / 2) • b₀ 0))
  rw [smul_smul, mul_inv_cancel₀ hμ, one_smul] at hmem
  rw [Module.Basis.mem_span_iff_repr_mem ℤ b₀] at hmem
  obtain ⟨n, hn⟩ := hmem 0
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_same, eq_intCast] at hn

  have h2 : (2 : ℝ) * n = 1 := by rw [hn]; norm_num
  have h2' : (2 : ℤ) * n = 1 := by exact_mod_cast h2
  omega

theorem mem_inv_smul_iff {c : ℂ} (hc : c ≠ 0) (S : Submodule ℤ (Fin 2 → ℂ)) (v : Fin 2 → ℂ) :
    v ∈ c⁻¹ • S ↔ c • v ∈ S := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · intro h
    exact ⟨c • v, h, by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem mem_smul_iff {c : ℂ} (hc : c ≠ 0) (S : Submodule ℤ (Fin 2 → ℂ)) (v : Fin 2 → ℂ) :
    v ∈ c • S ↔ c⁻¹ • v ∈ S := by
  have := mem_inv_smul_iff (inv_ne_zero hc) S v
  rwa [inv_inv] at this

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

theorem inf_toAddSubgroup (p p' : Submodule ℤ (Fin 2 → ℂ)) :
    (p ⊓ p').toAddSubgroup = p.toAddSubgroup ⊓ p'.toAddSubgroup := by
  ext v; simp

theorem map_iota_ratCast_mulVec {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (r : ℚ)
    (v : Fin 2 → ℂ) : ((ι (r : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v = (r : ℂ) • v := by
  have h1 : (r : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] r := rfl
  have h2 : (ι (r : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ) = (r : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [h1, ι.commutes]
    ext i j
    rw [Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h2, Matrix.smul_mulVec, Matrix.one_mulVec]

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

theorem mapPt_mapPt {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℂ)} {f' : A' ⟶ Spec (CommRingCat.of ℂ)}
    {f'' : A'' ⟶ Spec (CommRingCat.of ℂ)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of ℂ)} (P : SchemeHomOver t f) :
    mapPt ψ hψ (mapPt φ hφ P) = mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P :=
  Subtype.ext (by simp [mapPt])

theorem mapPt_congr {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℂ)} {f' : A' ⟶ Spec (CommRingCat.of ℂ)}
    {φ φ' : A ⟶ A'} (h : φ = φ') (hφ : φ ≫ f' = f) (hφ' : φ' ≫ f' = f)
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of ℂ)} (P : SchemeHomOver t f) :
    mapPt φ hφ P = mapPt φ' hφ' P := by
  subst h; rfl

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

theorem equiv_inv (P : SchemeHomOver specOne E.f) : eE (E.L.inv specOne P) = - eE P := by
  have h := heE (E.L.inv specOne P) P
  rw [E.L.inv_mul_cancel, equiv_one E L eE heE] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

include heE in

theorem equiv_nsmulPt (n : ℕ) (P : SchemeHomOver specOne E.f) : eE (nsmulPt E.L specOne n P) = n • eE P := by
  induction n with
  | zero => simp [nsmulPt, equiv_one E L eE heE]
  | succ n ih => rw [nsmulPt, heE, ih, succ_nsmul]

include heE in

theorem equiv_symm_add (x y : (Fin 2 → ℂ) ⧸ L.toAddSubgroup) :
    eE.symm (x + y) = E.L.mul specOne (eE.symm x) (eE.symm y) := by
  apply eE.injective
  rw [heE, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

include heE in

theorem equiv_symm_neg (x : (Fin 2 → ℂ) ⧸ L.toAddSubgroup) : eE.symm (-x) = E.L.inv specOne (eE.symm x) := by
  apply eE.injective
  rw [equiv_inv E L eE heE, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def levelAddSubgroup {ℓ : ℕ} (K : E.ExtraLevel ℓ)
    (heE : ∀ P Q : SchemeHomOver specOne E.f, eE (E.L.mul specOne P Q) = eE P + eE Q) : AddSubgroup (Fin 2 → ℂ) where
  carrier := {v | FactorsThrough K.levK (eE.symm (v : (Fin 2 → ℂ) ⧸ L.toAddSubgroup))}
  add_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [QuotientAddGroup.mk_add, equiv_symm_add E L eE heE]
    exact (K.levK_sub specOne _ _ hv hw).1
  zero_mem' := by
    simp only [Set.mem_setOf_eq, QuotientAddGroup.mk_zero, equiv_symm_zero E L eE heE]
    exact K.levK_one specOne
  neg_mem' := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [QuotientAddGroup.mk_neg, equiv_symm_neg E L eE heE]
    exact (K.levK_sub specOne _ _ hv hv).2

theorem mem_levelAddSubgroup {ℓ : ℕ} (K : E.ExtraLevel ℓ)
    (heE : ∀ P Q : SchemeHomOver specOne E.f, eE (E.L.mul specOne P Q) = eE P + eE Q) (v : Fin 2 → ℂ) :
    v ∈ levelAddSubgroup E L eE K heE ↔ FactorsThrough K.levK (eE.symm (v : (Fin 2 → ℂ) ⧸ L.toAddSubgroup)) :=
  Iff.rfl

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

theorem natCard_pts_extraLevel {ℓ : ℕ} [NeZero ℓ] (K : E.ExtraLevel ℓ) :
    Nat.card {x : SchemeHomOver specOne E.f // FactorsThrough K.levK x} = ℓ ^ 2 := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  obtain ⟨eK, -⟩ := K.levK_fibre ℂ (RingHom.id ℂ) hℓ
  let cst := ptCast E.f geomPoint_id
  let e' : {P : SchemeHomOver (geomPoint (S := ℂ) ℂ (RingHom.id ℂ)) E.f // FactorsThrough K.levK P} ≃
      {x : SchemeHomOver specOne E.f // FactorsThrough K.levK x} :=
    { toFun := fun P => ⟨cst P.1, by
        obtain ⟨P₀, hP₀⟩ := P.2
        exact ⟨P₀, by rw [hP₀]; rfl⟩⟩
      invFun := fun Q => ⟨cst.symm Q.1, by
        obtain ⟨Q₀, hQ₀⟩ := Q.2
        exact ⟨Q₀, by rw [hQ₀]; rfl⟩⟩
      left_inv := fun P => by ext1; simp
      right_inv := fun Q => by ext1; simp }
  rw [← Nat.card_congr (eK.trans e'), Nat.card_prod, Nat.card_zmod, pow_two]

end Points

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

end ExtraLevelLatticeSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv.ExtraLevelLatticeSol"

local notation "specOne" => (𝟙 (Spec (CommRingCat.of ℂ)) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))

open ExtraLevelLatticeSol in
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
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ N ℂ) (K : E.ExtraLevel ℓ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ) :
    ∃ LK : Submodule ℤ (Fin 2 → ℂ),
      (∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) ∧
      latt E ≤ LK ∧
      (c * ℓ) • LK ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ (c * ℓ) • LK) ∧
      (∀ y ∈ Λ, ∀ v ∈ (c * ℓ) • LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ (c * ℓ) • LK) ∧
      ((c * ℓ) • LK).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧

      (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ (c * ℓ) • LK → v ∈ latt E) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hcℓ : c * (ℓ : ℂ) ≠ 0 := mul_ne_zero hc hℓ0

  have he0 : e E (E.L.one specOne) = 0 := equiv_one E (latt E) (e E) (hE1 E)
  have hsymm : ∀ v : Fin 2 → ℂ,
      e E ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) :=
    fun v => Equiv.apply_symm_apply _ _

  let LKg : AddSubgroup (Fin 2 → ℂ) := levelAddSubgroup E (latt E) (e E) K (hE1 E)
  let LK : Submodule ℤ (Fin 2 → ℂ) := AddSubgroup.toIntSubmodule LKg
  have hLK : ∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) :=
    fun v => Iff.rfl

  have hLE : latt E ≤ LK := by
    intro v hv
    rw [hLK, (QuotientAddGroup.eq_zero_iff v).2 hv, equiv_symm_zero E (latt E) (e E) (hE1 E)]
    exact K.levK_one specOne

  have htors : ∀ v : Fin 2 → ℂ, v ∈ LK → (ℓ : ℂ) • v ∈ latt E := by
    intro v hv
    have h1 := K.levK_torsion specOne _ ((hLK v).1 hv)
    have h2 := congrArg (e E) h1
    rw [equiv_nsmulPt E (latt E) (e E) (hE1 E), hsymm, he0, ← QuotientAddGroup.mk_nsmul,
      QuotientAddGroup.eq_zero_iff] at h2
    rwa [Nat.cast_smul_eq_nsmul]

  obtain ⟨hLevE, hLE', -, -, -⟩ := hLev E
  have hdisj : ∀ v : Fin 2 → ℂ, v ∈ lattLev E → v ∈ LK → v ∈ latt E := by
    intro v hv hvK
    obtain ⟨P, hPC, hPv⟩ := (hLevE v).1 hv
    have hP : P = (e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
      rw [Equiv.eq_symm_apply]; exact hPv
    have hPK : FactorsThrough K.levK P := by rw [hP]; exact (hLK v).1 hvK
    have hP1 : P = E.L.one specOne := K.levK_disjoint specOne P hPK hPC
    rw [hP1, he0] at hPv
    exact (QuotientAddGroup.eq_zero_iff v).1 hPv.symm

  have hstab : ∀ y ∈ Λ, ∀ v ∈ LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ LK := by
    intro y hy v hv
    rw [hLK] at hv ⊢
    have h := hE2 E ⟨y, hy⟩ _ v (hsymm v)
    have h' : (e E).symm ((((ι y).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) =
        pushPt (E.act ⟨y, hy⟩) (E.act_over ⟨y, hy⟩) ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) := by
      rw [Equiv.symm_apply_eq]; exact h.symm
    rw [h']
    exact K.levK_stable ⟨y, hy⟩ specOne _ hv

  have hidxK : (latt E).toAddSubgroup.relIndex LK.toAddSubgroup = ℓ ^ 2 := by
    have h1 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
      (QuotientAddGroup.mk' (latt E).toAddSubgroup) LK.toAddSubgroup
    rw [AddMonoidHom.comap_bot, QuotientAddGroup.ker_mk', AddSubgroup.relIndex_bot_left] at h1
    rw [h1, ← natCard_pts_extraLevel E K]
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquiv (e E).symm (fun x => ?_))
    change x ∈ (LK.toAddSubgroup).map (QuotientAddGroup.mk' (latt E).toAddSubgroup) ↔ _
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hLK v).1 hv
    · intro hx
      obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact ⟨v, (hLK v).2 hx, rfl⟩

  have hidx : (((ℓ : ℂ)) • LK).toAddSubgroup.relIndex (latt E).toAddSubgroup = ℓ ^ 2 := by
    obtain ⟨b₀, hb₀⟩ := (hL1 E).1
    have h4 : (((ℓ : ℂ)) • latt E).toAddSubgroup.relIndex (latt E).toAddSubgroup = ℓ ^ 4 := by
      rw [hb₀]; exact relIndex_natCast_smul_span b₀ ℓ
    have h2 : (((ℓ : ℂ)) • latt E).toAddSubgroup.relIndex (((ℓ : ℂ)) • LK).toAddSubgroup = ℓ ^ 2 := by
      rw [relIndex_smul hℓ0, hidxK]
    have hle1 : ((ℓ : ℂ)) • latt E ≤ ((ℓ : ℂ)) • LK := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v _ (latt E)).1 hv
      exact Submodule.smul_mem_pointwise_smul u _ LK (hLE hu)
    have hle2 : ((ℓ : ℂ)) • LK ≤ latt E := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v _ LK).1 hv
      exact htors u hu
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hle1)
      ((Submodule.toAddSubgroup_le _ _).2 hle2)
    rw [h2, h4, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at hmul
    exact mul_left_cancel₀ (pow_ne_zero 2 hℓ.ne_zero) hmul

  refine ⟨LK, hLK, hLE, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v _ LK).1 hv
    rw [← hcL, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ c (latt E) (htors u hu)
  ·
    intro v hv
    rw [← hcL] at hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v c (latt E)).1 hv
    have : ((ℓ : ℤ)) • (c • u) = (c * (ℓ : ℂ)) • u := by
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul, mul_comm]
    rw [this]
    exact Submodule.smul_mem_pointwise_smul u _ LK (hLE hu)
  ·
    intro y hy v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v _ LK).1 hv
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ LK (hstab y hy u hu)
  ·
    rw [← hcL, mul_smul, relIndex_smul hc, hidx]
  ·
    intro v hv hmem
    obtain ⟨u, hu, hu'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ LK).1 hmem
    have huv : u = v := by
      have : (c * (ℓ : ℂ)) • u = (c * (ℓ : ℂ)) • v := by rw [hu', mul_comm]
      exact smul_right_injective (Fin 2 → ℂ) hcℓ this
    subst huv
    exact hdisj u hv hu

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv.ExtraLevelLatticeSol"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_transversal_of_pointEquiv (solution)
