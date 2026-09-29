-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_lattLev_eq_of_isLevelIsogeny_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fa51f5ed-19ec-58be-ab84-e8c66b7e0dae

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

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_lattLev_eq_of_isLevelIsogeny_of_pointEquiv

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace LevelIsogenyLatticeSol

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

local notation "𝟭" => (𝟙 (Spec (CommRingCat.of ℂ)) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))

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
  (eE : SchemeHomOver 𝟭 E.f ≃ ((Fin 2 → ℂ) ⧸ L.toAddSubgroup))
  (heE : ∀ P Q : SchemeHomOver 𝟭 E.f, eE (E.L.mul 𝟭 P Q) = eE P + eE Q)

include heE in

theorem equiv_one : eE (E.L.one 𝟭) = 0 := by
  have h := heE (E.L.one 𝟭) (E.L.one 𝟭)
  rw [E.L.one_mul] at h

  have := congrArg (fun z => z - eE (E.L.one 𝟭)) h
  simpa using this.symm

include heE in

theorem equiv_symm_zero : eE.symm 0 = E.L.one 𝟭 := by
  rw [Equiv.symm_apply_eq]; exact (equiv_one E L eE heE).symm

end Points

end LevelIsogenyLatticeSol

local notation "𝟭" => (𝟙 (Spec (CommRingCat.of ℂ)) : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ))

open LevelIsogenyLatticeSol in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) {N : ℕ}

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
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓΛ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (E d : FakeEllipticCurve Λ N ℂ) (K : E.ExtraLevel ℓ)
    (hiso : FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) d)
    (LK : Submodule ℤ (Fin 2 → ℂ))
    (hLK : ∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) :
    ∃ c' : ℂ, c' ≠ 0 ∧ c' • latt d = LK ∧

      (∀ v : Fin 2 → ℂ, v ∈ c' • lattLev d ↔ ∃ w ∈ lattLev E, ∃ m ∈ LK, w + m = v) := by
  have hN : N ≠ 0 := level_ne_zero E

  obtain ⟨φ, hφ, ψ, hψ, hφmul, hψmul, hφact, hψact, hcomp, hker, hlev⟩ := hiso
  dsimp only at φ hφ ψ hψ hφmul hψmul hφact hψact hcomp hker hlev

  obtain ⟨c, hc1, hc2⟩ := hH1 E d φ hφ (fun t P Q => hφmul t P Q) hφact
  obtain ⟨c₂, hc₂1, hc₂2⟩ := hH1 d E ψ hψ (fun t P Q => hψmul t P Q) hψact

  have he0 : ∀ E' : FakeEllipticCurve Λ N ℂ, e E' (E'.L.one 𝟭) = 0 :=
    fun E' => equiv_one E' (latt E') (e E') (hE1 E')
  have hsymm : ∀ (E' : FakeEllipticCurve Λ N ℂ) (v : Fin 2 → ℂ),
      e E' ((e E').symm (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) = (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup) :=
    fun E' v => Equiv.apply_symm_apply _ _

  have hcompℓ : φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩ := (hcomp hℓΛ).1
  have hpushℓ : ∀ P : SchemeHomOver 𝟭 E.f,
      mapPt ψ hψ (mapPt φ hφ P) = pushPt (E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓΛ⟩) (E.act_over _) P := by
    intro P
    rw [mapPt_mapPt]
    exact mapPt_congr hcompℓ _ _ P

  have hcc : c₂ * c = (ℓ : ℂ) := by
    obtain ⟨b₀, hb₀⟩ := (hL1 E).1
    have key : ∀ v : Fin 2 → ℂ, (c₂ * c - (ℓ : ℂ)) • v ∈ latt E := by
      intro v
      have hv := hsymm E v
      have h1 := hc2 _ v hv
      have h2 : e E (mapPt ψ hψ (mapPt φ hφ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)))) =
          ((c₂ • (c • v) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := hc₂2 _ _ h1
      have h3 : e E (mapPt ψ hψ (mapPt φ hφ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)))) =
          (((ℓ : ℂ) • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
        rw [hpushℓ, hE2 E _ _ v hv]
        simp only [map_iota_ratCast_mulVec, Rat.cast_natCast]
      rw [h2, QuotientAddGroup.eq_iff_sub_mem] at h3
      simpa [sub_smul, smul_smul] using h3
    have h0 : c₂ * c - (ℓ : ℂ) = 0 :=
      eq_zero_of_forall_smul_mem_span b₀ _ (fun v => by rw [← hb₀]; exact key v)
    exact sub_eq_zero.mp h0
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hc : c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcc; exact hℓ0 hcc.symm

  have hLK' : ∀ v : Fin 2 → ℂ, v ∈ LK ↔ c • v ∈ latt d := by
    intro v
    refine (hLK v).trans ?_
    refine (hker 𝟭 _).symm.trans ?_
    rw [← (e d).injective.eq_iff, hc2 _ v (hsymm E v), he0 d, QuotientAddGroup.eq_zero_iff]
    rfl

  obtain ⟨hLevE, hLE, -, -, hidxE⟩ := hLev E
  obtain ⟨hLevd, hLd, -, -, hidxd⟩ := hLev d
  have hdisj : ∀ v : Fin 2 → ℂ, v ∈ lattLev E → v ∈ LK → v ∈ latt E := by
    intro v hv hvK
    obtain ⟨P, hPC, hPv⟩ := (hLevE v).1 hv
    have hP : P = (e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
      rw [Equiv.eq_symm_apply]; exact hPv
    have hPK : FactorsThrough K.levK P := by rw [hP]; exact (hLK v).1 hvK
    have hP1 : P = E.L.one 𝟭 := K.levK_disjoint 𝟭 P hPK hPC
    rw [hP1, he0 E] at hPv
    exact (QuotientAddGroup.eq_zero_iff v).1 hPv.symm

  have hlevLat : ∀ w : Fin 2 → ℂ, w ∈ lattLev E → c • w ∈ lattLev d := by
    intro w hw
    obtain ⟨P, hPC, hPw⟩ := (hLevE w).1 hw
    exact (hLevd (c • w)).2 ⟨mapPt φ hφ P, hlev 𝟭 P hPC, hc2 P w hPw⟩

  have hAle : c • lattLev E ⊔ latt d ≤ lattLev d := by
    refine sup_le ?_ hLd
    intro v hv
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v c (lattLev E)).1 hv
    exact hlevLat w hw
  have hdA : latt d ≤ c • lattLev E ⊔ latt d := le_sup_right

  have hinf : latt d ⊓ c • lattLev E = c • latt E := by
    ext v
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨hvd, hvc⟩
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c (lattLev E)).1 hvc
      have hwK : w ∈ LK := (hLK' w).2 hvd
      exact Submodule.smul_mem_pointwise_smul w c (latt E) (hdisj w hw hwK)
    · intro hv
      obtain ⟨u, hu, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v c (latt E)).1 hv
      exact ⟨hc1 u hu, Submodule.smul_mem_pointwise_smul u c (lattLev E) (hLE hu)⟩

  have hidxA : (latt d).toAddSubgroup.relIndex (c • lattLev E ⊔ latt d).toAddSubgroup = N ^ 2 := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right,
      ← inf_toAddSubgroup, hinf, relIndex_smul hc, hidxE]

  have hAeq : c • lattLev E ⊔ latt d = lattLev d := by
    refine le_antisymm hAle ?_
    have hmul := AddSubgroup.relIndex_mul_relIndex (latt d).toAddSubgroup (c • lattLev E ⊔ latt d).toAddSubgroup
      (lattLev d).toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 hdA) ((Submodule.toAddSubgroup_le _ _).2 hAle)
    rw [hidxA, hidxd] at hmul
    have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have h1 : (c • lattLev E ⊔ latt d).toAddSubgroup.relIndex (lattLev d).toAddSubgroup = 1 :=
      mul_right_injective₀ hN2 (hmul.trans (mul_one _).symm)
    exact (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1)

  refine ⟨c⁻¹, inv_ne_zero hc, ?_, ?_⟩
  · ext v
    rw [mem_inv_smul_iff hc, hLK' v]
  · intro v
    rw [mem_inv_smul_iff hc, ← hAeq, Submodule.mem_sup]
    constructor
    · rintro ⟨y, hy, z, hz, hyz⟩
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y c (lattLev E)).1 hy
      refine ⟨w, hw, c⁻¹ • z, (hLK' _).2 (by rwa [smul_smul, mul_inv_cancel₀ hc, one_smul]), ?_⟩
      have := congrArg (fun u => c⁻¹ • u) hyz
      simpa [smul_add, smul_smul, inv_mul_cancel₀ hc] using this
    · rintro ⟨w, hw, m, hm, rfl⟩
      refine ⟨c • w, Submodule.smul_mem_pointwise_smul w c _ hw, c • m, (hLK' m).1 hm, ?_⟩
      rw [smul_add]

end

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_lattLev_eq_of_isLevelIsogeny_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_lattLev_eq_of_isLevelIsogeny_of_pointEquiv (solution)
