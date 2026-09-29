-- Prove2me | solution 1 for ExtCitation.comap_rootsOfUnity_levels_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/09130917-3512-5906-82f5-8a17a5b2de96

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum

import Theorems.Thm_ExtCitation_exists_padicLevel_fixingSubgroup_eq_of_isOpen
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Theorems.Thm_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_comap_rootsOfUnity_levels_of_isOpen
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (N : ℕ) (hN : 0 < N) :
    (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).Normal ∧ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))).FiniteIndex ∧
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      F.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) ∧
    (∃ φ : S, ∀ g : S, ∃ (n : ℤ) (u : S), u ∈ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) ∧ g = φ ^ n * u) ∧
    (∀ N' : ℕ, N ∣ N' → (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N' - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))) ≤ (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) ∧
    (∃ N' : ℕ, 0 < N' ∧ N ∣ N' ∧ p ∣ ((Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N' - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))).relIndex (Subgroup.comap S.subtype (((IntermediateField.adjoin ℚ_[q] {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ N - 1) = 1}).fixingSubgroup
              : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q)))) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨K, hKfd, hKS⟩ := ExtCitation.exists_padicLevel_fixingSubgroup_eq_of_isOpen q S hS
  haveI := hKfd
  let e : ↥S ≃* (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) :=
    (MulEquiv.subgroupCongr hKS).symm.trans (IntermediateField.fixingSubgroupEquiv K)
  let rK : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal q).comp (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)
  have hre' : ∀ τ, rK τ = ((primeLocalToGlobal q).comp S.subtype) (e.symm τ) := fun _ => rfl
  have hre : ∀ s : S, rK (e s) = ((primeLocalToGlobal q).comp S.subtype) s := by
    intro s
    rw [hre', MulEquiv.symm_apply_apply]

  let aut : ↥S → (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) := fun s => s.1
  let μ : ℕ → Set (PadicAlgCl q) := fun M => {ζ : PadicAlgCl q | ζ ^ ((q : ℕ) ^ M - 1) = 1}
  let U : ℕ → Subgroup S := fun M => Subgroup.comap S.subtype
    (((IntermediateField.adjoin ℚ_[q] (μ M)).fixingSubgroup : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)) : Subgroup (primeLocalGaloisGroup q))
  let E : ℕ → IntermediateField K (PadicAlgCl q) := fun M => IntermediateField.adjoin K (μ M)
  have hEfd : ∀ M, 0 < M → FiniteDimensional K (E M) := fun M hM =>
    (IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K M hM).1
  have hEn : ∀ M, 0 < M → Normal K (E M) := fun M hM =>
    (IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K M hM).2

  have hadj : ∀ {F : Type} [Field F] [Algebra F (PadicAlgCl q)] (σ : PadicAlgCl q ≃ₐ[F] PadicAlgCl q) (s : Set (PadicAlgCl q)),
      (∀ ζ ∈ s, σ ζ = ζ) → ∀ x ∈ IntermediateField.adjoin F s, σ x = x := by
    intro F _ _ σ s hs x hx
    have hle : IntermediateField.adjoin F s ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (PadicAlgCl q ≃ₐ[F] PadicAlgCl q) ζ :=
        (Subgroup.zpowers_le).2 (hs ζ hζ)
      exact hstab hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) σ (Subgroup.mem_zpowers σ)

  have hUiff : ∀ (M : ℕ) (s : S), s ∈ U M ↔ ∀ ζ ∈ μ M, aut s ζ = ζ := by
    intro M s
    show aut s ∈ (IntermediateField.adjoin ℚ_[q] (μ M)).fixingSubgroup ↔ _
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h ζ hζ => h ζ (IntermediateField.subset_adjoin ℚ_[q] (μ M) hζ), fun h => hadj _ _ h⟩
  have hUE : ∀ (M : ℕ) (s : S), s ∈ U M ↔ e s ∈ (E M).fixingSubgroup := by
    intro M s
    rw [hUiff, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h => hadj (e s) _ h, fun h ζ hζ => h ζ (IntermediateField.subset_adjoin K (μ M) hζ)⟩
  have hUeq : ∀ M, U M = ((E M).fixingSubgroup).comap e.toMonoidHom := fun M => Subgroup.ext (hUE M)
  have hker : ∀ (L : IntermediateField K (PadicAlgCl q)) [Normal K L],
      L.fixingSubgroup = (AlgEquiv.restrictNormalHom (K₁ := PadicAlgCl q) L).ker :=
    fun L _ => (IntermediateField.restrictNormalHom_ker L).symm

  have hindex : ∀ (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] [Normal K L],
      (L.fixingSubgroup).index = Module.finrank K L := by
    intro L _ _
    haveI : IsGalois K L := ⟨⟩
    rw [hker L, Subgroup.index_ker, MonoidHom.range_eq_top.2 (AlgEquiv.restrictNormalHom_surjective (PadicAlgCl q)),
      Subgroup.card_top]
    exact IsGalois.card_aut_eq_finrank K L

  have hμmono : ∀ M c : ℕ, μ M ⊆ μ (M * c) := by
    intro M c ζ hζ
    have hq0 : 0 < (q : ℕ) := q.2.pos
    have hd : (q : ℕ) ^ M - 1 ∣ (q : ℕ) ^ (M * c) - 1 := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_sub (Nat.one_le_pow _ _ hq0), Nat.cast_sub (Nat.one_le_pow _ _ hq0)]
      push_cast
      exact pow_one_sub_dvd_pow_mul_sub_one (q : ℤ) M c
    obtain ⟨d, hd⟩ := hd
    show ζ ^ ((q : ℕ) ^ (M * c) - 1) = 1
    have hζ' : ζ ^ ((q : ℕ) ^ M - 1) = 1 := hζ
    rw [hd, pow_mul, hζ', one_pow]
  haveI : FiniteDimensional K (E N) := hEfd N hN
  haveI : Normal K (E N) := hEn N hN
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩

  · have hn : ((E N).fixingSubgroup).Normal := by rw [hker (E N)]; exact MonoidHom.normal_ker _
    show (U N).Normal
    rw [hUeq]
    exact hn.comap _

  · show (U N).FiniteIndex
    refine ⟨?_⟩
    rw [hUeq, Subgroup.index_comap_of_surjective _ (show Function.Surjective e.toMonoidHom from e.surjective), hindex (E N)]
    exact Module.finrank_pos.ne'

  · obtain ⟨F, hF, hFE⟩ := IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) K (E N)
    refine ⟨F, hF, fun s hs => ?_⟩
    show s ∈ U N
    rw [hUE]
    apply hFE
    rw [hre]
    exact hs

  · obtain ⟨φE, hgen, -⟩ := IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic (q : ℕ) K N hN
    obtain ⟨φK, hφK⟩ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl q) φE
    refine ⟨e.symm φK, fun g => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hgen (AlgEquiv.restrictNormalHom (E N) (e g)))
    refine ⟨n, (e.symm φK) ^ (-n) * g, ?_, by group⟩
    show (e.symm φK) ^ (-n) * g ∈ U N
    rw [hUE, hker (E N), MonoidHom.mem_ker, map_mul, map_zpow, MulEquiv.apply_symm_apply, map_mul, map_zpow, hφK, ← hn,
      ← zpow_add, neg_add_cancel, zpow_zero]

  · rintro N' ⟨c, rfl⟩ s hs
    show s ∈ U N
    rw [hUiff] at hs ⊢
    exact fun ζ hζ => hs ζ (hμmono N c hζ)

  · obtain ⟨M, hM, hdM⟩ := IntermediateField.exists_finrank_adjoin_rootsOfUnity_padic_eq (q : ℕ) K
      (p ^ Module.finrank K (E N)) (pow_pos hp.pos _)
    have hNM : 0 < N * M := Nat.mul_pos hN hM
    refine ⟨N * M, hNM, dvd_mul_right N M, ?_⟩
    haveI : FiniteDimensional K (E M) := hEfd M hM
    haveI : Normal K (E M) := hEn M hM
    haveI : FiniteDimensional K (E (N * M)) := hEfd (N * M) hNM
    haveI : Normal K (E (N * M)) := hEn (N * M) hNM

    have hle₁ : (E (N * M)).fixingSubgroup ≤ (E N).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (IntermediateField.adjoin.mono K _ _ (hμmono N M))
    have hle₂ : (E (N * M)).fixingSubgroup ≤ (E M).fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone (IntermediateField.adjoin.mono K _ _ (by rw [mul_comm]; exact hμmono M N))

    have hrel : (U (N * M)).relIndex (U N) = ((E (N * M)).fixingSubgroup).relIndex ((E N).fixingSubgroup) := by
      rw [hUeq, hUeq, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
      exact e.surjective
    show p ∣ (U (N * M)).relIndex (U N)
    rw [hrel]
    have hmul := Subgroup.relIndex_mul_index hle₁
    rw [hindex (E N), hindex (E (N * M))] at hmul
    have hdvd : p ^ Module.finrank K (E N) ∣ Module.finrank K (E (N * M)) := by
      rw [← hdM, ← hindex (E M), ← hindex (E (N * M))]
      exact Subgroup.index_dvd_of_le hle₂
    rw [← hmul] at hdvd
    by_contra hndvd
    have hcop : Nat.Coprime (p ^ Module.finrank K (E N)) (((E (N * M)).fixingSubgroup).relIndex ((E N).fixingSubgroup)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
    have h1 : p ^ Module.finrank K (E N) ∣ Module.finrank K (E N) := hcop.dvd_of_dvd_mul_left hdvd
    have h2 : Module.finrank K (E N) < p ^ Module.finrank K (E N) := Nat.lt_pow_self hp.one_lt
    exact absurd (Nat.le_of_dvd Module.finrank_pos h1) (not_le.2 h2)

end S_ExtCitation_comap_rootsOfUnity_levels_of_isOpen
end P2MW
export P2MW.S_ExtCitation_comap_rootsOfUnity_levels_of_isOpen (solution)
