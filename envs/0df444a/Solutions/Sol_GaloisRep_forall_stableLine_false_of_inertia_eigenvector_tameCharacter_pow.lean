-- Prove2me | solution 1 for GaloisRep.forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/86038b83-118b-5d8d-a53a-0072414b5c27

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Theorems.Thm_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

namespace Niv2IrrAux

theorem sq_sub_trace_mul_add_det_eq_zero {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) (hv : v ≠ 0) (μ : K) (h : M.mulVec v = μ • v) :
    μ ^ 2 - M.trace * μ + M.det = 0 := by
  have hker : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]
  rw [Matrix.det_fin_two] at hker
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_one, mul_zero, sub_zero] at hker
  linear_combination hker

theorem charP_residueField (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    CharP (IsLocalRing.ResidueField P) p := by
  have hmem : (⟨(p : AlgebraicClosure ℚ), P.mem_of_valuation_le_one _ (le_of_lt hP)⟩ : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hP
  have h0 : (p : IsLocalRing.ResidueField P) = 0 := by
    have : IsLocalRing.residue P ⟨(p : AlgebraicClosure ℚ), P.mem_of_valuation_le_one _ (le_of_lt hP)⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [← map_natCast (IsLocalRing.residue P) p, ← this]
    congr 1
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

theorem not_dvd_sq_sub_one (p : ℕ) (hp : p.Prime) : ¬ p ∣ p ^ 2 - 1 := by
  intro h
  have h1 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h2 : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
  have h3 : p ∣ 1 := by
    have := (Nat.dvd_add_right h).mp (h2 ▸ h1)
    exact this
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

end Niv2IrrAux

open Niv2IrrAux in
theorem solution
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ψk : F →+* IsLocalRing.ResidueField P) (kn : ℕ) (hk2 : 2 ≤ kn) (hkp : kn ≤ p + 1)
    (hv : ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map ψk).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map ψk).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)))
    (u : Fin 2 → AlgebraicClosure F) (hu : u ≠ 0) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Matrix.mulVec ((ρ σ).val.map (algebraMap F (AlgebraicClosure F))) u ∉
        (AlgebraicClosure F) ∙ u := by
  classical
  by_contra hcon
  push_neg at hcon

  let e : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have he : e = algebraMap F (AlgebraicClosure F) := rfl
  haveI : CharP (IsLocalRing.ResidueField P) p := charP_residueField p P hP
  haveI : CharP F p := (RingHom.charP_iff_charP ψk p).mpr inferInstance
  haveI : CharP (AlgebraicClosure F) p := charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p

  let A : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (AlgebraicClosure F) :=
    (e.mapMatrix.toMonoidHom).comp ((Units.coeHom _).comp ρ)
  have hA : ∀ σ, A σ = (ρ σ).val.map e := fun σ => rfl

  have hc : ∀ σ, ∃ c : AlgebraicClosure F, (A σ).mulVec u = c • u := by
    intro σ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcon σ)
    exact ⟨c, by rw [hA]; exact hc.symm⟩
  choose c hcu using hc
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext fun i => by rw [Pi.zero_apply]; exact h i)
  have hcancel : ∀ a b : AlgebraicClosure F, a • u = b • u → a = b := by
    intro a b hab
    have := congrFun hab i₀
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi₀ this
  have hc_one : c 1 = 1 := by
    apply hcancel
    rw [← hcu 1, map_one, Matrix.one_mulVec, one_smul]
  have hc_mul : ∀ σ τ, c (σ * τ) = c σ * c τ := by
    intro σ τ
    apply hcancel
    rw [← hcu, map_mul, ← Matrix.mulVec_mulVec, hcu τ, Matrix.mulVec_smul, hcu σ, smul_smul, mul_comm]
  have hc_ne : ∀ σ, c σ ≠ 0 := by
    intro σ h0
    have h1 : c (σ⁻¹ * σ) = 0 := by rw [hc_mul, h0, mul_zero]
    rw [inv_mul_cancel, hc_one] at h1
    exact one_ne_zero h1

  let χ₁ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (AlgebraicClosure F)ˣ :=
    { toFun := fun σ => Units.mk0 (c σ) (hc_ne σ)
      map_one' := Units.ext hc_one
      map_mul' := fun σ τ => Units.ext (hc_mul σ τ) }
  have hχ₁ : ∀ σ, (χ₁ σ : AlgebraicClosure F) = c σ := fun σ => rfl

  let δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (AlgebraicClosure F)ˣ :=
    (Units.map e.toMonoidHom).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hδ : ∀ σ, (δ σ : AlgebraicClosure F) = (A σ).det := by
    intro σ
    show e ((ρ σ).val.det) = ((ρ σ).val.map e).det
    exact RingHom.map_det e _
  let χ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (AlgebraicClosure F)ˣ := δ / χ₁
  have hχ₂ : ∀ σ, (χ₁ σ : AlgebraicClosure F) * χ₂ σ = (A σ).det := by
    intro σ
    show (χ₁ σ : AlgebraicClosure F) * (((δ / χ₁) σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = _
    rw [← Units.val_mul, MonoidHom.div_apply, mul_div_cancel, hδ]

  obtain ⟨L₀, hL₀, h1⟩ := hfin
  have hA1 : ∀ σ, (∀ x ∈ L₀, σ x = x) → A σ = 1 := by
    intro σ hσ; show e.mapMatrix ((ρ σ).val) = 1; rw [h1 σ hσ, Units.val_one, map_one]
  have hχ₁triv : ∀ σ, (∀ x ∈ L₀, σ x = x) → χ₁ σ = 1 := by
    intro σ hσ
    apply Units.ext
    rw [hχ₁, Units.val_one]
    apply hcancel
    rw [← hcu, hA1 σ hσ, Matrix.one_mulVec, one_smul]
  have hfin₁ : GaloisFactorsThroughFiniteLevel χ₁ := ⟨L₀, hL₀, hχ₁triv⟩
  have hfin₂ : GaloisFactorsThroughFiniteLevel χ₂ := by
    refine ⟨L₀, hL₀, fun σ hσ => ?_⟩
    show δ σ / χ₁ σ = 1
    rw [hχ₁triv σ hσ, div_one]
    apply Units.ext
    show e ((ρ σ).val.det) = 1
    rw [h1 σ hσ, Units.val_one, Matrix.det_one, map_one]

  have hpow₁ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, c τ ^ (p - 1) = 1 := by
    intro τ hτ
    have := GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn p χ₁ hfin₁ P hP hτ
    have h' := congrArg (fun x : (AlgebraicClosure F)ˣ => (x : AlgebraicClosure F)) this
    simpa [hχ₁] using h'
  have hpow₂ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (χ₂ τ : AlgebraicClosure F) ^ (p - 1) = 1 := by
    intro τ hτ
    have := GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn p χ₂ hfin₂ P hP hτ
    have h' := congrArg (fun x : (AlgebraicClosure F)ˣ => (x : AlgebraicClosure F)) this
    simpa using h'

  have htrdet : ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      ((ρ (τ ^ (p - 1))).val).trace = 2 ∧ ((ρ (τ ^ (p - 1))).val).det = 1 := by
    intro τ hτ
    have hτ' : τ ^ (p - 1) ∈ P.inertiaSubgroupIn ℚ := Subgroup.pow_mem _ hτ _

    have hcτ' : c (τ ^ (p - 1)) = 1 := by rw [← hχ₁, map_pow, Units.val_pow_eq_pow_val, hχ₁, hpow₁ τ hτ]
    have hdet' : (A (τ ^ (p - 1))).det = 1 := by
      rw [← hχ₂, hχ₁, hcτ', one_mul, map_pow, Units.val_pow_eq_pow_val, hpow₂ τ hτ]
    have heig : (A (τ ^ (p - 1))).mulVec u = (1 : AlgebraicClosure F) • u := by rw [hcu, hcτ']
    have hq := sq_sub_trace_mul_add_det_eq_zero (A (τ ^ (p - 1))) u hu 1 heig
    rw [hdet'] at hq
    have htr' : (A (τ ^ (p - 1))).trace = 2 := by linear_combination -hq

    have hinj := (algebraMap F (AlgebraicClosure F)).injective
    constructor
    · apply hinj
      rw [map_ofNat]
      rw [← htr', hA]
      simp [Matrix.trace_fin_two, Matrix.map_apply]
      rfl
    · apply hinj
      rw [map_one, ← hdet', hA]
      exact RingHom.map_det _ _

  obtain ⟨v, hv0, hvcase⟩ := hv
  have hBpow : ∀ (B : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField P)) (lam : IsLocalRing.ResidueField P),
      B.mulVec v = lam • v → ∀ m : ℕ, (B ^ m).mulVec v = lam ^ m • v := by
    intro B lam hB m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  have hlam : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ lam : IsLocalRing.ResidueField P,
      ((ρ τ).val.map ψk).mulVec v = lam • v → lam ^ (p - 1) = 1 := by
    intro τ hτ lam hB
    obtain ⟨htr, hdet⟩ := htrdet τ hτ
    set Nm : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField P) := (ρ (τ ^ (p - 1))).val.map ψk with hNm
    have hNpow : Nm = ((ρ τ).val.map ψk) ^ (p - 1) := by
      rw [hNm, map_pow, Units.val_pow_eq_pow_val]
      exact map_pow ψk.mapMatrix _ _
    have htrN : Nm.trace = 2 := by
      have : ψk (((ρ (τ ^ (p - 1))).val).trace) = Nm.trace := by
        rw [hNm]; simp [Matrix.trace_fin_two, Matrix.map_apply]
      rw [← this, htr, map_ofNat]
    have hdetN : Nm.det = 1 := by
      have : ψk (((ρ (τ ^ (p - 1))).val).det) = Nm.det := by rw [hNm]; exact RingHom.map_det _ _
      rw [← this, hdet, map_one]
    have heigN : Nm.mulVec v = lam ^ (p - 1) • v := by rw [hNpow]; exact hBpow _ _ hB _
    have hq := sq_sub_trace_mul_add_det_eq_zero Nm v hv0 _ heigN
    rw [htrN, hdetN] at hq
    have : (lam ^ (p - 1) - 1) ^ 2 = 0 := by linear_combination hq
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

  obtain ⟨τ₀, hτ₀, hprim⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter P
    (Fact.out : p.Prime) hP (not_dvd_sq_sub_one p Fact.out) hπ
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have := Nat.sq_sub_sq p 1
    simpa using this
  have hk1 : 0 < kn - 1 := by omega
  have hk1' : kn - 1 < p + 1 := by omega
  have hcop : Nat.Coprime (p + 1) p := by
    rw [Nat.Coprime, add_comm, Nat.gcd_add_self_left, Nat.gcd_one_left]
  have hfinal : ¬ (p + 1 ∣ kn - 1) := fun h => (Nat.eq_zero_of_dvd_of_lt h hk1').symm.not_lt hk1 |>.elim
  rcases hvcase with hA' | hB'
  · have h1 := hlam τ₀ hτ₀ _ (hA' τ₀ hτ₀)
    rw [← pow_mul] at h1
    have hdvd := (hprim.pow_eq_one_iff_dvd _).mp h1
    rw [hsq] at hdvd
    exact hfinal (Nat.dvd_of_mul_dvd_mul_right hp1 hdvd)
  · have h1 := hlam τ₀ hτ₀ _ (hB' τ₀ hτ₀)
    rw [← pow_mul, ← pow_mul] at h1
    have hdvd := (hprim.pow_eq_one_iff_dvd _).mp h1
    rw [hsq] at hdvd
    have h2 : p + 1 ∣ p * (kn - 1) := by
      have : (p + 1) * (p - 1) ∣ (p * (kn - 1)) * (p - 1) := by
        have e1 : p * (kn - 1) * (p - 1) = p * ((kn - 1) * (p - 1)) := by ring
        rw [e1]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_right hp1 this
    exact hfinal (hcop.dvd_of_dvd_mul_left h2)

end S_GaloisRep_forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow
end P2MW
export P2MW.S_GaloisRep_forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow (solution)
