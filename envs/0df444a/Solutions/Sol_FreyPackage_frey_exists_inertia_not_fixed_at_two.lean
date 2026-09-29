-- Prove2me | solution 1 for FreyPackage.frey_exists_inertia_not_fixed_at_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c3c6817c-3227-5734-a7c8-d04f670a7888

import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_FreyPackage_freyCurveInt_discr_ne_zero
import Theorems.Thm_FreyPackage_dvd_freyCurveInt_discr_iff
import Theorems.Thm_FreyPackage_not_dvd_freyCurveInt_c4
import Theorems.Thm_FreyPackage_padicValInt_two_freyCurveInt_discr
import Theorems.Thm_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr
import Theorems.Thm_WeierstrassCurve_exists_criticalCentre_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction
import Theorems.Thm_WeierstrassCurve_not_inZeroComponentAt_some_iff_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_padicValInt
import Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
import Theorems.Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_frey_exists_inertia_not_fixed_at_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped Pointwise

noncomputable section

namespace FW2Aux

private lemma geom_factor {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} {ζ : R}
    (hζ : ζ ^ p = 1) (hne : ζ ≠ 1) :
    (p : R) = (1 - ζ) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
  have hsum0 : ∑ i ∈ Finset.range p, ζ ^ i = 0 := by
    have h1 : (∑ i ∈ Finset.range p, ζ ^ i) * (ζ - 1) = 0 := by
      rw [geom_sum_mul, hζ, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  calc (p : R) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
        rw [Finset.sum_sub_distrib, hsum0, sub_zero, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
    _ = ∑ i ∈ Finset.range p, (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hgs := geom_sum_mul ζ i
        linear_combination hgs
    _ = (1 - ζ) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
        rw [Finset.mul_sum]

private lemma valuation_sub_one_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hv2 : A.valuation (2 : AlgebraicClosure ℚ) < 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ p = 1) (hne : ζ ≠ 1) :
    A.valuation (ζ - 1) = 1 := by
  have hvζ : A.valuation ζ = 1 := by
    refine pow_left_injective (M := A.ValueGroup) hp.ne_zero ?_
    show A.valuation ζ ^ p = 1 ^ p
    rw [← map_pow, hζ, map_one, one_pow]
  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hvζ.le
  have hYA : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
    sum_mem fun i _ => sum_mem fun j _ => pow_mem hζA j
  have h1A : (1 - ζ) ∈ A := sub_mem (one_mem A) hζA
  have hvp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) = 1 := by
    refine A.valuation_natCast_eq_one_of_not_dvd Nat.prime_two ?_ ?_
    · have h2 : ((2 : ℕ) : AlgebraicClosure ℚ) = (2 : AlgebraicClosure ℚ) := by norm_num
      rw [h2]; exact hv2
    · intro hdvd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h | h
      · exact absurd h (by norm_num)
      · exact hp2 h.symm
  have hfact := geom_factor hζ hne
  have hvmul : A.valuation (1 - ζ) *
      A.valuation (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) = 1 := by
    rw [← map_mul, ← hfact]
    exact hvp
  have hle1 : A.valuation (1 - ζ) ≤ 1 := (A.valuation_le_one_iff _).mpr h1A
  have hleY : A.valuation (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr hYA
  have h1 : A.valuation (1 - ζ) = 1 := by
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · exact absurd hvmul (mul_lt_one_of_lt_of_le hlt hleY).ne
    · exact heq
  calc A.valuation (ζ - 1) = A.valuation (-(1 - ζ)) := by rw [neg_sub]
    _ = A.valuation (1 - ζ) := Valuation.map_neg _ _
    _ = 1 := h1

private lemma valuation_smul_lt_one (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (B : ValuationSubring (AlgebraicClosure ℚ)) {z : AlgebraicClosure ℚ}
    (hz : B.valuation z < 1) : (g • B).valuation (g z) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
  rcases hz with h0 | hinv
  · left; rw [h0, _root_.map_zero]
  · right
    rw [← map_inv₀]
    intro hmem
    rw [show g z⁻¹ = g • z⁻¹ from rfl,
      ValuationSubring.smul_mem_pointwise_smul_iff] at hmem
    exact hinv hmem

private lemma mem_inertiaSubgroupIn_of (B : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hD : σ ∈ B.decompositionSubgroup ℚ)
    (helt : ∀ b : AlgebraicClosure ℚ, b ∈ B → B.valuation (σ b - b) < 1) :
    σ ∈ B.inertiaSubgroupIn ℚ := by
  refine Subgroup.mem_map.mpr ⟨⟨σ, hD⟩, ?_, rfl⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  refine RingEquiv.ext fun xbar => ?_
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  show (IsLocalRing.residue B) ((⟨σ, hD⟩ : B.decompositionSubgroup ℚ) • c)
    = (IsLocalRing.residue B) c
  refine Ideal.Quotient.eq.mpr ?_
  refine (B.valuation_lt_one_iff _).mpr ?_
  have hcoe : (((⟨σ, hD⟩ : B.decompositionSubgroup ℚ) • c - c : B) : AlgebraicClosure ℚ)
      = σ (c : AlgebraicClosure ℚ) - (c : AlgebraicClosure ℚ) := rfl
  rw [hcoe]
  exact helt _ c.2

private lemma conj_mem_inertiaSubgroupIn (g σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hσ : σ ∈ B.inertiaSubgroupIn ℚ) :
    g * σ * g⁻¹ ∈ (g • B).inertiaSubgroupIn ℚ := by
  have hD : σ ∈ B.decompositionSubgroup ℚ := by
    obtain ⟨τ, _, rfl⟩ := hσ
    exact τ.2
  have hB : σ • B = B := MulAction.mem_stabilizer_iff.mp hD
  refine mem_inertiaSubgroupIn_of (g • B) (g * σ * g⁻¹) ?_ ?_
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hB]
  · intro b hb
    have hb' : g⁻¹ b ∈ B := by
      have := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hb
      exact this
    obtain ⟨_, hlt⟩ :=
      ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn B hσ hb'
    have hz : (g * σ * g⁻¹) b - b = g (σ (g⁻¹ b) - g⁻¹ b) := by
      rw [map_sub]
      have h1 : (g * σ * g⁻¹) b = g (σ (g⁻¹ b)) := rfl
      have h2 : g (g⁻¹ b) = b := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
      rw [h1, h2]
    rw [hz]
    exact valuation_smul_lt_one g B hlt

end FW2Aux

namespace FW2Aux

private def kumPoly (p m : ℕ) : Polynomial ℚ := Polynomial.X ^ p - Polynomial.C ((2 : ℚ) ^ m)

private def kumField (p m : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ((kumPoly p m).rootSet (AlgebraicClosure ℚ))

private scoped instance (p m : ℕ) : Polynomial.IsSplittingField ℚ (kumField p m) (kumPoly p m) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

private scoped instance (p m : ℕ) : FiniteDimensional ℚ (kumField p m) :=
  Polynomial.IsSplittingField.finiteDimensional (kumField p m) (kumPoly p m)

private scoped instance (p m : ℕ) : Normal ℚ (kumField p m) :=
  Normal.of_isSplittingField (kumPoly p m)

private scoped instance (p m : ℕ) : IsGalois ℚ (kumField p m) := ⟨⟩

private scoped instance (p m : ℕ) : NumberField (kumField p m) := ⟨⟩

set_option synthInstance.maxHeartbeats 4000000 in

private lemma exists_inertia_ne_of_pow_eq (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime 2) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : ¬ p ∣ m)
    {s : AlgebraicClosure ℚ} (hs : s ^ p = (2 : AlgebraicClosure ℚ) ^ m) :
    ∃ τ ∈ A.inertiaSubgroupIn ℚ, τ s ≠ s := by
  have h2ne : (2 : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hs
    exact pow_ne_zero m h2ne hs.symm

  set L := kumField p m with hLdef
  haveI : FiniteDimensional ℚ L := inferInstanceAs (FiniteDimensional ℚ (kumField p m))
  haveI hNorm : Normal ℚ L := inferInstanceAs (Normal ℚ (kumField p m))
  haveI : IsGalois ℚ L := inferInstanceAs (IsGalois ℚ (kumField p m))
  haveI : NumberField L := inferInstanceAs (NumberField (kumField p m))
  have hfne : kumPoly p m ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hp.pos _
  have hroot : ∀ r : AlgebraicClosure ℚ, r ^ p = (2 : AlgebraicClosure ℚ) ^ m →
      r ∈ (kumPoly p m).rootSet (AlgebraicClosure ℚ) := by
    intro r hr
    rw [Polynomial.mem_rootSet]
    refine ⟨hfne, ?_⟩
    rw [kumPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, hr]
    rw [map_pow]
    norm_num
  have hsL : s ∈ L := IntermediateField.subset_adjoin ℚ _ (hroot s hs)
  set shat : L := ⟨s, hsL⟩ with hshat
  have hshat0 : shat ≠ 0 := by
    intro h
    exact hs0 (by simpa [hshat] using congrArg (Subtype.val) h)
  have hshatpow : shat ^ p = (2 : L) ^ m := by
    apply Subtype.coe_injective
    push_cast
    exact hs

  haveI hmax2 : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := NumberField.RingOfIntegers L)
      (Ideal.span {(2 : ℤ)})
  haveI := hQmax
  haveI := hQover
  have h2Q : (2 : NumberField.RingOfIntegers L) ∈ Q := by
    have h2span : (2 : ℤ) ∈ Ideal.span {(2 : ℤ)} := Ideal.subset_span rfl
    have := hQover.over ▸ h2span
    rw [Ideal.mem_comap] at this
    simpa using this
  have h2Qne : (2 : NumberField.RingOfIntegers L) ≠ 0 := by
    intro h
    have : ((2 : NumberField.RingOfIntegers L) : L) = 0 := by rw [h]; simp
    norm_num at this
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at h2Q
    exact h2Qne h2Q

  have hsint : IsIntegral ℤ shat := by
    refine ⟨Polynomial.X ^ p - Polynomial.C ((2 : ℤ) ^ m),
      Polynomial.monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hshatpow, map_pow,
      map_ofNat, sub_self]
  set shatO : NumberField.RingOfIntegers L := ⟨shat, hsint⟩ with hshatO
  have hshatOpow : shatO ^ p = (2 : NumberField.RingOfIntegers L) ^ m := by
    apply Subtype.ext
    show shat ^ p = (2 : L) ^ m
    exact hshatpow

  by_contra hall
  push Not at hall

  have hclaim : ∃ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) ∧ τbar shat ≠ shat := by
    by_contra hfin
    push Not at hfin

    have hζfix : ∀ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) →
        ∀ ζ : L, ζ ^ p = 1 → τbar ζ = ζ := by
      intro τbar hτbar ζ hζp
      have hζint : IsIntegral ℤ ζ := by
        refine ⟨Polynomial.X ^ p - Polynomial.C (1 : ℤ),
          Polynomial.monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hζp, map_one,
          sub_self]
      set ζO : NumberField.RingOfIntegers L := ⟨ζ, hζint⟩ with hζO
      have hζOpow : ζO ^ p = 1 := by
        apply Subtype.ext
        show ζ ^ p = 1
        exact hζp
      have hmem := AddSubgroup.mem_inertia.mp hτbar ζO
      have hsmulcoe : ((τbar • ζO : NumberField.RingOfIntegers L) : L) = τbar ζ := rfl

      set ζ' : NumberField.RingOfIntegers L := (τbar • ζO) * ζO ^ (p - 1) with hζ'
      have hζζ : ζO * ζO ^ (p - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
        exact hζOpow
      have hζ'pow : ζ' ^ p = 1 := by
        have h1 : (τbar • ζO) ^ p = 1 := by
          rw [← smul_pow', hζOpow, smul_one]
        rw [hζ', mul_pow, h1, one_mul, ← pow_mul, mul_comm (p - 1) p, pow_mul, hζOpow,
          one_pow]
      have hζ'sub : ζ' - 1 = (τbar • ζO - ζO) * ζO ^ (p - 1) := by
        rw [hζ', sub_mul, hζζ]
      have hζ'Q : ζ' - 1 ∈ Q := by
        rw [hζ'sub]
        exact Ideal.mul_mem_right _ _ hmem
      by_cases hζ'1 : ζ' = 1
      · have hτζ : τbar • ζO = ζO := by
          have key : τbar • ζO = ζ' * ζO := by
            rw [hζ', mul_assoc, mul_comm (ζO ^ (p - 1)) ζO, hζζ, mul_one]
          rw [key, hζ'1, one_mul]
        calc τbar ζ = ((τbar • ζO : NumberField.RingOfIntegers L) : L) := hsmulcoe.symm
          _ = ((ζO : NumberField.RingOfIntegers L) : L) := by rw [hτζ]
          _ = ζ := rfl
      ·
        exfalso
        have hpfact := geom_factor hζ'pow hζ'1
        have hpQ : ((p : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
          rw [hpfact]
          refine Ideal.mul_mem_right _ _ ?_
          have : (1 : NumberField.RingOfIntegers L) - ζ' = -(ζ' - 1) := by ring
          rw [this]
          exact Q.neg_mem hζ'Q
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        have h1Q : (1 : NumberField.RingOfIntegers L) ∈ Q := by
          have hcalc : (1 : NumberField.RingOfIntegers L)
              = ((p : ℕ) : NumberField.RingOfIntegers L) - (k : NumberField.RingOfIntegers L) * 2 := by
            have : ((p : ℕ) : NumberField.RingOfIntegers L)
                = 2 * (k : NumberField.RingOfIntegers L) + 1 := by
              rw [hk]; push_cast; ring
            rw [this]; ring
          rw [hcalc]
          exact Q.sub_mem hpQ (Ideal.mul_mem_left _ _ h2Q)
        exact hQmax.ne_top ((Ideal.eq_top_iff_one Q).mpr h1Q)

    have hfixall : ∀ τbar : L ≃ₐ[ℚ] L, τbar ∈ Q.inertia (L ≃ₐ[ℚ] L) → τbar = 1 := by
      intro τbar hτbar
      have hsfix : τbar shat = shat := hfin τbar hτbar
      have hroots : ∀ r (hr : r ∈ (kumPoly p m).rootSet (AlgebraicClosure ℚ)),
          τbar ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩
            = ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩ := by
        intro r hr
        set rhat : L := ⟨r, IntermediateField.subset_adjoin ℚ _ hr⟩ with hrhat
        have hrpow : rhat ^ p = (2 : L) ^ m := by
          apply Subtype.coe_injective
          push_cast [hrhat]
          have := (Polynomial.mem_rootSet.mp hr).2
          rw [kumPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at this
          have h2m : (algebraMap ℚ (AlgebraicClosure ℚ)) ((2:ℚ) ^ m)
              = (2 : AlgebraicClosure ℚ) ^ m := by
            rw [map_pow]; norm_num
          rw [h2m] at this
          exact sub_eq_zero.mp this
        have hζpow : (rhat * shat⁻¹) ^ p = 1 := by
          rw [mul_pow, hrpow, inv_pow, hshatpow, mul_inv_eq_one₀]
          exact pow_ne_zero m (by norm_num)
        have hζ := hζfix τbar hτbar (rhat * shat⁻¹) hζpow
        calc τbar rhat = τbar (rhat * shat⁻¹ * shat) := by
              rw [inv_mul_cancel_right₀ hshat0]
          _ = τbar (rhat * shat⁻¹) * τbar shat := map_mul τbar _ _
          _ = rhat * shat⁻¹ * shat := by rw [hζ, hsfix]
          _ = rhat := inv_mul_cancel_right₀ hshat0 _
      have hhom : (τbar : L →ₐ[ℚ] L) = AlgHom.id ℚ L :=
        IntermediateField.adjoin_algHom_ext ℚ fun r hr => hroots r hr
      exact AlgEquiv.ext fun x => DFunLike.congr_fun hhom x

    have hbot : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hfixall
    have hcard : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot

    letI : Field (ℤ ⧸ Ideal.span {(2:ℤ)}) := Ideal.Quotient.field _
    letI : Field (NumberField.RingOfIntegers L ⧸ Q) := Ideal.Quotient.field Q
    haveI : Finite (ℤ ⧸ Ideal.span {(2:ℤ)}) :=
      Finite.of_equiv _ (Int.quotientSpanEquivZMod 2).symm.toEquiv
    haveI : PerfectField (ℤ ⧸ Ideal.span {(2:ℤ)}) := PerfectField.ofFinite
    haveI : Algebra.IsIntegral (ℤ ⧸ Ideal.span {(2:ℤ)}) (NumberField.RingOfIntegers L ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver Q (Ideal.span {(2:ℤ)})
    haveI : Algebra.IsSeparable (ℤ ⧸ Ideal.span {(2:ℤ)}) (NumberField.RingOfIntegers L ⧸ Q) :=
      inferInstance

    have hcount2 : (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(2 : NumberField.RingOfIntegers L)})).count Q = 1 := by
      have hmap : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.span {(2:ℤ)}) = Ideal.span {(2 : NumberField.RingOfIntegers L)} := by
        rw [Ideal.map_span]
        norm_num
      have hmapne : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
          (Ideal.span {(2:ℤ)}) ≠ ⊥ := by
        rw [hmap]
        intro h
        rw [Ideal.span_singleton_eq_bot] at h
        exact h2Qne h
      rw [← hmap]
      rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapne
        inferInstance hQ0]
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (by simp)]
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(2:ℤ)}) Q (L ≃ₐ[ℚ] L)]
      rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Ideal.span {(2:ℤ)}) Q]
      exact hcard

    have hspan : Ideal.span {shatO} ^ p = Ideal.span {(2 : NumberField.RingOfIntegers L)} ^ m := by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, hshatOpow]
    have hcounts : p * (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {shatO})).count Q = m * (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(2 : NumberField.RingOfIntegers L)})).count Q := by
      have hc := congrArg
        (fun I => (UniqueFactorizationMonoid.normalizedFactors I).count Q) hspan
      simpa [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul] using hc
    rw [hcount2, mul_one] at hcounts
    exact hm ⟨_, hcounts.symm⟩
  obtain ⟨τbar, hτbar, hτbarne⟩ := hclaim

  obtain ⟨σ, hres, 𝔔, h𝔔max, h2𝔔, hσ𝔔⟩ :=
    NumberField.exists_lift_mem_inertia_integralClosure L Q (q := 2)
      (by exact_mod_cast h2Q) τbar hτbar
  haveI := h𝔔max
  obtain ⟨A₁, hA₁, hσA₁⟩ :=
    ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn 𝔔 Nat.prime_two h2𝔔 σ hσ𝔔

  have hσs : σ s ≠ s := by
    have happ : (AlgEquiv.restrictNormalHom L σ shat : AlgebraicClosure ℚ) = σ s :=
      @AlgEquiv.restrictNormalHom_apply ℚ _ _ _ _ L hNorm σ shat
    rw [hres] at happ
    intro heq
    apply hτbarne
    apply Subtype.coe_injective
    show ((τbar shat : L) : AlgebraicClosure ℚ) = ((shat : L) : AlgebraicClosure ℚ)
    rw [happ, heq]

  obtain ⟨g, hg⟩ :=
    ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime Nat.prime_two A A₁ hA hA₁
  have hθ : g⁻¹ * σ * g ∈ A.inertiaSubgroupIn ℚ := by
    have h1 : g⁻¹ * σ * (g⁻¹)⁻¹ ∈ (g⁻¹ • A₁).inertiaSubgroupIn ℚ :=
      conj_mem_inertiaSubgroupIn g⁻¹ σ A₁ hσA₁
    rw [inv_inv] at h1
    rw [← hg, inv_smul_smul] at h1
    exact h1
  have hθs : (g⁻¹ * σ * g) s = s := hall _ hθ
  have hσgs : σ (g s) = g s := by
    have h1 : g⁻¹ (σ (g s)) = s := by
      have := hθs
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      exact this
    have h2 := congrArg g h1
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2
    exact h2

  have hgs_pow : (g s) ^ p = (2 : AlgebraicClosure ℚ) ^ m := by
    rw [← map_pow, hs, map_pow, map_ofNat]
  have hζ2pow : (g s / s) ^ p = 1 := by
    rw [div_pow, hgs_pow, hs, div_self]
    exact pow_ne_zero m h2ne
  have hζ2fix : σ (g s / s) = g s / s :=
    ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn Nat.prime_two A₁ hA₁
      hσA₁ (by
        intro hdvd
        rcases Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd with h | h
        · exact absurd h (by norm_num)
        · exact hp2 h.symm) hζ2pow
  have hgs_eq : g s = (g s / s) * s := (div_mul_cancel₀ _ hs0).symm
  have hζ2ne : (g s / s) ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hζ2pow
    exact zero_ne_one hζ2pow

  apply hσs
  have hσgs' : σ (g s / s) * σ s = (g s / s) * s := by
    rw [← map_mul, ← hgs_eq]
    exact hσgs
  rw [hζ2fix] at hσgs'
  exact mul_left_cancel₀ hζ2ne hσgs'

end FW2Aux
p2m_reactivate "P2MW.S_FreyPackage_frey_exists_inertia_not_fixed_at_two.FW2Aux"

theorem solution (P : FreyPackage)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ τ ∈ A.inertiaSubgroupIn ℚ,
      ∃ x : Submodule.torsionBy ℤ
          ((P.freyCurveInt.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point P.p,
        τ • x ≠ x := by
  by_contra hall
  push Not at hall
  have hp2 : P.p ≠ 2 := by have := P.hp5; omega
  have hv2' : A.valuation ((2:ℕ) : AlgebraicClosure ℚ) < 1 := hA
  have hcast : ((2:ℕ) : AlgebraicClosure ℚ) = (2 : AlgebraicClosure ℚ) := by norm_num
  have hv2 : A.valuation (2 : AlgebraicClosure ℚ) < 1 := by rw [← hcast]; exact hv2'

  have hΔ0 : P.freyCurveInt.Δ ≠ 0 := P.freyCurveInt_discr_ne_zero
  have habc2 : ((2:ℕ) : ℤ) ∣ P.a * P.b * P.c := by exact_mod_cast P.two_dvd_abc
  have h2Δ : ((2:ℕ) : ℤ) ∣ P.freyCurveInt.Δ :=
    (P.dvd_freyCurveInt_discr_iff Nat.prime_two).mpr habc2
  have h2c₄ : ¬ ((2:ℕ) : ℤ) ∣ P.freyCurveInt.c₄ := P.not_dvd_freyCurveInt_c4 Nat.prime_two habc2

  obtain ⟨x₀, y₀, hx₀, hy₀, hFy, hFx, hnode, hbad, hIfix⟩ :=
    WeierstrassCurve.exists_criticalCentre_of_multiplicativeReduction P.freyCurveInt
      Nat.prime_two hΔ0 h2Δ h2c₄ A hA
  obtain ⟨T, hT⟩ :=
    WeierstrassCurve.exists_torsion_not_inZeroComponentAt_of_multiplicativeReduction P.freyCurveInt
      Nat.prime_two hΔ0 h2Δ h2c₄ A hA P.pp
  obtain ⟨pt, hptmem⟩ := T
  cases pt with
  | zero => exact hT (Or.inl rfl)
  | some x y hxy =>
    have htor : P.p • (Point.some x y hxy) = 0 := by
      have h1 := (Submodule.mem_torsionBy_iff _ _).mp hptmem
      rwa [natCast_zsmul] at h1
    have hX : A.valuation (x - x₀) < 1 :=
      (WeierstrassCurve.not_inZeroComponentAt_some_iff_of_criticalCentre P.freyCurveInt A hx₀ hy₀
        hFy hFx hnode hbad hxy).mp hT
    obtain ⟨-, j, hj1, hj2, hvpow⟩ :=
      WeierstrassCurve.valuation_pow_eq_of_torsion_of_not_inZeroComponentAt P.freyCurveInt
        Nat.prime_two hΔ0 h2Δ h2c₄ A hA hx₀ hy₀ hFy hFx hnode hbad P.pp hp2 hp2 hxy htor hX

    have hvΔ : A.valuation ((P.freyCurveInt.Δ : ℤ) : AlgebraicClosure ℚ)
        = A.valuation ((2:ℕ) : AlgebraicClosure ℚ) ^ padicValInt 2 P.freyCurveInt.Δ :=
      ValuationSubring.valuation_intCast_eq_pow_padicValInt A Nat.prime_two hv2' hΔ0
    have hvt : A.valuation (x - x₀) ^ P.p
        = A.valuation ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j) := by
      rw [hvpow, hvΔ, ← pow_mul]
    have hpm : ¬ P.p ∣ padicValInt 2 P.freyCurveInt.Δ * j := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul P.pp).mp hdvd with h | h
      · exact P.not_p_dvd_padicValInt_two_freyCurveInt_discr h
      · have := Nat.le_of_dvd (by omega) h
        omega

    have hfixt : ∀ τ ∈ A.inertiaSubgroupIn ℚ, τ (x - x₀) = x - x₀ := by
      intro τ hτ
      have hx : τ x = x := by
        have h1 := hall τ hτ ⟨Point.some x y hxy, hptmem⟩
        have h2 : τ • (Point.some x y hxy) = Point.some x y hxy := Subtype.ext_iff.mp h1
        rw [algEquiv_smul_def, Point.map_some] at h2
        injection h2
      rw [map_sub, hx, (hIfix τ hτ).1]

    have h2vne : A.valuation ((2:ℕ) : AlgebraicClosure ℚ) ≠ 0 := by simp
    have ht0 : x - x₀ ≠ 0 := by
      intro h0
      rw [h0, _root_.map_zero, zero_pow P.pp.ne_zero] at hvt
      exact pow_ne_zero _ h2vne hvt.symm

    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq
      ((x - x₀) ^ P.p / ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j))
      P.hppos
    have h2M0 : ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j) ≠ 0 := by
      apply pow_ne_zero
      norm_num
    have hu0 : (x - x₀) ^ P.p
        / ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ ht0) h2M0
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, zero_pow P.pp.ne_zero] at hw
      exact hu0 hw.symm
    have hvw : A.valuation w = 1 := by
      refine pow_left_injective (M := A.ValueGroup) P.pp.ne_zero ?_
      show A.valuation w ^ P.p = 1 ^ P.p
      rw [← map_pow, hw, one_pow, map_div₀, map_pow, map_pow, hvt]
      exact div_self (pow_ne_zero _ h2vne)

    have hwfix : ∀ τ ∈ A.inertiaSubgroupIn ℚ, τ w = w := by
      intro τ hτ
      have hτu : τ ((x - x₀) ^ P.p
            / ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j))
          = (x - x₀) ^ P.p
            / ((2:ℕ) : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j) := by
        rw [map_div₀, map_pow, map_pow, hfixt τ hτ, map_natCast]
      have hζpow : (τ w / w) ^ P.p = 1 := by
        rw [div_pow, ← map_pow, hw, hτu]
        exact div_self hu0
      have hwA : w ∈ A := (A.valuation_le_one_iff w).mp hvw.le
      obtain ⟨-, hlt⟩ :=
        ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hτ hwA
      by_contra hne
      have hζne1 : τ w / w ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq hw0).mp h1)
      have hv1 : A.valuation (τ w / w - 1) = 1 :=
        FW2Aux.valuation_sub_one_eq_one hv2 P.pp hp2 hζpow hζne1
      have hfac : τ w - w = (τ w / w - 1) * w := by
        field_simp
      rw [hfac, map_mul, hv1, hvw, mul_one] at hlt
      exact lt_irrefl _ hlt

    have hspow : ((x - x₀) / w) ^ P.p
        = (2 : AlgebraicClosure ℚ) ^ (padicValInt 2 P.freyCurveInt.Δ * j) := by
      rw [div_pow, hw, div_div_eq_mul_div, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero _ ht0), mul_one, hcast]
    obtain ⟨τ, hτ, hτs⟩ :=
      FW2Aux.exists_inertia_ne_of_pow_eq A hA P.pp hp2 hpm hspow
    apply hτs
    rw [map_div₀, hfixt τ hτ, hwfix τ hτ]

end
p2m_reactivate "P2MW.S_FreyPackage_frey_exists_inertia_not_fixed_at_two.FW2Aux"

end S_FreyPackage_frey_exists_inertia_not_fixed_at_two
end P2MW
export P2MW.S_FreyPackage_frey_exists_inertia_not_fixed_at_two (solution)
