-- Prove2me | solution 1 for CuspForm.exists_isNewform_of_point_of_up_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a2256145-28f2-5cc2-b6b8-12d4e8224d66

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_exists_isNewform_descent
import Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNewform_of_point_of_up_dvd
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000

open ModularFormClass

namespace NewformOfPointDvd

private theorem exists_subring_ringHom_extend {L R : Type} [Field L] [CommRing R] [IsDomain R]
    (A : Subring L) (φ : A →+* R) (a₀ : A) (ha₀ : φ a₀ ≠ 0) :
    ∃ (B : Subring L) (ψ : B →+* R),
      ∀ (x : L) (n : ℕ) (y : A) (q : R), (a₀ : L) ^ n * x = y → φ y = φ a₀ ^ n * q →
        ∃ hx : x ∈ B, ψ ⟨x, hx⟩ = q := by
  classical
  let P : L → ℕ → A → R → Prop := fun x n y q => (a₀ : L) ^ n * x = y ∧ φ y = φ a₀ ^ n * q

  have uniq : ∀ (x : L) (n m : ℕ) (y z : A) (q r : R), P x n y q → P x m z r → q = r := by
    intro x n m y z q r ⟨h1, h2⟩ ⟨h3, h4⟩
    have hA : a₀ ^ m * y = a₀ ^ n * z := by
      apply Subtype.ext
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
      rw [← h1, ← h3]; ring
    have := congrArg φ hA
    rw [map_mul, map_mul, map_pow, map_pow, h2, h4] at this
    have hne : (φ a₀) ^ (n + m) ≠ 0 := pow_ne_zero _ ha₀
    apply mul_left_cancel₀ hne
    calc φ a₀ ^ (n + m) * q = φ a₀ ^ m * (φ a₀ ^ n * q) := by ring
      _ = φ a₀ ^ n * (φ a₀ ^ m * r) := this
      _ = φ a₀ ^ (n + m) * r := by ring

  have Pone : P 1 0 1 1 := ⟨by simp, by simp⟩
  have Pzero : P 0 0 0 0 := ⟨by simp, by simp⟩
  have Pmul : ∀ {x₁ x₂ : L} {n₁ n₂ : ℕ} {y₁ y₂ : A} {q₁ q₂ : R},
      P x₁ n₁ y₁ q₁ → P x₂ n₂ y₂ q₂ → P (x₁ * x₂) (n₁ + n₂) (y₁ * y₂) (q₁ * q₂) := by
    intro x₁ x₂ n₁ n₂ y₁ y₂ q₁ q₂ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Subring.coe_mul, ← h1, ← h3]; ring
    · rw [map_mul, h2, h4, pow_add]; ring
  have Padd : ∀ {x₁ x₂ : L} {n₁ n₂ : ℕ} {y₁ y₂ : A} {q₁ q₂ : R},
      P x₁ n₁ y₁ q₁ → P x₂ n₂ y₂ q₂ →
        P (x₁ + x₂) (n₁ + n₂) (a₀ ^ n₂ * y₁ + a₀ ^ n₁ * y₂) (q₁ + q₂) := by
    intro x₁ x₂ n₁ n₂ y₁ y₂ q₁ q₂ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow]
      rw [← h1, ← h3]; ring
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, h2, h4]; ring
  have Pneg : ∀ {x : L} {n : ℕ} {y : A} {q : R}, P x n y q → P (-x) n (-y) (-q) := by
    intro x n y q ⟨h1, h2⟩
    exact ⟨by rw [Subring.coe_neg, ← h1]; ring, by rw [map_neg, h2]; ring⟩

  let B : Subring L :=
    { carrier := {x | ∃ (n : ℕ) (y : A) (q : R), P x n y q}
      mul_mem' := by
        rintro x₁ x₂ ⟨n₁, y₁, q₁, h₁⟩ ⟨n₂, y₂, q₂, h₂⟩
        exact ⟨_, _, _, Pmul h₁ h₂⟩
      one_mem' := ⟨0, 1, 1, Pone⟩
      add_mem' := by
        rintro x₁ x₂ ⟨n₁, y₁, q₁, h₁⟩ ⟨n₂, y₂, q₂, h₂⟩
        exact ⟨_, _, _, Padd h₁ h₂⟩
      zero_mem' := ⟨0, 0, 0, Pzero⟩
      neg_mem' := by
        rintro x ⟨n, y, q, h⟩
        exact ⟨_, _, _, Pneg h⟩ }
  have hB : ∀ x : B, ∃ (n : ℕ) (y : A) (q : R), P x n y q := fun x => x.2

  let v : B → R := fun x => (hB x).choose_spec.choose_spec.choose
  have hv : ∀ x : B, P x (hB x).choose (hB x).choose_spec.choose (v x) :=
    fun x => (hB x).choose_spec.choose_spec.choose_spec
  have v_eq : ∀ (x : B) (n : ℕ) (y : A) (q : R), P x n y q → v x = q :=
    fun x n y q h => uniq x _ _ _ _ _ _ (hv x) h
  let ψ : B →+* R :=
    { toFun := v
      map_one' := v_eq 1 0 1 1 Pone
      map_mul' := fun x₁ x₂ => v_eq (x₁ * x₂) _ _ _ (Pmul (hv x₁) (hv x₂))
      map_zero' := v_eq 0 0 0 0 Pzero
      map_add' := fun x₁ x₂ => v_eq (x₁ + x₂) _ _ _ (Padd (hv x₁) (hv x₂)) }
  refine ⟨B, ψ, fun x n y q h1 h2 => ?_⟩
  have hx : x ∈ B := ⟨n, y, q, h1, h2⟩
  exact ⟨hx, v_eq ⟨x, hx⟩ n y q ⟨h1, h2⟩⟩

end NewformOfPointDvd

open NewformOfPointDvd in

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [CharZero 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hpN : p ∣ N) (up : 𝒪')
    (hup : ∃ χ' : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p}) →+* 𝒪',
      (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset) t) = χ t) ∧
      χ' (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN (by simp)) = up)
    (hdvd : up ∣ (p : 𝒪')) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (hMgN : Mg ∣ N)
      (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (_ : g.IsNewform)
      (chig : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →+* ℂ)
      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) = ModularFormClass.qCoeff g ℓ)
      (_ : ∀ (hpMg : p ∣ Mg),
        chig (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpMg (by simp)) =
          ModularFormClass.qCoeff g p)
      (iota : chig.range →+* 𝒪'),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
          (fun h => hℓN (h.trans hMgN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
          χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ((∃ hpMg : ¬ p ∣ Mg,
          up * up - iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpMg (by simp))) * up + (p : 𝒪') = 0) ∨
       (∃ hpMg : p ∣ Mg, ¬ p ^ 2 ∣ Mg ∧
          iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpMg (by simp))) = up)) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨χ', hχ'χ, hχ'U⟩ := hup
  obtain ⟨β, hβ⟩ := hdvd
  have hp0 : (p : 𝒪') ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hup0 : up ≠ 0 := fun h => hp0 (by rw [hβ, h, zero_mul])
  have hpS' : p ∉ ((↑S : Set ℕ) \ {p}) := fun h => h.2 rfl

  set 𝔭 : Ideal (CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p})) := RingHom.ker χ' with h𝔭def
  have h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime χ'
  obtain ⟨f, hf, hann⟩ := CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime _ 𝔭 h𝔭

  obtain ⟨χf, hχf, hχfT, hχfU⟩ := hf.exists_ringHom_heckeAlgebra ((↑S : Set ℕ) \ {p})
  have hker : ∀ t, χf t = 0 → χ' t = 0 := by
    intro t ht
    have h := hχf t
    rw [ht, zero_smul] at h
    exact hann t h
  have hsurj : Function.Surjective χf.rangeRestrict := RingHom.rangeRestrict_surjective χf
  let ι₀ : χf.range →+* 𝒪' :=
    (RingHom.liftOfRightInverse χf.rangeRestrict (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
      ⟨χ', fun t ht => by
        rw [RingHom.mem_ker] at ht ⊢
        exact hker t (congrArg Subtype.val ht)⟩
  have hι₀ : ∀ t, ι₀ (χf.rangeRestrict t) = χ' t := fun t =>
    RingHom.liftOfRightInverse_comp_apply χf.rangeRestrict _ _ _ t

  set α : ℂ := qCoeff f p with hαdef
  have hχfUp : χf (CuspForm.heckeAlgebra.U hp hpN hpS') = α := hχfU p hp hpN hpS'
  have hι₀α : ι₀ (χf.rangeRestrict (CuspForm.heckeAlgebra.U hp hpN hpS')) = up := by rw [hι₀]; exact hχ'U
  have hα0 : α ≠ 0 := by
    intro h0
    apply hup0
    rw [← hχ'U]
    exact hker _ (hχfUp.trans h0)

  have hA : ∀ k : ℕ, qCoeff f (p ^ k) = α ^ k := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => simp [hf.qCoeff_one]
    | one => simp [hαdef]
    | more k ih0 ih1 =>
      rw [hf.qCoeff_prime_pow_of_dvd p k hp hpN, ih1, pow_succ, pow_succ, pow_succ]; ring

  obtain ⟨Mg, hMgN, g, hg, hdesc⟩ := CuspForm.exists_isNewform_descent f hf
  haveI : NeZero Mg := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hMgN⟩
  obtain ⟨chig, -, hchigT, hchigU⟩ := hg.isNormalizedEigenform.exists_ringHom_heckeAlgebra ((↑S : Set ℕ) \ {p})

  obtain ⟨c, hc⟩ := CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching Mg N hMgN g hg f hf
    (fun ℓ hℓ hℓN => hdesc ℓ hℓ hℓN)
  set a : ℂ := qCoeff g p with hadef

  have hNM0 : N / Mg ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hMgN).mpr ⟨NeZero.ne N, NeZero.ne Mg⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, N / Mg < p ^ (k₀ + 1) :=
    ⟨N / Mg, (Nat.lt_pow_self hp.one_lt).trans_le (Nat.pow_le_pow_right hp.pos (Nat.le_succ _))⟩
  have hdiv_pow : ∀ (d : ℕ), d ∈ (N / Mg).divisors → ∀ m : ℕ, k₀ < m → ¬ d ∣ p ^ k₀ → ¬ d ∣ p ^ m := by
    intro d hd m hm hdk hdm
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdm
    have hjk : k₀ < j := by
      by_contra hle
      exact hdk (pow_dvd_pow p (not_lt.mp hle))
    have h1 : p ^ j ≤ N / Mg := Nat.divisor_le hd
    have h2 : p ^ (k₀ + 1) ≤ p ^ j := Nat.pow_le_pow_right hp.pos hjk
    omega

  obtain ⟨B, ψ, hBψ⟩ := exists_subring_ringHom_extend χf.range ι₀
    (χf.rangeRestrict (CuspForm.heckeAlgebra.U hp hpN hpS')) (by rw [hι₀α]; exact hup0)
  have hcoeU : ((χf.rangeRestrict (CuspForm.heckeAlgebra.U hp hpN hpS') : χf.range) : ℂ) = α := hχfUp

  have hvalT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (hℓMg : ¬ ℓ ∣ Mg)
      (hℓS' : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      ∃ hx : chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS') ∈ B,
        ψ ⟨_, hx⟩ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) := by
    intro ℓ hℓ hℓS hℓN hℓMg hℓS'
    refine hBψ _ 0 (χf.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS')) _ ?_ ?_
    · rw [pow_zero, one_mul, hchigT ℓ hℓ hℓMg hℓS', RingHom.coe_rangeRestrict, hχfT ℓ hℓ hℓN hℓS',
        hdesc ℓ hℓ hℓN]
    · rw [pow_zero, one_mul, hι₀, ← hχ'χ]
      rfl
  by_cases hpMg : p ∣ Mg
  ·
    have hb : ∀ m : ℕ, qCoeff g (p ^ (m + 1)) = a * qCoeff g (p ^ m) := by
      intro m
      cases m with
      | zero => simp [hadef, hg.isNormalizedEigenform.qCoeff_one]
      | succ m => exact hg.isNormalizedEigenform.qCoeff_prime_pow_of_dvd p m hp hpMg
    have key : qCoeff f (p ^ (k₀ + 1)) = a * qCoeff f (p ^ k₀) := by
      rw [hc, hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      by_cases hdk : d ∣ p ^ k₀
      · obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdk
        rw [if_pos (pow_dvd_pow p (by omega)), if_pos (pow_dvd_pow p hj),
          Nat.pow_div (by omega) hp.pos, Nat.pow_div hj hp.pos,
          show k₀ + 1 - j = (k₀ - j) + 1 by omega, hb]
        ring
      · rw [if_neg (hdiv_pow d hd (k₀ + 1) (by omega) hdk), if_neg hdk]
        ring
    have hαa : α = a := by
      rw [hA, hA, pow_succ, mul_comm a] at key
      exact mul_left_cancel₀ (pow_ne_zero k₀ hα0) key
    have hp2 : ¬ p ^ 2 ∣ Mg := fun h2 =>
      hα0 (hαa.trans (CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg p hp h2))

    have hvalU : ∀ (hq : p.Prime) (hqMg : p ∣ Mg) (hqS' : p ∉ ((↑S : Set ℕ) \ {p})),
        ∃ hx : chig (CuspForm.heckeAlgebra.U hq hqMg hqS') ∈ B, ψ ⟨_, hx⟩ = up := by
      intro hq hqMg hqS'
      refine hBψ _ 0 (χf.rangeRestrict (CuspForm.heckeAlgebra.U hp hpN hpS')) _ ?_ ?_
      · rw [pow_zero, one_mul, hchigU p hq hqMg hqS', hcoeU, hαa]
      · rw [pow_zero, one_mul, hι₀α]
    have hgenT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS' : ℓ ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS') ∈ B := by
      intro ℓ hℓ hℓMg hℓS'
      have hℓp : ℓ ≠ p := fun h => hℓMg (h ▸ hpMg)
      have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS' ⟨h, hℓp⟩
      exact (hvalT ℓ hℓ hℓS (fun h => hℓS (hNS ℓ hℓ h)) hℓMg hℓS').1
    have hgenU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg) (hqS' : q ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.U hq hqMg hqS') ∈ B := by
      intro q hq hqMg hqS'
      have hqS : q ∈ (↑S : Set ℕ) := hNS q hq (hqMg.trans hMgN)
      have hqp : q = p := by
        by_contra h
        exact hqS' ⟨hqS, h⟩
      subst hqp
      exact (hvalU hq hqMg hqS').1

    have htop : Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
          CuspForm.heckeGenerators Mg 2 ((↑S : Set ℕ) \ {p})) = ⊤ := by
      apply Subalgebra.map_injective (f := (CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p})).val)
        Subtype.val_injective
      rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, Subalgebra.coe_val,
        Set.image_preimage_eq_of_subset]
      · rfl
      · rw [Subtype.range_coe]
        exact Algebra.subset_adjoin
    have hmem' : ∀ t : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}), chig t ∈ B := by
      intro t
      have ht : t ∈ Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
            CuspForm.heckeGenerators Mg 2 ((↑S : Set ℕ) \ {p})) := by
        rw [htop]; exact Algebra.mem_top
      induction ht using Algebra.adjoin_induction with
      | mem t ht =>
        rcases ht with ⟨ℓ, hℓ, hℓMg, hℓS', ht⟩ | ⟨q, hqMg, hq, hqS', ht⟩
        · have : t = CuspForm.heckeAlgebra.T hℓ hℓMg hℓS' := Subtype.ext ht
          rw [this]; exact hgenT ℓ hℓ hℓMg hℓS'
        · have : t = CuspForm.heckeAlgebra.U hq hqMg hqS' := Subtype.ext ht
          rw [this]; exact hgenU q hq hqMg hqS'
      | algebraMap r =>
        rw [eq_intCast, map_intCast chig]
        exact intCast_mem B r
      | add x y _ _ ihx ihy =>
        rw [chig.map_add]
        exact add_mem ihx ihy
      | mul x y _ _ ihx ihy =>
        rw [chig.map_mul]
        exact mul_mem ihx ihy

    let Θ : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →+* 𝒪' := ψ.comp (chig.codRestrict B hmem')
    have hΘ : ∀ t, Θ t = ψ ⟨chig t, hmem' t⟩ := fun t => rfl
    have hsurjg : Function.Surjective chig.rangeRestrict := RingHom.rangeRestrict_surjective chig
    let ι : chig.range →+* 𝒪' :=
      (RingHom.liftOfRightInverse chig.rangeRestrict (Function.surjInv hsurjg)
        (Function.rightInverse_surjInv hsurjg))
        ⟨Θ, fun t ht => by
          rw [RingHom.mem_ker] at ht ⊢
          have h0 : chig t = 0 := congrArg Subtype.val ht
          rw [hΘ]
          have : (⟨chig t, hmem' t⟩ : B) = 0 := Subtype.ext h0
          rw [this, map_zero]⟩
    have hι : ∀ t, ι (chig.rangeRestrict t) = ψ ⟨chig t, hmem' t⟩ := fun t =>
      RingHom.liftOfRightInverse_comp_apply chig.rangeRestrict _ _ _ t
    refine ⟨Mg, inferInstance, hMgN, g, hg, chig, hchigT, fun hpMg' => hchigU p _ hpMg' _, ι, ?_,
      Or.inr ⟨hpMg, hp2, ?_⟩⟩
    · intro ℓ hℓ hℓN hℓS
      rw [hι]
      exact (hvalT ℓ hℓ hℓS hℓN _ _).2
    · rw [hι]
      exact (hvalU _ hpMg _).2
  ·
    have hb2 : ∀ m : ℕ, qCoeff g (p ^ (m + 2)) = a * qCoeff g (p ^ (m + 1)) - p * qCoeff g (p ^ m) :=
      fun m => hg.isNormalizedEigenform.qCoeff_prime_pow_of_not_dvd p m hp hpMg
    have key : qCoeff f (p ^ (k₀ + 2)) - a * qCoeff f (p ^ (k₀ + 1)) + p * qCoeff f (p ^ k₀) = 0 := by
      rw [hc (p ^ (k₀ + 2)), hc (p ^ (k₀ + 1)), hc (p ^ k₀), Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun d hd => ?_
      by_cases hdk : d ∣ p ^ k₀
      · obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdk
        rw [if_pos (pow_dvd_pow p (by omega)), if_pos (pow_dvd_pow p (by omega)), if_pos (pow_dvd_pow p hj),
          Nat.pow_div (by omega) hp.pos, Nat.pow_div (by omega) hp.pos, Nat.pow_div hj hp.pos,
          show k₀ + 2 - j = (k₀ - j) + 2 by omega, show k₀ + 1 - j = (k₀ - j) + 1 by omega, hb2]
        ring
      · rw [if_neg (hdiv_pow d hd (k₀ + 2) (by omega) hdk), if_neg (hdiv_pow d hd (k₀ + 1) (by omega) hdk),
          if_neg hdk]
        ring
    have hquad : α * α - a * α + p = 0 := by
      rw [hA, hA, hA] at key
      have : α ^ k₀ * (α * α - a * α + p) = 0 := by rw [← key]; ring
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero k₀ hα0)

    have hvalTp : ∀ (hq : p.Prime) (hqMg : ¬ p ∣ Mg) (hqS' : p ∉ ((↑S : Set ℕ) \ {p})),
        ∃ hx : chig (CuspForm.heckeAlgebra.T hq hqMg hqS') ∈ B, ψ ⟨_, hx⟩ = up + β := by
      intro hq hqMg hqS'
      refine hBψ _ 1 (χf.rangeRestrict (CuspForm.heckeAlgebra.U hp hpN hpS' * CuspForm.heckeAlgebra.U hp hpN hpS'
          + (p : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p})))) _ ?_ ?_
      · rw [pow_one, hcoeU, hchigT p hq hqMg hqS', ← hadef, RingHom.coe_rangeRestrict, map_add, map_mul,
          map_natCast, hχfUp]
        linear_combination -hquad
      · rw [pow_one, hι₀α, hι₀, map_add, map_mul, map_natCast, hχ'U, hβ]
        ring
    have hgenT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS' : ℓ ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS') ∈ B := by
      intro ℓ hℓ hℓMg hℓS'
      by_cases hℓp : ℓ = p
      · subst hℓp
        exact (hvalTp hℓ hℓMg hℓS').1
      · have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS' ⟨h, hℓp⟩
        exact (hvalT ℓ hℓ hℓS (fun h => hℓS (hNS ℓ hℓ h)) hℓMg hℓS').1
    have hgenU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg) (hqS' : q ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.U hq hqMg hqS') ∈ B := by
      intro q hq hqMg hqS'
      have hqS : q ∈ (↑S : Set ℕ) := hNS q hq (hqMg.trans hMgN)
      have hqp : q = p := by
        by_contra h
        exact hqS' ⟨hqS, h⟩
      subst hqp
      exact absurd hqMg hpMg

    have htop : Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
          CuspForm.heckeGenerators Mg 2 ((↑S : Set ℕ) \ {p})) = ⊤ := by
      apply Subalgebra.map_injective (f := (CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p})).val)
        Subtype.val_injective
      rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, Subalgebra.coe_val,
        Set.image_preimage_eq_of_subset]
      · rfl
      · rw [Subtype.range_coe]
        exact Algebra.subset_adjoin
    have hmem' : ∀ t : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}), chig t ∈ B := by
      intro t
      have ht : t ∈ Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
            CuspForm.heckeGenerators Mg 2 ((↑S : Set ℕ) \ {p})) := by
        rw [htop]; exact Algebra.mem_top
      induction ht using Algebra.adjoin_induction with
      | mem t ht =>
        rcases ht with ⟨ℓ, hℓ, hℓMg, hℓS', ht⟩ | ⟨q, hqMg, hq, hqS', ht⟩
        · have : t = CuspForm.heckeAlgebra.T hℓ hℓMg hℓS' := Subtype.ext ht
          rw [this]; exact hgenT ℓ hℓ hℓMg hℓS'
        · have : t = CuspForm.heckeAlgebra.U hq hqMg hqS' := Subtype.ext ht
          rw [this]; exact hgenU q hq hqMg hqS'
      | algebraMap r =>
        rw [eq_intCast, map_intCast chig]
        exact intCast_mem B r
      | add x y _ _ ihx ihy =>
        rw [chig.map_add]
        exact add_mem ihx ihy
      | mul x y _ _ ihx ihy =>
        rw [chig.map_mul]
        exact mul_mem ihx ihy

    let Θ : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →+* 𝒪' := ψ.comp (chig.codRestrict B hmem')
    have hΘ : ∀ t, Θ t = ψ ⟨chig t, hmem' t⟩ := fun t => rfl
    have hsurjg : Function.Surjective chig.rangeRestrict := RingHom.rangeRestrict_surjective chig
    let ι : chig.range →+* 𝒪' :=
      (RingHom.liftOfRightInverse chig.rangeRestrict (Function.surjInv hsurjg)
        (Function.rightInverse_surjInv hsurjg))
        ⟨Θ, fun t ht => by
          rw [RingHom.mem_ker] at ht ⊢
          have h0 : chig t = 0 := congrArg Subtype.val ht
          rw [hΘ]
          have : (⟨chig t, hmem' t⟩ : B) = 0 := Subtype.ext h0
          rw [this, map_zero]⟩
    have hι : ∀ t, ι (chig.rangeRestrict t) = ψ ⟨chig t, hmem' t⟩ := fun t =>
      RingHom.liftOfRightInverse_comp_apply chig.rangeRestrict _ _ _ t
    refine ⟨Mg, inferInstance, hMgN, g, hg, chig, hchigT, fun hpMg' => absurd hpMg' hpMg, ι, ?_,
      Or.inl ⟨hpMg, ?_⟩⟩
    · intro ℓ hℓ hℓN hℓS
      rw [hι]
      exact (hvalT ℓ hℓ hℓS hℓN _ _).2
    · rw [hι, (hvalTp _ hpMg _).2, hβ]
      ring

end S_CuspForm_exists_isNewform_of_point_of_up_dvd
end P2MW
export P2MW.S_CuspForm_exists_isNewform_of_point_of_up_dvd (solution)
