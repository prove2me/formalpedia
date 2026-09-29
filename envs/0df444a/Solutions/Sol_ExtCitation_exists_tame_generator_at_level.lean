-- Prove2me | solution 1 for ExtCitation.exists_tame_generator_at_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9280ecd6-e26c-5efb-a952-fed34809f9bd

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
import Theorems.Thm_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer
import Theorems.Thm_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_exists_tame_generator_at_level

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open ExtCitation
open scoped NumberField Pointwise

namespace GaloisRep
namespace SecB

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem valuation_apply_lt_one_iff (A : ValuationSubring (AlgebraicClosure ℚ)) {σ : Γℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (x : AlgebraicClosure ℚ) :
    A.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  have hA : σ • A = A := hσ
  have hmem : ∀ y : AlgebraicClosure ℚ, y ∈ A ↔ σ y ∈ A := by
    intro y
    constructor
    · intro hy
      have h := ValuationSubring.smul_mem_pointwise_smul σ y A hy
      rwa [hA] at h
    · intro hy
      rw [← hA] at hy
      obtain ⟨s, hs, hsx⟩ := (ValuationSubring.mem_smul_pointwise_iff_exists σ _ A).mp hy
      have : s = y := σ.injective hsx
      exact this ▸ hs
  by_cases hx : x = 0
  · subst hx; simp
  have hσx : σ x ≠ 0 := by simpa using hx

  have key : ∀ y : AlgebraicClosure ℚ, y ≠ 0 → (A.valuation y < 1 ↔ y⁻¹ ∉ A) := by
    intro y hy
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hy))]
  rw [key _ hσx, key _ hx, ← map_inv₀, not_iff_not]
  exact (hmem x⁻¹).symm

theorem smul_mem_sq_of_forall_smul_mem {B : Type*} [CommRing B] {G : Type*} [Group G] [MulSemiringAction G B]
    (𝔓 : Ideal B) {φ : G} (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) {z : B} (hz : z ∈ 𝔓 ^ 2) : φ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B φ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hφP x hx
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

end GaloisRep.SecB

open GaloisRep.SecB in
theorem GaloisRep.SecB.quotient_form
    (q : Nat.Primes) (φ : primeLocalGaloisGroup q)
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    [((F.fixingSubgroup).comap (primeLocalToGlobal q)).Normal] :
    ∃ (t : primeLocalGaloisGroup q)
      (_ : t ∈ (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)))
      (W : Subgroup (primeLocalGaloisGroup q ⧸ ((F.fixingSubgroup).comap (primeLocalToGlobal q)))),
      W.Normal ∧ IsPGroup q W ∧
      W ≤ (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).map
            (QuotientGroup.mk' ((F.fixingSubgroup).comap (primeLocalToGlobal q))) ∧
      (((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)).map
            (QuotientGroup.mk' ((F.fixingSubgroup).comap (primeLocalToGlobal q)))
        = W ⊔ Subgroup.zpowers (QuotientGroup.mk t) ∧
      (QuotientGroup.mk φ : _ ⧸ (F.fixingSubgroup).comap (primeLocalToGlobal q)) * QuotientGroup.mk t *
          (QuotientGroup.mk φ)⁻¹ * ((QuotientGroup.mk t) ^ (q : ℕ))⁻¹ ∈ W := by
  classical
  haveI hqF : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  set r : primeLocalGaloisGroup q →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := primeLocalToGlobal q with hr
  set P : ValuationSubring (AlgebraicClosure ℚ) := primeLocalPlace q with hPdef
  set U : Subgroup (primeLocalGaloisGroup q) := (F.fixingSubgroup).comap r with hU
  set I : Subgroup (primeLocalGaloisGroup q) := (P.inertiaSubgroupIn ℚ).comap r with hI
  set res : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (F ≃ₐ[ℚ] F) := AlgEquiv.restrictNormalHom F with hres
  have hPq : P.LiesOverPrime q := liesOverPrime_primeLocalPlace q
  have hdec : ∀ g : primeLocalGaloisGroup q, r g ∈ P.decompositionSubgroup ℚ := fun g =>
    localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g
  have hresapp : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F),
      (algebraMap F (AlgebraicClosure ℚ)) (res σ x) = σ (algebraMap F (AlgebraicClosure ℚ) x) :=
    fun σ x => AlgEquiv.restrictNormal_commutes σ F x

  obtain ⟨Q, hQmax, hQfin, hqQ, hint, hQmem, hD1, hwild, ϖ, hϖQ, hgen, hreg⟩ :=
    ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom F P q.2 hPq
  haveI := hQmax
  haveI := hQfin
  letI : Field (𝓞 F ⧸ Q) := Ideal.Quotient.field Q

  have hcoe : ∀ (τ : F ≃ₐ[ℚ] F) (y : 𝓞 F),
      (algebraMap F (AlgebraicClosure ℚ)) ((τ • y : 𝓞 F) : F) = (algebraMap F (AlgebraicClosure ℚ)) (τ (y : F)) :=
    fun τ y => rfl

  have hstab : ∀ g : primeLocalGaloisGroup q, ∀ z ∈ Q, res (r g) • z ∈ Q := by
    intro g z hz
    rw [hQmem] at hz ⊢
    rw [hcoe, hresapp]
    exact (valuation_apply_lt_one_iff P (hdec g) _).mpr hz

  have hUker : ∀ g : primeLocalGaloisGroup q, g ∈ U ↔ res (r g) = 1 := by
    intro g
    rw [hU, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      refine AlgEquiv.ext fun x => ?_
      apply (algebraMap F (AlgebraicClosure ℚ)).injective
      rw [hresapp, AlgEquiv.one_apply]
      exact h x x.2
    · intro h x hx
      have := hresapp (r g) ⟨x, hx⟩
      rw [h, AlgEquiv.one_apply] at this
      exact this.symm
  have hle : U ≤ (res.comp r).ker := fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply]; exact (hUker g).mp hg
  set ι : primeLocalGaloisGroup q ⧸ U →* (F ≃ₐ[ℚ] F) := QuotientGroup.lift U (res.comp r) hle with hι
  have hιmk : ∀ g : primeLocalGaloisGroup q, ι (QuotientGroup.mk g) = res (r g) := fun g =>
    QuotientGroup.lift_mk U hle g
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, hι, QuotientGroup.ker_lift, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (hUker g).mpr hg

  set S : Subgroup (primeLocalGaloisGroup q ⧸ U) := I.map (QuotientGroup.mk' U) with hS
  have hιS : ∀ s : primeLocalGaloisGroup q ⧸ U, s ∈ S → ι s ∈ Q.inertia (F ≃ₐ[ℚ] F) := by
    intro s hs
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
    rw [QuotientGroup.mk'_apply, hιmk, ← hD1]
    exact Subgroup.mem_map_of_mem _ hg

  have hN : (P.inertiaSubgroup ℚ).Normal := by
    unfold ValuationSubring.inertiaSubgroup; infer_instance
  have hIconj : ∀ (g i : primeLocalGaloisGroup q), i ∈ I → g * i * g⁻¹ ∈ I := by
    intro g i hi
    rw [hI, Subgroup.mem_comap] at hi ⊢
    obtain ⟨d, hd, hdi⟩ := Subgroup.mem_map.mp hi
    simp only [map_mul, map_inv]
    have hconj : (⟨r g, hdec g⟩ * d * ⟨r g, hdec g⟩⁻¹ : P.decompositionSubgroup ℚ) ∈ P.inertiaSubgroup ℚ :=
      hN.conj_mem d hd ⟨r g, hdec g⟩
    refine Subgroup.mem_map.mpr ⟨_, hconj, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv] at hdi ⊢
    rw [hdi]
  have hSconj : ∀ (x s : primeLocalGaloisGroup q ⧸ U), s ∈ S → x * s * x⁻¹ ∈ S := by
    intro x s hs
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.mp hs
    refine Subgroup.mem_map.mpr ⟨g * i * g⁻¹, hIconj g i hi, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

  obtain ⟨θ, hθchar, hθker, hθcyc⟩ := Ideal.exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer (G := F ≃ₐ[ℚ] F) Q hϖQ hgen hreg
  let Θ : S →* (𝓞 F ⧸ Q)ˣ :=
    { toFun := fun s => θ ⟨ι s, hιS s s.2⟩
      map_one' := by
        have : (⟨ι (1 : S), hιS _ (1 : S).2⟩ : Q.inertia (F ≃ₐ[ℚ] F)) = 1 := Subtype.ext (by simp)
        rw [this, map_one]
      map_mul' := fun s s' => by
        have : (⟨ι (s * s' : S), hιS _ (s * s').2⟩ : Q.inertia (F ≃ₐ[ℚ] F))
            = ⟨ι s, hιS s s.2⟩ * ⟨ι s', hιS s' s'.2⟩ := Subtype.ext (by simp)
        rw [this, map_mul] }
  have hΘ : ∀ s : S, Θ s = θ ⟨ι s, hιS s s.2⟩ := fun s => rfl
  set W : Subgroup (primeLocalGaloisGroup q ⧸ U) := Θ.ker.map S.subtype with hW
  have hWle : W ≤ S := by
    rintro _ ⟨w, -, rfl⟩; exact w.2
  have hmemW : ∀ (s : primeLocalGaloisGroup q ⧸ U) (hs : s ∈ S), s ∈ W ↔ Θ ⟨s, hs⟩ = 1 := by
    intro s hs
    constructor
    · rintro ⟨w, hw, hws⟩
      have : w = ⟨s, hs⟩ := Subtype.ext hws
      rw [← this]; exact hw
    · intro h; exact ⟨⟨s, hs⟩, h, rfl⟩

  have hWp : IsPGroup q W := by
    intro w
    obtain ⟨s, hs1, hsw⟩ := w.2
    have hs1' : θ ⟨ι s, hιS s s.2⟩ = 1 := hs1
    rw [hθker] at hs1'
    obtain ⟨a, ha⟩ := hwild (ι s) (hιS s s.2) hs1'
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hsw, Subgroup.coe_subtype, ← ha, orderOf_injective ι hιinj]
    exact pow_orderOf_eq_one _

  have hWnormal : W.Normal := by
    refine ⟨fun w hw x => ?_⟩
    have hwS : w ∈ S := hWle hw
    have hcS : x * w * x⁻¹ ∈ S := hSconj x w hwS
    rw [hmemW _ hcS, hΘ, hθker]
    rw [hmemW _ hwS, hΘ, hθker] at hw
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    intro y
    have e : ι (QuotientGroup.mk g * w * (QuotientGroup.mk g)⁻¹) = res (r g) * ι w * (res (r g))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιmk]
    have e2 : ((⟨ι (QuotientGroup.mk g * w * (QuotientGroup.mk g)⁻¹), hιS _ hcS⟩ : Q.inertia (F ≃ₐ[ℚ] F)) : F ≃ₐ[ℚ] F) • y - y
        = res (r g) • ((ι w) • ((res (r g))⁻¹ • y) - (res (r g))⁻¹ • y) := by
      change (ι (QuotientGroup.mk g * w * (QuotientGroup.mk g)⁻¹)) • y - y = _
      rw [e, smul_sub, mul_smul, mul_smul, smul_inv_smul]
    rw [e2]
    exact smul_mem_sq_of_forall_smul_mem Q (hstab g) (hw _)

  haveI : IsCyclic (𝓞 F ⧸ Q)ˣ := inferInstance
  haveI : IsCyclic Θ.range := Subgroup.isCyclic _
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Θ.range)
  obtain ⟨s₀, hs₀⟩ := g₀.2
  obtain ⟨t, htI, hts₀⟩ := Subgroup.mem_map.mp s₀.2
  rw [QuotientGroup.mk'_apply] at hts₀
  have hs₀t : (s₀ : primeLocalGaloisGroup q ⧸ U) = QuotientGroup.mk t := hts₀.symm
  refine ⟨t, htI, W, hWnormal, hWp, hWle, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro s hs
      have hmem : (⟨Θ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩⟩ : Θ.range) ∈ Subgroup.zpowers g₀ := hg₀ _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : Θ s₀ ^ k = Θ ⟨s, hs⟩ := by
        have := congrArg (fun z : Θ.range => (z : (𝓞 F ⧸ Q)ˣ)) hk
        simpa [hs₀] using this
      have hu : s * (QuotientGroup.mk t) ^ (-k) ∈ W := by
        have hmemS : s * (QuotientGroup.mk t) ^ (-k) ∈ S :=
          S.mul_mem hs (S.zpow_mem (hs₀t ▸ s₀.2) _)
        rw [hmemW _ hmemS]
        have : (⟨s * (QuotientGroup.mk t) ^ (-k), hmemS⟩ : S) = ⟨s, hs⟩ * s₀ ^ (-k) := by
          apply Subtype.ext; simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow, hs₀t]; rfl
        rw [this, map_mul, map_zpow, ← hk', ← zpow_add, add_neg_cancel, zpow_zero]
      have e : s = (s * (QuotientGroup.mk t) ^ (-k)) * (QuotientGroup.mk t) ^ k := by
        rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
      rw [e]
      exact Subgroup.mul_mem_sup hu (Subgroup.zpow_mem_zpowers _ _)
    · refine sup_le hWle ?_
      rw [Subgroup.zpowers_le, ← hs₀t]; exact s₀.2
  ·
    set x : primeLocalGaloisGroup q ⧸ U := QuotientGroup.mk φ with hx
    have htS : (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ U) ∈ S := hs₀t ▸ s₀.2
    have hcS : x * QuotientGroup.mk t * x⁻¹ ∈ S := hSconj x _ htS
    have hmemS : x * QuotientGroup.mk t * x⁻¹ * ((QuotientGroup.mk t) ^ (q : ℕ))⁻¹ ∈ S :=
      S.mul_mem hcS (S.inv_mem (S.pow_mem htS _))
    rw [hmemW _ hmemS]

    have key : Θ ⟨x * QuotientGroup.mk t * x⁻¹, hcS⟩ = Θ ⟨QuotientGroup.mk t, htS⟩ ^ (q : ℕ) := by
      rw [hΘ, hΘ]

      set σ' : Q.inertia (F ≃ₐ[ℚ] F) := ⟨ι (QuotientGroup.mk t), hιS _ htS⟩ with hσ'
      obtain ⟨tc, htc⟩ := Ideal.Quotient.mk_surjective (((θ σ' : (𝓞 F ⧸ Q)ˣ) : 𝓞 F ⧸ Q))
      have hcong : (σ' : F ≃ₐ[ℚ] F) • ϖ - ϖ * tc ∈ Q ^ 2 := (hθchar σ' tc).mp htc.symm

      have hφ1 : ∀ y : 𝓞 F, res (r φ) • y - y ^ (q : ℕ) ∈ Q := by
        intro y
        obtain ⟨hd, hfrob⟩ := hφ
        rw [hQmem]
        have hy : (algebraMap F (AlgebraicClosure ℚ)) (y : F) ∈ P := (P.valuation_le_one_iff _).mp (hint y)
        have h1 := hfrob (IsLocalRing.residue P ⟨_, hy⟩)
        have h2 : ((⟨r φ, hd⟩ : P.decompositionSubgroup ℚ) • IsLocalRing.residue P ⟨_, hy⟩ : IsLocalRing.ResidueField P)
            = IsLocalRing.residue P ((⟨r φ, hd⟩ : P.decompositionSubgroup ℚ) • ⟨_, hy⟩) := rfl
        rw [h2, ← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
        have h3 := (ValuationSubring.valuation_lt_one_iff P _).mp h1
        rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow] at h3
        have h3' : P.valuation ((r φ) ((algebraMap F (AlgebraicClosure ℚ)) (y : F))
            - ((algebraMap F (AlgebraicClosure ℚ)) (y : F)) ^ (q : ℕ)) < 1 := h3
        have e3 : ((res (r φ) • y - y ^ (q : ℕ) : 𝓞 F) : F) = ((res (r φ) • y : 𝓞 F) : F) - ((y : 𝓞 F) : F) ^ (q : ℕ) := by
          simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_sub, map_pow]
        rw [e3, map_sub, map_pow, hcoe, hresapp]
        exact h3'
      have hφQ : ∀ z ∈ Q, res (r φ) • z ∈ Q := hstab φ
      have hφQ' : ∀ z ∈ Q, (res (r φ))⁻¹ • z ∈ Q := by
        intro z hz; have := hstab φ⁻¹ z hz; rwa [map_inv, map_inv] at this
      have hTB := Ideal.conj_smul_sub_mul_pow_mem_sq_of_frobenius (G := F ≃ₐ[ℚ] F) Q hϖQ hgen σ'.2 hcong hφ1 hφQ hφQ'

      have e : ι (x * QuotientGroup.mk t * x⁻¹) = res (r φ) * (σ' : F ≃ₐ[ℚ] F) * (res (r φ))⁻¹ := by
        rw [map_mul, map_mul, map_inv, hx, hιmk]
      have h4 : θ ⟨ι (x * QuotientGroup.mk t * x⁻¹), hιS _ hcS⟩ = θ σ' ^ (q : ℕ) := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, ← htc, ← map_pow]
        apply (hθchar _ _).mpr
        change (ι (x * QuotientGroup.mk t * x⁻¹)) • ϖ - ϖ * tc ^ (q : ℕ) ∈ Q ^ 2
        rw [e]; exact hTB
      exact h4
    have e2 : (⟨x * QuotientGroup.mk t * x⁻¹ * ((QuotientGroup.mk t) ^ (q : ℕ))⁻¹, hmemS⟩ : S)
        = ⟨x * QuotientGroup.mk t * x⁻¹, hcS⟩ * (⟨QuotientGroup.mk t, htS⟩ ^ (q : ℕ))⁻¹ := by
      apply Subtype.ext; simp
    rw [e2, map_mul, map_inv, map_pow, key, mul_inv_cancel]

open GaloisRep.SecB in
theorem solution (q : Nat.Primes)
    (φ : primeLocalGaloisGroup q) (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F] :
    ∃ (t : primeLocalGaloisGroup q) (W : Subgroup (primeLocalGaloisGroup q)),
      t ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ∧
      (F.fixingSubgroup).comap (primeLocalToGlobal q) ≤ W ∧
      W ≤ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) ⊔ (F.fixingSubgroup).comap (primeLocalToGlobal q) ∧
      W.Normal ∧
      (∀ w ∈ W, ∃ a : ℕ, w ^ ((q : ℕ) ^ a) ∈ (F.fixingSubgroup).comap (primeLocalToGlobal q)) ∧
      (∀ i ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q), ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W) ∧
      (t ^ (q : ℕ))⁻¹ * (φ * t * φ⁻¹) ∈ W := by
  classical
  haveI hqF : Fact ((q : ℕ)).Prime := ⟨q.2⟩
  set U : Subgroup (primeLocalGaloisGroup q) := (F.fixingSubgroup).comap (primeLocalToGlobal q) with hU
  set I : Subgroup (primeLocalGaloisGroup q) := ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q) with hI
  haveI hUn : U.Normal := ExtCitation.levelSubgroup_normal q F
  haveI : U.FiniteIndex := ExtCitation.levelSubgroup_finiteIndex q F
  haveI : Finite (primeLocalGaloisGroup q ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨t, htI, W, hWn, hWp, hWle, hS, hrel⟩ := GaloisRep.SecB.quotient_form q φ hφ F
  set mk : primeLocalGaloisGroup q →* primeLocalGaloisGroup q ⧸ U := QuotientGroup.mk' U with hmk
  have hmk1 : ∀ g : primeLocalGaloisGroup q, mk g = 1 ↔ g ∈ U := fun g => by
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨t, W.comap mk, htI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    rw [Subgroup.mem_comap, (hmk1 g).mpr hg]; exact W.one_mem
  ·
    intro g hg
    rw [Subgroup.mem_comap] at hg
    obtain ⟨i, hi, hig⟩ := Subgroup.mem_map.mp (hWle hg)
    have hu : i⁻¹ * g ∈ U := by
      rw [← hmk1, map_mul, map_inv, hig, inv_mul_cancel]
    have : g = i * (i⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hi hu
  ·
    exact hWn.comap mk
  ·
    intro w hw
    rw [Subgroup.mem_comap] at hw
    obtain ⟨a, ha⟩ := hWp ⟨mk w, hw⟩
    refine ⟨a, ?_⟩
    rw [← hmk1, map_pow]
    exact congrArg Subtype.val ha
  ·
    intro i hi
    have hiS : mk i ∈ I.map mk := Subgroup.mem_map_of_mem _ hi
    rw [show I.map mk = W ⊔ Subgroup.zpowers (QuotientGroup.mk t) from hS] at hiS
    have hset : (mk i : primeLocalGaloisGroup q ⧸ U) ∈ ((W ⊔ Subgroup.zpowers (QuotientGroup.mk t) : Subgroup _) : Set _) := hiS
    rw [Subgroup.normal_mul] at hset
    obtain ⟨w, hw, z, hz, hwz⟩ := Set.mem_mul.mp hset
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz

    set n := orderOf (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ U) with hn
    have hn0 : 0 < n := orderOf_pos _
    set a : ℕ := (k % n).toNat with ha
    have hka : (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ U) ^ k = (QuotientGroup.mk t) ^ a := by
      rw [← zpow_natCast, ha, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn0.ne')), hn,
        zpow_mod_orderOf]
    refine ⟨a, ?_⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, map_pow]
    have hmkt : mk t = QuotientGroup.mk t := rfl
    rw [hmkt, ← hwz, hka]
    have : ((QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ U) ^ a)⁻¹ * (w * (QuotientGroup.mk t) ^ a)
        = ((QuotientGroup.mk t) ^ a)⁻¹ * w * ((QuotientGroup.mk t) ^ a)⁻¹⁻¹ := by rw [inv_inv, mul_assoc]
    rw [this]
    exact hWn.conj_mem w hw _
  ·
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow]
    have hmkt : mk t = QuotientGroup.mk t := rfl
    have hmkφ : mk φ = QuotientGroup.mk φ := rfl
    rw [hmkt, hmkφ]
    set A := (QuotientGroup.mk φ : primeLocalGaloisGroup q ⧸ U) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹ with hA
    set B := (QuotientGroup.mk t : primeLocalGaloisGroup q ⧸ U) ^ (q : ℕ) with hB
    have h1 : A * B⁻¹ ∈ W := hrel
    have : B⁻¹ * A = B⁻¹ * (A * B⁻¹) * B⁻¹⁻¹ := by rw [inv_inv, mul_assoc, inv_mul_cancel_right]
    rw [this]
    exact hWn.conj_mem _ h1 _

end S_ExtCitation_exists_tame_generator_at_level
end P2MW
export P2MW.S_ExtCitation_exists_tame_generator_at_level (solution)
