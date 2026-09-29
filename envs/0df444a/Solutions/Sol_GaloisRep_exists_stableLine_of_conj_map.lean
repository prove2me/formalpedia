-- Prove2me | solution 1 for GaloisRep.exists_stableLine_of_conj_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/10b0a9e3-a416-5860-a965-1a7458057906

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_stableLine_of_conj_map
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace GaloisRep
namespace StableLineDescentInst

theorem exists_isFrobeniusAt' {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA

theorem exists_frobeniusAt_pow_mul_inertia_fixing' (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀] :
    ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ A.inertiaSubgroupIn ℚ ∧ (φ ^ n * τ)⁻¹ * σ ∈ L₀.fixingSubgroup :=
  ModularCurve.exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup q hq A hA φ hφ σ hσ L₀

end GaloisRep.StableLineDescentInst

namespace GaloisRep
namespace StableLineDescentAux

theorem mem_span_singleton_of_comp_eq_smul_comp {F F' : Type*} [Field F] [Field F']
    (e : F →+* F') {n : Type*} (v w : n → F) (d : F') (h : e ∘ w = d • (e ∘ v))
    (hv : v ≠ 0) : w ∈ F ∙ v := by
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv (funext h')
  have het : e (v t) ≠ 0 := (map_ne_zero e).mpr ht
  have hd : d = e (w t / v t) := by
    have h1 := congr_fun h t
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [map_div₀, h1, mul_div_cancel_right₀ _ het]
  refine Submodule.mem_span_singleton.mpr ⟨w t / v t, ?_⟩
  funext s
  apply e.injective
  have h2 := congr_fun h s
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [Pi.smul_apply, smul_eq_mul, map_mul, ← hd, h2]

theorem exists_rational_generator {F F' : Type*} [Field F] [Field F'] (e : F →+* F')
    (N : Matrix (Fin 2) (Fin 2) F) (hN : N ≠ 0) (u : Fin 2 → F')
    (h : ∀ w : Fin 2 → F', (N.map e).mulVec w ∈ F' ∙ u) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ u ∈ F' ∙ (e ∘ v) := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hN (Matrix.ext fun i j => h' i j)
  refine ⟨N.mulVec (Pi.single j 1), ?_, ?_⟩
  · intro h0
    apply hij
    have := congr_fun h0 i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Fin.sum_univ_two] using this
  · have hev : e ∘ N.mulVec (Pi.single j 1) = (N.map e).mulVec (e ∘ Pi.single j 1) := by
      funext t
      exact RingHom.map_mulVec e N _ t
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h (e ∘ Pi.single j 1))

    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hij
      have h1 : (e ∘ N.mulVec (Pi.single j 1)) i = 0 := by
        rw [hev, ← hc, zero_smul, Pi.zero_apply]
      have h2 : N.mulVec (Pi.single j 1) i = 0 := (map_eq_zero e).mp h1
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Fin.sum_univ_two] using h2
    refine Submodule.mem_span_singleton.mpr ⟨c⁻¹, ?_⟩
    rw [hev, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end GaloisRep.StableLineDescentAux

open GaloisRep.StableLineDescentAux in

theorem solution
    (p : ℕ) [Fact p.Prime] {F F' : Type} [Field F] [Field F'] (e : F →+* F')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F')
    (g : GL (Fin 2) F') (hconj : ∀ σ, (ρ' σ).val = g.val * (ρ σ).val.map e * (g⁻¹).val)
    (kn : ℕ) (ap : F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (h' : ∃ v' : Fin 2 → F', v' ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ' σ).val v' ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - w ∈ F' ∙ v') ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - e ap • w ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ' σ).val v' = ((a : F') ^ (kn - 1)) • v')) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ σ).val v ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - w ∈ F ∙ v) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - ap • w ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ σ).val v = ((a : F) ^ (kn - 1)) • v) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨v', hv'0, h1', h2', h3', h4'⟩ := h'

  have hGiG : (g⁻¹).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGGi : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ∀ σ, (ρ σ).val.map e = (g⁻¹).val * (ρ' σ).val * g.val := by
    intro σ
    rw [hconj σ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, Matrix.mul_assoc, hGiG,
      Matrix.mul_one]
  set u : Fin 2 → F' := (g⁻¹).val.mulVec v' with hudef
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv'0
    calc v' = (g.val * (g⁻¹).val).mulVec v' := by rw [hGGi, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, ← hudef, h0, Matrix.mulVec_zero]
  have hGu : g.val.mulVec u = v' := by rw [hudef, Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]
  have hGiGw : ∀ w : Fin 2 → F', (g⁻¹).val.mulVec (g.val.mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
  have linGi : ∀ x : Fin 2 → F', x ∈ F' ∙ v' → (g⁻¹).val.mulVec x ∈ F' ∙ u := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨c, by rw [Matrix.mulVec_smul]⟩

  have T1 : ∀ σ ∈ P.decompositionSubgroup ℚ, ((ρ σ).val.map e).mulVec u ∈ F' ∙ u := by
    intro σ hσ
    rw [key σ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGu]
    exact linGi _ (h1' σ hσ)
  have T2 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F',
      ((ρ σ).val.map e).mulVec w - w ∈ F' ∙ u := by
    intro σ hσ w
    have hw : ((ρ σ).val.map e).mulVec w - w =
        (g⁻¹).val.mulVec ((ρ' σ).val.mulVec (g.val.mulVec w) - g.val.mulVec w) := by
      rw [key σ, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGiGw]
    rw [hw]
    exact linGi _ (h2' σ hσ (g.val.mulVec w))
  have T3 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
      ∀ w : Fin 2 → F', ((ρ σ).val.map e).mulVec w - e ap • w ∈ F' ∙ u := by
    intro σ hσ w
    have hw : ((ρ σ).val.map e).mulVec w - e ap • w =
        (g⁻¹).val.mulVec ((ρ' σ).val.mulVec (g.val.mulVec w) - e ap • g.val.mulVec w) := by
      rw [key σ, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
        hGiGw]
    rw [hw]
    exact linGi _ (h3' σ hσ (g.val.mulVec w))
  have T4 : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
        ((ρ σ).val.map e).mulVec u = ((a : F') ^ (kn - 1)) • u := by
    intro σ hσ a ha
    rw [key σ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGu, h4' σ hσ a ha, Matrix.mulVec_smul]

  have finish : ∀ v : Fin 2 → F, v ≠ 0 → u ∈ F' ∙ (e ∘ v) →
      ∃ v : Fin 2 → F, v ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ σ).val v ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - w ∈ F ∙ v) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - ap • w ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ σ).val v = ((a : F) ^ (kn - 1)) • v) := by
    intro v hv0 huv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp huv

    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hu0 hc.symm
    have hev : (e ∘ v) = c⁻¹ • u := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hline : ∀ x : Fin 2 → F', x ∈ F' ∙ u → x ∈ F' ∙ (e ∘ v) := fun x hx => by
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨d * c, by rw [mul_smul, hc]⟩
    have desc : ∀ (X : Matrix (Fin 2) (Fin 2) F) (w : Fin 2 → F),
        (X.map e).mulVec (e ∘ w) ∈ F' ∙ u → X.mulVec w ∈ F ∙ v := by
      intro X w h
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hline _ h)
      have h2 : e ∘ (X.mulVec w) = d • (e ∘ v) := by
        rw [hd]
        funext t
        exact RingHom.map_mulVec e X w t
      exact mem_span_singleton_of_comp_eq_smul_comp e v (X.mulVec w) d h2 hv0
    refine ⟨v, hv0, ?_, ?_, ?_, ?_⟩
    · intro σ hσ
      apply desc
      rw [hev, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (T1 σ hσ)
    · intro σ hσ w
      have hX : (((ρ σ).val - 1).map e).mulVec (e ∘ w) = ((ρ σ).val.map e).mulVec (e ∘ w) - e ∘ w := by
        change (e.mapMatrix ((ρ σ).val - 1)).mulVec (e ∘ w) = _
        rw [map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec]
        rfl
      have h := desc ((ρ σ).val - 1) w (hX ▸ T2 σ hσ (e ∘ w))
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h
    · intro σ hσ w
      have hX : (((ρ σ).val - ap • (1 : Matrix (Fin 2) (Fin 2) F)).map e).mulVec (e ∘ w) =
          ((ρ σ).val.map e).mulVec (e ∘ w) - e ap • (e ∘ w) := by
        change (e.mapMatrix ((ρ σ).val - ap • 1)).mulVec (e ∘ w) = _
        rw [map_sub, Matrix.sub_mulVec]
        congr 1
        rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul e), Matrix.map_one _ (map_zero e) (map_one e),
          Matrix.smul_mulVec, Matrix.one_mulVec]
      have h := desc ((ρ σ).val - ap • 1) w (hX ▸ T3 σ hσ (e ∘ w))
      rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    · intro σ hσ a ha
      have h := T4 σ hσ a ha
      have h2 : ((ρ σ).val.map e).mulVec (e ∘ v) = ((a : F') ^ (kn - 1)) • (e ∘ v) := by
        rw [hev, Matrix.mulVec_smul, h, smul_comm]
      funext t
      apply e.injective
      have h3 := congr_fun h2 t
      rw [← RingHom.map_mulVec] at h3
      rw [h3, Pi.smul_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, smul_eq_mul, map_mul,
        map_pow, map_natCast]

  by_cases hI : ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, (ρ σ₀).val ≠ 1
  · obtain ⟨σ₀, hσ₀, hne⟩ := hI
    have hN0 : (ρ σ₀).val - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hNw : ∀ w : Fin 2 → F', (((ρ σ₀).val - 1).map e).mulVec w ∈ F' ∙ u := by
      intro w
      have hX : (((ρ σ₀).val - 1).map e).mulVec w = ((ρ σ₀).val.map e).mulVec w - w := by
        change (e.mapMatrix ((ρ σ₀).val - 1)).mulVec w = _
        rw [map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec]
        rfl
      rw [hX]
      exact T2 σ₀ hσ₀ w
    obtain ⟨v, hv0, huv⟩ := exists_rational_generator e _ hN0 u hNw
    exact finish v hv0 huv
  push Not at hI

  by_cases hF : ∃ σ₁ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      P.IsFrobeniusAt σ₁ p ∧ (ρ σ₁).val ≠ ap • 1
  · obtain ⟨σ₁, hσ₁, hne⟩ := hF
    have hN0 : (ρ σ₁).val - ap • 1 ≠ 0 := sub_ne_zero.mpr hne
    have hNw : ∀ w : Fin 2 → F', (((ρ σ₁).val - ap • (1 : Matrix (Fin 2) (Fin 2) F)).map e).mulVec w
        ∈ F' ∙ u := by
      intro w
      have hX : (((ρ σ₁).val - ap • (1 : Matrix (Fin 2) (Fin 2) F)).map e).mulVec w =
          ((ρ σ₁).val.map e).mulVec w - e ap • w := by
        change (e.mapMatrix ((ρ σ₁).val - ap • 1)).mulVec w = _
        rw [map_sub, Matrix.sub_mulVec]
        congr 1
        rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul e), Matrix.map_one _ (map_zero e) (map_one e),
          Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [hX]
      exact T3 σ₁ hσ₁ w
    obtain ⟨v, hv0, huv⟩ := exists_rational_generator e _ hN0 u hNw
    exact finish v hv0 huv
  push Not at hF

  obtain ⟨φ, hφ⟩ := GaloisRep.StableLineDescentInst.exists_isFrobeniusAt' hp P hP
  obtain ⟨L, hLfd, hL⟩ := hfin
  haveI := hLfd
  have hscal : ∀ σ ∈ P.decompositionSubgroup ℚ, ∃ n : ℕ, (ρ σ).val = (ap ^ n) • 1 := by
    intro σ hσ
    obtain ⟨n, τ, hτ, hfix⟩ :=
      GaloisRep.StableLineDescentInst.exists_frobeniusAt_pow_mul_inertia_fixing' p hp P hP φ hφ
        σ hσ L
    refine ⟨n, ?_⟩
    have h1 : ρ ((φ ^ n * τ)⁻¹ * σ) = 1 :=
      hL _ ((IntermediateField.mem_fixingSubgroup_iff L _).mp hfix)
    have h2 : σ = (φ ^ n * τ) * ((φ ^ n * τ)⁻¹ * σ) := by group
    rw [h2, map_mul, h1, mul_one, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, hF φ hφ,
      hI τ hτ, mul_one, smul_pow, one_pow]
  refine ⟨Pi.single 0 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have := congr_fun h0 0
    simp at this
  · intro σ hσ
    obtain ⟨n, hn⟩ := hscal σ hσ
    rw [hn, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro σ hσ w
    rw [hI σ hσ, Matrix.one_mulVec, sub_self]
    exact zero_mem _
  · intro σ hσ w
    rw [hF σ hσ, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    exact zero_mem _
  · intro σ hσ a ha
    have h := T4 σ hσ a ha
    rw [hI σ hσ, Matrix.map_one e (map_zero e) (map_one e), Matrix.one_mulVec] at h
    have hs : ((a : F') ^ (kn - 1)) = 1 := by
      by_contra hs
      apply hu0
      have h0 : (1 - (a : F') ^ (kn - 1)) • u = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hs))
    have hs' : ((a : F) ^ (kn - 1)) = 1 :=
      e.injective (by rw [map_pow, map_natCast, hs, map_one])
    rw [hI σ hσ, Matrix.one_mulVec, hs', one_smul]

end S_GaloisRep_exists_stableLine_of_conj_map
end P2MW
export P2MW.S_GaloisRep_exists_stableLine_of_conj_map (solution)
