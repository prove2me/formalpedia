-- Prove2me | solution 1 for ContractionLemma.lemma_A_10_hermite_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:45:09.009816+00:00
-- url     : https://prove2.me/submissions/3748ef47-509d-4637-95c0-320f263b727b

import Mathlib

open Polynomial

set_option autoImplicit false

theorem solution (D : ℕ) (pts : Finset ℚ) (m : ℚ → ℕ)
    (hm : D < ∑ t ∈ pts, m t) :
    (∀ F₁ F₂ : ℚ[X], F₁.natDegree ≤ D → F₂.natDegree ≤ D →
      (∀ t ∈ pts, ∀ k < m t, (taylor t F₁).coeff k = (taylor t F₂).coeff k) → F₁ = F₂) ∧
    ∃ Λ : ℚ → ℕ → ℚ, ∀ F : ℚ[X], F.natDegree ≤ D →
      F.eval 0 = ∑ t ∈ pts, ∑ k ∈ Finset.range (m t), Λ t k * (taylor t F).coeff k := by
  classical
  -- Part 1: uniqueness
  have huniq : ∀ F₁ F₂ : ℚ[X], F₁.natDegree ≤ D → F₂.natDegree ≤ D →
      (∀ t ∈ pts, ∀ k < m t, (taylor t F₁).coeff k = (taylor t F₂).coeff k) → F₁ = F₂ := by
    intro F₁ F₂ hF₁ hF₂ hcoeff
    let P : ℚ[X] := F₁ - F₂
    have hPdeg : P.natDegree ≤ D := by
      have h : P.natDegree ≤ max F₁.natDegree F₂.natDegree := natDegree_sub_le F₁ F₂
      exact h.trans (max_le hF₁ hF₂)
    have hPcoeff : ∀ t ∈ pts, ∀ k < m t, (taylor t P).coeff k = 0 := by
      intro t ht k hk
      have hsub : (taylor t) P = (taylor t) F₁ - (taylor t) F₂ := by
        simp [P, map_sub]
      rw [hsub, coeff_sub, hcoeff t ht k hk, sub_self]
    have hXdvd : ∀ t ∈ pts, X ^ (m t) ∣ (taylor t) P := by
      intro t ht
      rw [X_pow_dvd_iff]
      intro k hk
      exact hPcoeff t ht k hk
    have hdvd : ∀ t ∈ pts, (X - C t) ^ (m t) ∣ P := by
      intro t ht
      rcases hXdvd t ht with ⟨q, hq⟩
      refine ⟨(taylor (-t)) q, ?_⟩
      calc P = (taylor (-t)) ((taylor t) P) := by
              rw [taylor_taylor, neg_add_cancel, taylor_zero]
        _ = (taylor (-t)) (X ^ (m t) * q) := by rw [hq]
        _ = (taylor (-t)) (X ^ (m t)) * (taylor (-t)) q := by rw [taylor_mul]
        _ = (X - C t) ^ (m t) * (taylor (-t)) q := by
              rw [taylor_pow, taylor_X, map_neg, sub_eq_add_neg]
    have hcoprime : (↑pts : Set ℚ).Pairwise
        (Function.onFun IsCoprime (fun t => (X - C t) ^ (m t))) := by
      intro t _ t' _ hne
      exact (isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))).pow
    have hprod_dvd : (∏ t ∈ pts, (X - C t) ^ (m t)) ∣ P :=
      Finset.prod_dvd_of_coprime hcoprime hdvd
    have hQmonic : (∏ t ∈ pts, (X - C t) ^ (m t)).Monic :=
      monic_prod_of_monic pts _ (fun t _ => (monic_X_sub_C t).pow _)
    have hQdeg : (∏ t ∈ pts, (X - C t) ^ (m t)).natDegree = ∑ t ∈ pts, m t := by
      rw [natDegree_prod_of_monic pts _ (fun t _ => (monic_X_sub_C t).pow _)]
      apply Finset.sum_congr rfl
      intro t _
      rw [natDegree_pow, natDegree_X_sub_C, Nat.mul_one]
    by_contra hne
    have hPne : P ≠ 0 := by
      simpa [P] using sub_ne_zero.mpr hne
    have hle := natDegree_le_of_dvd hprod_dvd hPne
    rw [hQdeg] at hle
    omega
  refine ⟨huniq, ?_⟩
  -- Part 2: representation via a left inverse of the Taylor map
  let V : Submodule ℚ ℚ[X] := Polynomial.degreeLE ℚ (D : WithBot ℕ)
  let W : Type := (t : ↥pts) → Fin (m t.1) → ℚ
  let T : V →ₗ[ℚ] W :=
    LinearMap.pi (fun t : ↥pts =>
      LinearMap.pi (fun k : Fin (m t.1) =>
        (Polynomial.lcoeff ℚ k.val).comp ((Polynomial.taylor (t : ℚ)).comp V.subtype)))
  have hT_apply : ∀ (F : V) (t : ↥pts) (k : Fin (m t.1)),
      T F t k = (taylor (t : ℚ) (F : ℚ[X])).coeff k := by
    intro F t k
    change (Polynomial.lcoeff ℚ k.val) ((Polynomial.taylor (t : ℚ)) ((F : V) : ℚ[X])) =
      (taylor (t : ℚ) (F : ℚ[X])).coeff k
    rw [Polynomial.lcoeff_apply]
  have hTker : T.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro F₁ F₂ hTF
    apply Subtype.ext
    apply huniq F₁.val F₂.val
    · exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp F₁.property)
    · exact Polynomial.natDegree_le_iff_degree_le.mpr (Polynomial.mem_degreeLE.mp F₂.property)
    · intro t ht k hk
      have h := congr_fun (congr_fun hTF ⟨t, ht⟩) ⟨k, hk⟩
      rwa [hT_apply, hT_apply] at h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hTker
  let Λ : ℚ → ℕ → ℚ := fun t k =>
    if ht : t ∈ pts then
      if hk : k < m t then
        ((g (Pi.single ⟨t, ht⟩ (Pi.single ⟨k, hk⟩ (1 : ℚ))) : V) : ℚ[X]).eval 0
      else 0
    else 0
  have hexp : ∀ w : W, w = ∑ t : ↥pts, ∑ k : Fin (m t.1),
      w t k • (Pi.single t (Pi.single k (1 : ℚ)) : W) := by
    intro w
    funext t0 k0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single t0]
    · rw [Finset.sum_eq_single k0]
      · simp [Pi.single_eq_same]
      · intro k _ hk
        have h : (Pi.single k (1 : ℚ) : Fin (m t0.1) → ℚ) k0 = 0 :=
          Pi.single_eq_of_ne (Ne.symm hk) 1
        simp [Pi.single_eq_same, h]
      · intro hk0
        exact absurd (Finset.mem_univ k0) hk0
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro k _
      have h : (Pi.single t (Pi.single k (1 : ℚ)) : W) t0 = 0 :=
        Pi.single_eq_of_ne (Ne.symm ht) _
      simp [h]
    · intro ht0
      exact absurd (Finset.mem_univ t0) ht0
  let lam : W →ₗ[ℚ] ℚ := (Polynomial.lcoeff ℚ 0).comp (V.subtype.comp g)
  have hlam_apply : ∀ w : W, lam w = ((g w : V) : ℚ[X]).eval 0 := by
    intro w
    simp [lam, Polynomial.lcoeff_apply, Polynomial.coeff_zero_eq_eval_zero]
  have hlam_e : ∀ (t : ↥pts) (k : Fin (m t.1)),
      lam (Pi.single t (Pi.single k (1 : ℚ))) = Λ t.val k.val := by
    intro t k
    rw [hlam_apply]
    simp only [Λ]
    rw [dif_pos t.property, dif_pos k.isLt]
  have hidentity : ∀ w : W,
      lam w = ∑ t : ↥pts, ∑ k : Fin (m t.1), w t k * Λ t.val k.val := by
    intro w
    conv_lhs => rw [hexp w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, hlam_e t k, smul_eq_mul]
  refine ⟨Λ, ?_⟩
  intro F hF
  let Fv : V := ⟨F, Polynomial.mem_degreeLE.mpr (Polynomial.natDegree_le_iff_degree_le.mp hF)⟩
  have hgF : g (T Fv) = Fv := by
    have := LinearMap.congr_fun hg Fv
    simpa [LinearMap.comp_apply] using this
  calc F.eval 0 = lam (T Fv) := by rw [hlam_apply, hgF]
    _ = ∑ t : ↥pts, ∑ k : Fin (m t.1), (T Fv) t k * Λ t.val k.val := hidentity (T Fv)
    _ = ∑ t : ↥pts, ∑ k : Fin (m t.1),
          (taylor (t : ℚ) F).coeff k.val * Λ t.val k.val := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro k _
        rw [hT_apply]
    _ = ∑ t ∈ pts, ∑ k ∈ Finset.range (m t), (taylor t F).coeff k * Λ t k := by
        have hcoe : (∑ t : ↥pts, ∑ k : Fin (m t.1),
            (taylor (t : ℚ) F).coeff k.val * Λ t.val k.val)
            = ∑ t ∈ pts, ∑ k : Fin (m t), (taylor t F).coeff k * Λ t k :=
          Finset.sum_coe_sort pts (fun t => ∑ k : Fin (m t), (taylor t F).coeff k * Λ t k)
        rw [hcoe]
        apply Finset.sum_congr rfl
        intro t _
        rw [Fin.sum_univ_eq_sum_range (fun k => (taylor t F).coeff k * Λ t k) (m t)]
    _ = ∑ t ∈ pts, ∑ k ∈ Finset.range (m t), Λ t k * (taylor t F).coeff k := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro k _
        ring

