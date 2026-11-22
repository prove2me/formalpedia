-- Prove2me | solution 1 for BellSampling.Learn.determined_by_signs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:55:31.328576+00:00
-- url     : https://prove2.me/submissions/0741317d-23b3-4fd9-b949-df2933c3e793

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_sigma_mul
import Theorems.Thm_BellSampling_Learn_stabSet_subspace
import Theorems.Thm_BellSampling_Learn_expect_eq_zero_of_not_mem
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private lemma sigma1_zero : sigma1 (0, 0) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [sigma1, sigma00, bitIdx]

private lemma sigma_zero (n : ℕ) : sigma (0 : PStr n) = 1 := by
  ext x y
  have h0 : ∀ i : Fin n, sigma1 ((0 : PStr n) i) (x i) (y i) = if x i = y i then 1 else 0 := by
    intro i
    have hs : (0 : PStr n) i = (0, 0) := rfl
    rw [hs, sigma1_zero]
    rfl
  simp_rw [sigma, Matrix.of_apply, h0]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have h_ex : ∃ i : Fin n, x i ≠ y i := by
      by_contra h_all
      exact hxy (funext fun i => not_ne_iff.mp (fun hne => h_all ⟨i, hne⟩))
    rcases h_ex with ⟨i, hi⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ i), Matrix.one_apply_ne hxy]
    exact if_neg hi

private lemma stabilizer_norm_eq_one {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∑ x : Bits n, star (ψ x) * ψ x = 1 := by
  rcases hψ with ⟨U, ⟨hU_unit, _⟩, rfl⟩
  have hU : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have hdot : star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n)) = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
    simp [dotProduct, zeroState]
  simpa [dotProduct, Pi.star_apply] using hdot

private lemma sigma1_mul_self (c : ZMod 2 × ZMod 2) (a b : Bool) :
    (∑ u : Bool, sigma1 c a u * sigma1 c u b) =
      (if c = (1, 1) then (-1 : ℂ) else 1) * (if a = b then 1 else 0) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases c with ⟨c1, c2⟩
  rcases hz c1 with rfl | rfl <;> rcases hz c2 with rfl | rfl <;>
    cases a <;> cases b <;>
    simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx, h01, h10]

private lemma prod_neg_one_boole {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∏ i : α, if p i then (-1 : ℂ) else 1) = (-1 : ℂ) ^ (Finset.univ.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

private lemma sigma_mul_self {n : ℕ} (t : PStr n) :
    sigma t * sigma t =
      ((-1 : ℂ) ^ (Finset.univ.filter fun i : Fin n => t i = (1, 1)).card) •
        (1 : Matrix (Bits n) (Bits n) ℂ) := by
  ext x z
  simp only [Matrix.mul_apply, sigma, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hprod : ∀ y : Bits n,
      (∏ i : Fin n, sigma1 (t i) (x i) (y i)) * (∏ i : Fin n, sigma1 (t i) (y i) (z i)) =
        ∏ i : Fin n, (sigma1 (t i) (x i) (y i) * sigma1 (t i) (y i) (z i)) :=
    fun y => (Finset.prod_mul_distrib).symm
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (i : Fin n) (u : Bool) =>
    sigma1 (t i) (x i) u * sigma1 (t i) u (z i))]
  simp_rw [sigma1_mul_self, Finset.prod_mul_distrib]
  rw [prod_neg_one_boole (fun i : Fin n => t i = (1, 1))]
  congr 1
  by_cases hxz : x = z
  · subst hxz
    simp
  · rw [Matrix.one_apply_ne hxz]
    have hex : ∃ i : Fin n, x i ≠ z i := by
      by_contra hall
      exact hxz (funext fun i => not_ne_iff.mp (fun hne => hall ⟨i, hne⟩))
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma pauliH_mul_self {n : ℕ} (t : PStr n) :
    pauliH t * pauliH t = 1 := by
  set k := (Finset.univ.filter fun i : Fin n => t i = (1, 1)).card
  simp only [pauliH, Matrix.smul_mul, Matrix.mul_smul, sigma_mul_self, smul_smul]
  have hpow : (-Complex.I) ^ k * ((-Complex.I) ^ k * (-1 : ℂ) ^ k) = 1 := by
    rw [← mul_pow, ← mul_pow]
    have hbase : -Complex.I * (-Complex.I * (-1 : ℂ)) = 1 := by
      simp
    rw [hbase, one_pow]
  rw [hpow, one_smul]

private lemma sum_sigma1_orth (a b a' b' : Bool) :
    (∑ c : ZMod 2 × ZMod 2, star (sigma1 c a b) * sigma1 c a' b') =
      if a = a' ∧ b = b' then (2 : ℂ) else 0 := by
  have huniv : (Finset.univ : Finset (ZMod 2 × ZMod 2)) =
      {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
  rw [huniv]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [sigma1, sigma00, sigma01, sigma10, sigma11_eq, bitIdx] <;>
    norm_num

private lemma sum_sigma_orth {n : ℕ} (x y x' y' : Bits n) :
    (∑ r : PStr n, star (sigma r x y) * sigma r x' y') =
      if x = x' ∧ y = y' then (2 : ℂ) ^ n else 0 := by
  have hterm : ∀ r : PStr n,
      star (sigma r x y) * sigma r x' y' =
        ∏ i : Fin n, (star (sigma1 (r i) (x i) (y i)) * sigma1 (r i) (x' i) (y' i)) := by
    intro r
    simp only [sigma, Matrix.of_apply, star_prod, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : Fin n) (c : ZMod 2 × ZMod 2) =>
    star (sigma1 c (x i) (y i)) * sigma1 c (x' i) (y' i))]
  simp_rw [sum_sigma1_orth]
  by_cases hxy : x = x' ∧ y = y'
  · rcases hxy with ⟨rfl, rfl⟩
    simp
  · rw [if_neg hxy]
    have hex : ∃ i : Fin n, ¬(x i = x' i ∧ y i = y' i) := by
      by_contra hall
      exact hxy ⟨funext fun i => Classical.byContradiction fun hx => hall ⟨i, fun h => hx h.1⟩,
        funext fun i => Classical.byContradiction fun hy => hall ⟨i, fun h => hy h.2⟩⟩
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (b : Fin n → PStr n) (hb : ∀ j, b j ∈ stabSet ψ) (hli : LinearIndependent (ZMod 2) b) :
    (∀ j, (pauliH (b j)).mulVec ψ = ψ ∨ (pauliH (b j)).mulVec ψ = -ψ) ∧
    ∀ φ : QState n,
      (∀ j (e : ℂ), (pauliH (b j)).mulVec ψ = e • ψ → (pauliH (b j)).mulVec φ = e • φ) →
      ∃ c : ℂ, φ = c • ψ := by
  classical
  have hnorm : ∑ x : Bits n, star (ψ x) * ψ x = 1 := stabilizer_norm_eq_one ψ hψ
  have h_dot_smul : ∀ (a : ℂ), (∑ x : Bits n, star (ψ x) * (a • ψ) x) = a := by
    intro a
    simp only [Pi.smul_apply, smul_eq_mul]
    have hp : (∑ x : Bits n, star (ψ x) * (a * ψ x)) = a * ∑ x : Bits n, star (ψ x) * ψ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hp, hnorm, mul_one]
  have h_part1 : ∀ j : Fin n, (pauliH (b j)).mulVec ψ = ψ ∨ (pauliH (b j)).mulVec ψ = -ψ := by
    intro j
    rcases hb j with ⟨c, hc⟩
    set k := (Finset.univ.filter fun i : Fin n => b j i = (1, 1)).card
    set e : ℂ := (-Complex.I) ^ k * c
    have he : (pauliH (b j)).mulVec ψ = e • ψ := by
      simp only [pauliH, Matrix.smul_mulVec, hc, smul_smul, e, k]
    have hsq : (pauliH (b j) * pauliH (b j)).mulVec ψ = (e * e) • ψ := by
      rw [← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul, he, smul_smul]
    rw [pauliH_mul_self, Matrix.one_mulVec] at hsq
    have he2 : e * e = 1 := by
      have h1 := h_dot_smul (e * e)
      rw [← hsq, hnorm] at h1
      exact h1.symm
    rcases mul_self_eq_one_iff.mp he2 with he1 | he1
    · left; rw [he, he1, one_smul]
    · right; rw [he, he1, neg_one_smul]
  refine ⟨h_part1, fun φ hφ => ?_⟩
  let M : Set (PStr n) :=
    {t | ∃ α : ℂ, (sigma t).mulVec ψ = α • ψ ∧ (sigma t).mulVec φ = α • φ}
  have h0M : (0 : PStr n) ∈ M := by
    refine ⟨1, ?_, ?_⟩ <;> simp [sigma_zero]
  have haddM : ∀ {s t : PStr n}, s ∈ M → t ∈ M → s + t ∈ M := by
    rintro s t ⟨α₁, hψ₁, hφ₁⟩ ⟨α₂, hψ₂, hφ₂⟩
    have hmul_ψ : (sigma s * sigma t).mulVec ψ = (α₁ * α₂) • ψ := by
      rw [← Matrix.mulVec_mulVec, hψ₂, Matrix.mulVec_smul, hψ₁, smul_smul, mul_comm]
    have hmul_φ : (sigma s * sigma t).mulVec φ = (α₁ * α₂) • φ := by
      rw [← Matrix.mulVec_mulVec, hφ₂, Matrix.mulVec_smul, hφ₁, smul_smul, mul_comm]
    rcases BellSampling.Learn.sigma_mul s t with hst | hst
    · refine ⟨α₁ * α₂, ?_, ?_⟩
      · rw [← hst, hmul_ψ]
      · rw [← hst, hmul_φ]
    · refine ⟨-(α₁ * α₂), ?_, ?_⟩
      · have hneg : (-sigma (s + t)).mulVec ψ = (α₁ * α₂) • ψ := by rw [← hst, hmul_ψ]
        rw [Matrix.neg_mulVec, neg_eq_iff_eq_neg] at hneg
        rw [hneg, neg_smul]
      · have hneg : (-sigma (s + t)).mulVec φ = (α₁ * α₂) • φ := by rw [← hst, hmul_φ]
        rw [Matrix.neg_mulVec, neg_eq_iff_eq_neg] at hneg
        rw [hneg, neg_smul]
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  let U_sub : Submodule (ZMod 2) (PStr n) :=
    { carrier := M
      zero_mem' := h0M
      add_mem' := fun hs ht => haddM hs ht
      smul_mem' := by
        intro a t ht
        rcases hz a with rfl | rfl
        · rw [zero_smul]; exact h0M
        · rw [one_smul]; exact ht }
  have hb_mem : ∀ j : Fin n, b j ∈ U_sub := by
    intro j
    set k := (Finset.univ.filter fun i : Fin n => b j i = (1, 1)).card
    have hk_ne : (-Complex.I) ^ k ≠ 0 := pow_ne_zero k (neg_ne_zero.mpr Complex.I_ne_zero)
    rcases h_part1 j with hpos | hneg
    · have hψ_j : (pauliH (b j)).mulVec ψ = (1 : ℂ) • ψ := by simpa using hpos
      have hφ_j : (pauliH (b j)).mulVec φ = (1 : ℂ) • φ := hφ j 1 hψ_j
      refine ⟨((-Complex.I) ^ k)⁻¹, ?_, ?_⟩
      · simp only [pauliH, Matrix.smul_mulVec] at hψ_j
        have h1 : ((-Complex.I) ^ k)⁻¹ • ((-Complex.I) ^ k • (sigma (b j)).mulVec ψ) =
            ((-Complex.I) ^ k)⁻¹ • ((1 : ℂ) • ψ) := congr_arg _ hψ_j
        simpa [smul_smul, inv_mul_cancel₀ hk_ne] using h1
      · simp only [pauliH, Matrix.smul_mulVec] at hφ_j
        have h1 : ((-Complex.I) ^ k)⁻¹ • ((-Complex.I) ^ k • (sigma (b j)).mulVec φ) =
            ((-Complex.I) ^ k)⁻¹ • ((1 : ℂ) • φ) := congr_arg _ hφ_j
        simpa [smul_smul, inv_mul_cancel₀ hk_ne] using h1
    · have hψ_j : (pauliH (b j)).mulVec ψ = (-1 : ℂ) • ψ := by simpa [neg_smul] using hneg
      have hφ_j : (pauliH (b j)).mulVec φ = (-1 : ℂ) • φ := hφ j (-1) hψ_j
      refine ⟨-((-Complex.I) ^ k)⁻¹, ?_, ?_⟩
      · simp only [pauliH, Matrix.smul_mulVec] at hψ_j
        have h1 : ((-Complex.I) ^ k)⁻¹ • ((-Complex.I) ^ k • (sigma (b j)).mulVec ψ) =
            ((-Complex.I) ^ k)⁻¹ • ((-1 : ℂ) • ψ) := congr_arg _ hψ_j
        simpa [smul_smul, inv_mul_cancel₀ hk_ne] using h1
      · simp only [pauliH, Matrix.smul_mulVec] at hφ_j
        have h1 : ((-Complex.I) ^ k)⁻¹ • ((-Complex.I) ^ k • (sigma (b j)).mulVec φ) =
            ((-Complex.I) ^ k)⁻¹ • ((-1 : ℂ) • φ) := congr_arg _ hφ_j
        simpa [smul_smul, inv_mul_cancel₀ hk_ne] using h1
  obtain ⟨W, hW_set, hW_rank⟩ := BellSampling.Learn.stabSet_subspace ψ hψ
  have hU_le_W : U_sub ≤ W := by
    intro t ht
    rw [← SetLike.mem_coe, hW_set]
    rcases ht with ⟨α, hα, _⟩
    exact ⟨α, hα⟩
  let bU : Fin n → U_sub := fun j => ⟨b j, hb_mem j⟩
  have hli_U : LinearIndependent (ZMod 2) bU := by
    have hcomp : (U_sub.subtype ∘ bU) = b := rfl
    exact LinearIndependent.of_comp U_sub.subtype (by rwa [hcomp])
  have hrank_U : n ≤ Module.finrank (ZMod 2) U_sub := by
    simpa [Fintype.card_fin] using hli_U.fintype_card_le_finrank
  have hcardW : Fintype.card W = 2 ^ n := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    simpa [ZMod.card, hW_rank] using hc
  have hcardU_ge : Fintype.card W ≤ Fintype.card U_sub := by
    have hcU := Module.card_eq_pow_finrank (K := ZMod 2) (V := U_sub)
    rw [hcardW, hcU, ZMod.card]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank_U
  have hW_le_U : W ≤ U_sub := by
    have h_fin_sub : Finset.univ.filter (fun t : PStr n => t ∈ U_sub) ⊆
        Finset.univ.filter (fun t : PStr n => t ∈ W) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact hU_le_W ht
    have hcard_filter_U : (Finset.univ.filter (fun t : PStr n => t ∈ U_sub)).card =
        Fintype.card U_sub :=
      (Fintype.card_subtype (fun t : PStr n => t ∈ U_sub)).symm
    have hcard_filter_W : (Finset.univ.filter (fun t : PStr n => t ∈ W)).card =
        Fintype.card W :=
      (Fintype.card_subtype (fun t : PStr n => t ∈ W)).symm
    have h_fin_eq : Finset.univ.filter (fun t : PStr n => t ∈ U_sub) =
        Finset.univ.filter (fun t : PStr n => t ∈ W) :=
      Finset.eq_of_subset_of_card_le h_fin_sub (by linarith)
    intro t ht
    have ht_mem : t ∈ Finset.univ.filter (fun x : PStr n => x ∈ W) := by simp [ht]
    rw [← h_fin_eq] at ht_mem
    simpa using ht_mem
  have h_stab_in_M : ∀ t ∈ stabSet ψ, t ∈ M := by
    intro t ht
    have htW : t ∈ W := by rwa [← SetLike.mem_coe, hW_set]
    exact hW_le_U htW
  refine ⟨∑ y' : Bits n, star (ψ y') * φ y', ?_⟩
  ext y
  simp only [Pi.smul_apply, smul_eq_mul]
  set S : ℂ := ∑ t : PStr n,
    star (∑ x : Bits n, star (ψ x) * ((sigma t).mulVec ψ) x) * ((sigma t).mulVec φ) y
  have hS_lhs : S = (2 : ℂ) ^ n * φ y := by
    have h_term : ∀ t : PStr n,
        star (∑ x : Bits n, star (ψ x) * ((sigma t).mulVec ψ) x) * ((sigma t).mulVec φ) y =
          if t ∈ W then φ y else 0 := by
      intro t
      by_cases htW : t ∈ W
      · rw [if_pos htW]
        have ht_stab : t ∈ stabSet ψ := by rwa [← hW_set]
        obtain ⟨α, hα_ψ, hα_φ⟩ := h_stab_in_M t ht_stab
        have h_sum_α : (∑ x : Bits n, star (ψ x) * ((sigma t).mulVec ψ) x) = α := by
          rw [hα_ψ]
          exact h_dot_smul α
        have h_sq_vec : ((sigma t * sigma t).mulVec ψ) = (α * α) • ψ := by
          rw [← Matrix.mulVec_mulVec, hα_ψ, Matrix.mulVec_smul, hα_ψ, smul_smul]
        have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
        have h_add_self : t + t = 0 := by ext i <;> exact h2 _
        have h_norm_α : star α * α = 1 := by
          have hα2 : α * α = 1 ∨ α * α = -1 := by
            rcases BellSampling.Learn.sigma_mul t t with hsq | hsq
            · left
              rw [h_add_self, sigma_zero] at hsq
              rw [hsq, Matrix.one_mulVec] at h_sq_vec
              have h1 := h_dot_smul (α * α)
              rw [← h_sq_vec, hnorm] at h1
              exact h1.symm
            · right
              rw [h_add_self, sigma_zero] at hsq
              rw [hsq, Matrix.neg_mulVec, Matrix.one_mulVec] at h_sq_vec
              have h1 := h_dot_smul (α * α)
              have h_neg_dot : (∑ x : Bits n, star (ψ x) * ((-ψ) x)) = -1 := by
                simp_rw [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, hnorm]
              rw [← h_sq_vec, h_neg_dot] at h1
              exact h1.symm
          have hnorm_sq : ‖α‖ ^ 2 = 1 := by
            rcases hα2 with h1 | h1
            · calc ‖α‖ ^ 2 = ‖α * α‖ := by rw [sq, ← norm_mul]
                _ = 1 := by rw [h1, norm_one]
            · calc ‖α‖ ^ 2 = ‖α * α‖ := by rw [sq, ← norm_mul]
                _ = 1 := by rw [h1, norm_neg, norm_one]
          have hc : star α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
            rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.normSq_eq_conj_mul_self]
          rw [hc, hnorm_sq, Complex.ofReal_one]
        rw [h_sum_α, hα_φ]
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, h_norm_α, one_mul]
      · rw [if_neg htW]
        have ht_not : t ∉ stabSet ψ := by rwa [← hW_set]
        rw [BellSampling.Learn.expect_eq_zero_of_not_mem ψ hψ t ht_not, star_zero, zero_mul]
    simp only [S]
    simp_rw [h_term]
    have h_sub : (∑ t : PStr n, if t ∈ W then φ y else 0) = ∑ _w : W, φ y := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun u : PStr n => u ∈ W)
        (fun u => by simp) (fun _ => φ y)
    rw [h_sub, Finset.sum_const, Finset.card_univ, hcardW, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  have hS_rhs : S = (2 : ℂ) ^ n * ((∑ y' : Bits n, star (ψ y') * φ y') * ψ y) := by
    simp only [S]
    have h_expand : ∀ t : PStr n,
        star (∑ x : Bits n, star (ψ x) * ((sigma t).mulVec ψ) x) * ((sigma t).mulVec φ) y =
        ∑ x : Bits n, ∑ x' : Bits n, ∑ y' : Bits n,
          (ψ x * star (ψ x') * φ y') * (star (sigma t x x') * sigma t y y') := by
      intro t
      simp only [Matrix.mulVec, dotProduct]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [star_mul', star_star, star_sum, mul_comm (ψ x), Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y' _ => ?_
      simp only [star_mul']
      ring
    simp_rw [h_expand]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ (α := PStr n))]
    have h_sum_t : ∀ x x' y' : Bits n,
        (∑ t : PStr n, (ψ x * star (ψ x') * φ y') * (star (sigma t x x') * sigma t y y')) =
        (ψ x * star (ψ x') * φ y') * (if x = y ∧ x' = y' then (2 : ℂ) ^ n else 0) :=
      fun x x' y' => by rw [← Finset.mul_sum, sum_sigma_orth]
    simp_rw [h_sum_t]
    have h_diag : ∀ x x' : Bits n,
        (∑ y' : Bits n,
          (ψ x * star (ψ x') * φ y') * if x = y ∧ x' = y' then (2 : ℂ) ^ n else 0) =
        if x = y then (2 : ℂ) ^ n * (star (ψ x') * φ x') * ψ y else 0 := by
      intro x x'
      by_cases hxy : x = y
      · subst hxy
        simp only [true_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        ring
      · simp [hxy]
    simp_rw [h_diag]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← Finset.sum_mul]
    simp_rw [← Finset.mul_sum, mul_assoc]
  have h2n_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  exact mul_left_cancel₀ h2n_ne (hS_lhs.symm.trans hS_rhs)
