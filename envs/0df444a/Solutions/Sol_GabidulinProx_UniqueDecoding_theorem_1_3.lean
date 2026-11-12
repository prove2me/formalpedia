-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:34.763488+00:00
-- url     : https://prove2.me/submissions/0610fc73-5517-415c-a65e-2ba6bc2efcb5

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Codes
import Theorems.Thm_GabidulinProx_UniqueDecoding_theorem_3_3
import Theorems.Thm_GabidulinProx_UniqueDecoding_remark_3_8

section
set_option autoImplicit false

namespace GabidulinProx.Dev.T13

open GabidulinProx.UniqueDecoding

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Fintype L] {n : ℕ}

lemma wordRank_eq_zero {M : Type*} [AddCommGroup M] [Module K M] (y : Fin n → M)
    (h : wordRank K y ≤ 0) : y = 0 := by
  have : Module.Finite K (Submodule.span K (Set.range y)) :=
    Module.Finite.span_of_finite K (Set.finite_range y)
  have h0 : Module.finrank K (Submodule.span K (Set.range y)) = 0 := by
    unfold wordRank at h; omega
  rw [Submodule.finrank_eq_zero] at h0
  funext r
  have : y r ∈ Submodule.span K (Set.range y) := Submodule.subset_span (Set.mem_range_self r)
  rw [h0] at this
  simpa using this

lemma pairRank_zero : pairRank K (0 : Fin n → L) (0 : Fin n → L) = 0 := by
  unfold pairRank wordRank
  have : Submodule.span K (Set.range (fun r : Fin n => ((0 : Fin n → L) r, (0 : Fin n → L) r)))
      = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro x ⟨r, rfl⟩
    simp
  rw [this]; simp

lemma exists_of_codeDistance_le (C : Submodule L (Fin n → L)) (v : Fin n → L) (e : ℕ)
    (h : codeDistance K C v ≤ e) : ∃ c ∈ C, wordRank K (v - c) ≤ e := by
  classical
  unfold codeDistance at h
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨c, _, hc⟩ := Finset.mem_image.1 (Finset.min'_mem
    (Finset.univ.image (fun c : C => wordRank K (v - c.val)))
    (Finset.image_nonempty.mpr Finset.univ_nonempty))
  exact ⟨c.val, c.2, by rw [hc]; exact h⟩

lemma pairDistance_le_of_mem (C : Submodule L (Fin n → L)) (u₀ u₁ c₀ c₁ : Fin n → L)
    (h₀ : c₀ ∈ C) (h₁ : c₁ ∈ C) :
    pairDistance K C u₀ u₁ ≤ pairRank K (u₀ - c₀) (u₁ - c₁) := by
  classical
  unfold pairDistance
  letI : Fintype C := Fintype.ofFinite C
  apply Finset.min'_le
  rw [Finset.mem_image]
  exact ⟨(⟨c₀, h₀⟩, ⟨c₁, h₁⟩), Finset.mem_univ _, rfl⟩

/-- e = 0: two distinct parameters in the code force both rows into the code. -/
lemma zero_case (C : Submodule L (Fin n → L)) (hn : 1 ≤ n) (u₀ u₁ : Fin n → L)
    (hfrac : uniformFraction (fun z => codeDistance K C (linePoint u₀ u₁ z) ≤ 0) >
      (1 : ℝ) / (Fintype.card L : ℝ)) :
    pairDistance K C u₀ u₁ ≤ 0 := by
  classical
  have hL : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 Fintype.card_pos
  unfold uniformFraction at hfrac
  rw [gt_iff_lt, div_lt_div_iff_of_pos_right hL] at hfrac
  have h1 := Nat.one_lt_cast.1 hfrac
  obtain ⟨z, hz, z', hz', hne⟩ := Finset.one_lt_card.1 h1
  have hin : ∀ w : L, codeDistance K C (linePoint u₀ u₁ w) ≤ 0 → linePoint u₀ u₁ w ∈ C := by
    intro w hw
    obtain ⟨c, hc, hr⟩ := exists_of_codeDistance_le _ _ _ hw
    have := wordRank_eq_zero _ hr
    rw [sub_eq_zero] at this
    rw [this]; exact hc
  have hz1 := hin z (by simpa using hz)
  have hz2 := hin z' (by simpa using hz')
  have hsub : (z - z') • u₁ ∈ C := by
    have := C.sub_mem hz1 hz2
    convert this using 1
    funext r
    simp only [linePoint, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hu₁ : u₁ ∈ C := by
    have := C.smul_mem (z - z')⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at this
  have hu₀ : u₀ ∈ C := by
    have := C.sub_mem hz1 (C.smul_mem z hu₁)
    convert this using 1
    funext r
    simp [linePoint]
  refine (pairDistance_le_of_mem C u₀ u₁ u₀ u₁ hu₀ hu₁).trans ?_
  rw [sub_self, sub_self, pairRank_zero]

end GabidulinProx.Dev.T13

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.T13

/-- Theorem 1.3, p.5, at full strength: every real radius, e=0 included,
exact error τ_e/|L| and the bound τ_e≤10q^(n-1). Here |L|=q^[L:K]. -/
theorem chk_theorem_1_3 {K L : Type*} [Field K] [Fintype K] [Field L] [Fintype L]
    [Algebra K L] {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (α : Fin n → L) (hα : LinearIndependent K α)
    (δ : ℝ) (hδ : 0 < δ) (hδmax : δ ≤ ((n - k : ℕ) : ℝ) / (2 * (n : ℝ))) :
    let e := ⌊δ * (n : ℝ)⌋₊
    HasProximityGap K (gabidulin K α k) δ
      ((tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ)) ∧
    tau (Fintype.card K) k e ≤ 10 * Fintype.card K ^ (n - 1) ∧
    (tau (Fintype.card K) k e : ℝ) / (Fintype.card L : ℝ) ≤
      (10 * Fintype.card K ^ (n - 1) : ℕ) / (Fintype.card L : ℝ) := by
  intro e
  have hn : 1 ≤ n := hk.trans hkn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hdist : ∀ d : ℕ, ((d : ℝ) / n ≤ δ) ↔ d ≤ e := by
    intro d
    rw [div_le_iff₀ hnR, show e = ⌊δ * (n : ℝ)⌋₊ from rfl,
      Nat.le_floor_iff (by positivity), mul_comm]
  have hpred : ∀ u₀ u₁ : Fin n → L,
      (fun z => (codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) : ℝ) / (n : ℝ) ≤ δ) =
      (fun z => codeDistance K (gabidulin K α k) (linePoint u₀ u₁ z) ≤ e) := by
    intro u₀ u₁
    funext z
    exact propext (hdist _)
  have hτ : tau (Fintype.card K) k e ≤ 10 * Fintype.card K ^ (n - 1) := by
    rcases Nat.eq_zero_or_pos e with he | he
    · have : tau (Fintype.card K) k e = 1 := by
        rw [he]; simp [tau, sigma]
      rw [this]
      have : 0 < Fintype.card K ^ (n - 1) := pow_pos (by omega) _
      omega
    · have hdec : 2 * e < n - k + 1 := by
        have h1 : (e : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
        have h2 : δ * (2 * (n : ℝ)) ≤ ((n - k : ℕ) : ℝ) := (le_div_iff₀ (by positivity)).1 hδmax
        have h3 : (2 * e : ℝ) ≤ ((n - k : ℕ) : ℝ) := by nlinarith
        have h4 : 2 * e ≤ n - k := by exact_mod_cast h3
        omega
      exact (remark_3_8 (Fintype.card K) n k e hq2 hk hkn he hdec).2.2.2.2.1
  refine ⟨?_, hτ, ?_⟩
  · intro u₀ u₁ hfrac
    rw [hpred] at hfrac
    rw [div_le_iff₀ hnR, ← div_le_iff₀ hnR, hdist]
    rcases Nat.eq_zero_or_pos e with he | he
    · have h1 : tau (Fintype.card K) k e = 1 := by
        rw [he]; simp [tau, sigma]
      rw [h1, he] at hfrac
      simp only [Nat.cast_one] at hfrac
      rw [he]
      exact zero_case _ hn u₀ u₁ hfrac
    · have hdec : 2 * e < n - k + 1 := by
        have h1 : (e : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
        have h2 : δ * (2 * (n : ℝ)) ≤ ((n - k : ℕ) : ℝ) := (le_div_iff₀ (by positivity)).1 hδmax
        have h3 : (2 * e : ℝ) ≤ ((n - k : ℕ) : ℝ) := by nlinarith
        have h4 : 2 * e ≤ n - k := by exact_mod_cast h3
        omega
      exact (theorem_3_3 hk hkn he hdec α hα u₀ u₁ hfrac).1
  · have hL : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 Fintype.card_pos
    exact div_le_div_of_nonneg_right (by exact_mod_cast hτ) hL.le

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_theorem_1_3 := @GabidulinProx.UniqueDecoding.chk_theorem_1_3
