-- Prove2me | solution 1 for DriftLinBandit.BOB.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:59:08.032159+00:00
-- url     : https://prove2.me/submissions/0f8a6bee-90e3-44c0-b794-8c7d974427e9

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

open Matrix DriftLinBandit.BOB

namespace BOBLemma3Aux

lemma gram_transpose {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    (gram lam X W)ᵀ = gram lam X W := by
  unfold DriftLinBandit.BOB.gram
  rw [transpose_add, transpose_smul, transpose_one, transpose_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  ext i j; simp [vecMulVec_apply, mul_comm]

lemma gram_quad {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) (y : Fin d → ℝ) :
    y ⬝ᵥ (gram lam X W *ᵥ y) = lam * (y ⬝ᵥ y) + ∑ s ∈ W, (X s ⬝ᵥ y) ^ 2 := by
  unfold DriftLinBandit.BOB.gram
  rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec, dotProduct_smul]
  simp [dotProduct_comm y (X s), sq]

lemma gram_isUnit {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) :
    IsUnit (gram lam X W) := by
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h : gram lam X W *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have hq := gram_quad lam X W (a - b)
  rw [h, dotProduct_zero] at hq
  have hs : 0 ≤ ∑ s ∈ W, (X s ⬝ᵥ (a - b)) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdd : 0 ≤ (a - b) ⬝ᵥ (a - b) := by
    rw [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hz : (a - b) ⬝ᵥ (a - b) = 0 := by nlinarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 hz)


lemma gram_mulVec {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) (y : Fin d → ℝ) :
    gram lam X W *ᵥ y = lam • y + ∑ s ∈ W, (X s ⬝ᵥ y) • X s := by
  unfold DriftLinBandit.BOB.gram
  rw [add_mulVec, smul_mulVec, one_mulVec, sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [vecMulVec_mulVec]
  simp

lemma l2_eq {d : ℕ} (x : Fin d → ℝ) : l2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, l2]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

lemma l2_add_le {d : ℕ} (a b : Fin d → ℝ) : l2 (a + b) ≤ l2 a + l2 b := by
  rw [l2_eq, l2_eq, l2_eq, WithLp.toLp_add]
  exact norm_add_le _ _

lemma l2_nonneg {d : ℕ} (a : Fin d → ℝ) : 0 ≤ l2 a := Real.sqrt_nonneg _

lemma l2_sum_le {d : ℕ} (W : Finset ℕ) (f : ℕ → Fin d → ℝ) :
    l2 (∑ p ∈ W, f p) ≤ ∑ p ∈ W, l2 (f p) := by
  classical
  induction W using Finset.induction_on with
  | empty => simp [l2, dotProduct]
  | insert a W ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l2_add_le _ _).trans (by linarith)

lemma col_eq {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    (fun k => Ψ k j) = Ψ *ᵥ Pi.single j 1 := by
  ext k; simp [mulVec_single_one]

lemma single_mul_eq {d : ℕ} (f : Fin d → ℝ) (j k : Fin d) :
    f j * (Pi.single j (1 : ℝ) : Fin d → ℝ) k = f k * (Pi.single j (1 : ℝ) : Fin d → ℝ) k := by
  by_cases h : k = j
  · subst h; rfl
  · simp [Pi.single_apply, h]

/-- The contraction estimate under Assumption 1. -/
lemma key {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℝ) (hΨ : Ψᵀ * Ψ = 1) (lam : ℝ) (hlam : 0 < lam)
    (X : ℕ → Fin d → ℝ) (W S1 : Finset ℕ) (hS : S1 ⊆ W) (z : ℕ → ℝ) (i : ℕ → Fin d)
    (hX : ∀ s ∈ W, X s = z s • fun k => Ψ k (i s)) (Δ : Fin d → ℝ) :
    l2 ((gram lam X W)⁻¹ *ᵥ ∑ s ∈ S1, (X s ⬝ᵥ Δ) • X s) ≤ l2 Δ := by
  have hΨ' : Ψ * Ψᵀ = 1 := mul_eq_one_comm.1 hΨ
  set b := ∑ s ∈ S1, (X s ⬝ᵥ Δ) • X s with hb
  set y := (gram lam X W)⁻¹ *ᵥ b with hy
  have hVy : gram lam X W *ᵥ y = b := by
    rw [hy, mulVec_mulVec,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (gram_isUnit lam hlam X W)), one_mulVec]
  have hcol : ∀ s ∈ W, Ψᵀ *ᵥ X s = z s • (Pi.single (i s) 1 : Fin d → ℝ) := by
    intro s hs
    rw [hX s hs, mulVec_smul, col_eq, mulVec_mulVec, hΨ, one_mulVec]
  have hdot : ∀ s ∈ W, ∀ u : Fin d → ℝ, X s ⬝ᵥ u = z s * (Ψᵀ *ᵥ u) (i s) := by
    intro s hs u
    rw [hX s hs, smul_dotProduct, smul_eq_mul]
    congr 1
  set Y := Ψᵀ *ᵥ y with hY
  set D := Ψᵀ *ᵥ Δ with hD
  -- coordinates
  have hcoord : ∀ k, (lam + ∑ s ∈ W, z s ^ 2 * (Pi.single (i s) (1 : ℝ) : Fin d → ℝ) k) * Y k =
      (∑ s ∈ S1, z s ^ 2 * (Pi.single (i s) (1 : ℝ) : Fin d → ℝ) k) * D k := by
    intro k
    have e := congrArg (fun v => (Ψᵀ *ᵥ v) k) hVy
    rw [gram_mulVec, mulVec_add, mulVec_smul, mulVec_sum, hb, mulVec_sum] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mulVec_smul] at e
    rw [Finset.sum_congr rfl (fun s hs => by rw [hcol s hs, hdot s hs]),
      Finset.sum_congr (s₁ := S1) rfl (fun s hs => by rw [hcol s (hS hs), hdot s (hS hs)])] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [← hY, ← hD] at e
    have hL : ∑ x ∈ W, z x * Y (i x) * (z x * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) =
        ∑ x ∈ W, z x ^ 2 * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k * Y k := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have := single_mul_eq Y (i x) k
      calc z x * Y (i x) * (z x * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k)
          = z x ^ 2 * (Y (i x) * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) := by ring
        _ = z x ^ 2 * (Y k * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) := by rw [this]
        _ = _ := by ring
    have hR : ∑ x ∈ S1, z x * D (i x) * (z x * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) =
        ∑ x ∈ S1, z x ^ 2 * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k * D k := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have := single_mul_eq D (i x) k
      calc z x * D (i x) * (z x * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k)
          = z x ^ 2 * (D (i x) * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) := by ring
        _ = z x ^ 2 * (D k * (Pi.single (i x) (1 : ℝ) : Fin d → ℝ) k) := by rw [this]
        _ = _ := by ring
    rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← hL, ← hR]
    exact e
  have hsq : ∀ k, Y k ^ 2 ≤ D k ^ 2 := by
    intro k
    have hnn : ∀ s, 0 ≤ z s ^ 2 * (Pi.single (i s) (1 : ℝ) : Fin d → ℝ) k := by
      intro s
      apply mul_nonneg (sq_nonneg _)
      by_cases h : k = i s
      · subst h; simp
      · simp [h]
    set aW := ∑ s ∈ W, z s ^ 2 * (Pi.single (i s) (1 : ℝ) : Fin d → ℝ) k
    set aS := ∑ s ∈ S1, z s ^ 2 * (Pi.single (i s) (1 : ℝ) : Fin d → ℝ) k
    have h1 : 0 ≤ aS := Finset.sum_nonneg fun s _ => hnn s
    have h2 : aS ≤ aW := Finset.sum_le_sum_of_subset_of_nonneg hS fun s _ _ => hnn s
    have hpos : 0 < lam + aW := by linarith
    have e := hcoord k
    have : (lam + aW) ^ 2 * Y k ^ 2 ≤ (lam + aW) ^ 2 * D k ^ 2 := by
      have : (lam + aW) ^ 2 * Y k ^ 2 = aS ^ 2 * D k ^ 2 := by
        rw [← mul_pow, ← mul_pow, e]
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ h1 (by linarith) 2
    exact le_of_mul_le_mul_left this (by positivity)
  have hpars : ∀ u : Fin d → ℝ, (Ψᵀ *ᵥ u) ⬝ᵥ (Ψᵀ *ᵥ u) = u ⬝ᵥ u := by
    intro u
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hΨ', one_mulVec, dotProduct_comm]
  unfold l2
  apply Real.sqrt_le_sqrt
  rw [← hpars y, ← hpars Δ, ← hY, ← hD]
  unfold dotProduct
  exact Finset.sum_le_sum fun k _ => by rw [← sq, ← sq]; exact hsq k

lemma telescope {d : ℕ} (f : ℕ → Fin d → ℝ) (s n : ℕ) :
    ∑ p ∈ Finset.Ico s (s + n), (f p - f (p + 1)) = f s - f (s + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    abel

end BOBLemma3Aux

open BOBLemma3Aux in
theorem solution {d : ℕ} (I : Instance d) (hA : Assumption1 I) (lam : ℝ) (hlam : 0 < lam)
    (w : ℕ) (hw : 1 ≤ w) (X : ℕ → Fin d → ℝ) (hX : ∀ s ∈ Finset.Icc 1 I.T, X s ∈ I.D s)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 I.T) :
    l2 ((gram lam X (win 1 w t))⁻¹ *ᵥ
        ∑ s ∈ win 1 w t, (X s ⬝ᵥ (I.θ s - I.θ t)) • X s) ≤
      ∑ s ∈ win 1 w t, l2 (I.θ s - I.θ (s + 1)) := by
  classical
  rw [Finset.mem_Icc] at ht
  set W := win 1 w t with hW
  have hWmem : ∀ s, s ∈ W ↔ max 1 (t - w) ≤ s ∧ s ≤ t - 1 := fun s => by
    rw [hW, win, Finset.mem_Icc]
  obtain ⟨Ψ, hΨ, hrep⟩ := hA
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : ∀ v : Fin 0 → ℝ, l2 v = 0 := fun v => by simp [l2, dotProduct]
    rw [this]
    exact Finset.sum_nonneg fun _ _ => l2_nonneg _
  have hex : ∀ s, ∃ (z : ℝ) (i : Fin d), s ∈ W → X s = z • fun k => Ψ k i := by
    intro s
    by_cases hs : s ∈ W
    · have hs' : s ∈ Finset.Icc 1 I.T := by
        rw [hWmem] at hs; rw [Finset.mem_Icc]; omega
      obtain ⟨z, i, h⟩ := hrep s hs' (X s) (hX s hs')
      exact ⟨z, i, fun _ => h⟩
    · exact ⟨0, ⟨0, hd⟩, fun h => absurd h hs⟩
  choose z i hzi using hex
  -- rewrite the vector as a sum over increments
  have hvec : ∑ s ∈ W, (X s ⬝ᵥ (I.θ s - I.θ t)) • X s =
      ∑ p ∈ W, ∑ s ∈ W.filter (fun s => s ≤ p), (X s ⬝ᵥ (I.θ p - I.θ (p + 1))) • X s := by
    have h1 : ∀ s ∈ W, (X s ⬝ᵥ (I.θ s - I.θ t)) • X s =
        ∑ p ∈ W.filter (fun p => s ≤ p), (X s ⬝ᵥ (I.θ p - I.θ (p + 1))) • X s := by
      intro s hs
      have hs' := (hWmem s).1 hs
      have hfil : W.filter (fun p => s ≤ p) = Finset.Ico s (s + (t - s)) := by
        ext p; rw [Finset.mem_filter, hWmem, Finset.mem_Ico]; omega
      have hst : s + (t - s) = t := by have := ht.1; have := hs'.2; omega
      rw [hfil, ← Finset.sum_smul, ← dotProduct_sum, telescope, hst]
    rw [Finset.sum_congr rfl h1]
    apply Finset.sum_comm'
    intro s p
    simp only [Finset.mem_filter]
    tauto
  rw [hvec, mulVec_sum]
  refine (l2_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  exact key Ψ hΨ lam hlam X W _ (Finset.filter_subset _ _) z i hzi _
