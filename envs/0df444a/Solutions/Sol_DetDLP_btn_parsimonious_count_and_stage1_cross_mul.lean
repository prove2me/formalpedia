-- Prove2me | solution 1 for DetDLP.btn_parsimonious_count_and_stage1_cross_mul
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:34.064856+00:00
-- url     : https://prove2.me/submissions/57dc65b5-16d5-4a9a-9317-b4107238f9be

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

private lemma truncPolyOfCoeffs_one_eq_natCast (P0 c : ℕ) :
    truncPolyOfCoeffs P0 1 (fun _ => c) = (c : TruncPoly P0 1) := by
  unfold truncPolyOfCoeffs
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, Polynomial.monomial_zero_left, map_natCast]

private lemma btn_parsimonious_count
    (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
    (P0 : ℕ) (hpar : IsParsimonious G T ext R) (hP0 : G.nE < P0) :
    (Finset.univ.filter R).card < 2 ^ P0 ∧
    BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
      truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card) := by
  let Sat : Finset (Fin G.nE → Bool) :=
    Finset.univ.filter (fun x => ∀ v : Fin G.nV, T v (fun j => x ((G.ports v).get j)) = true)
  have hcard_eq : Sat.card = (Finset.univ.filter R).card := by
    refine Finset.card_bij (fun x _ => fun i => x (ext i)) ?_ ?_ ?_
    · intro x hx
      simp only [Sat, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      by_contra hnotR
      exact ((hpar.2 (fun i => x (ext i))).2 hnotR) ⟨x, fun _ => rfl, hx⟩
    · intro x₁ hx₁ x₂ hx₂ hfeq
      simp only [Sat, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      let xext : Fin k → Bool := fun i => x₁ (ext i)
      have hRx : R xext := by
        by_contra hnotR
        exact ((hpar.2 xext).2 hnotR) ⟨x₁, fun _ => rfl, hx₁⟩
      obtain ⟨y, _, hy_uniq⟩ := (hpar.2 xext).1 hRx
      have h1 : x₁ = y := hy_uniq x₁ ⟨fun _ => rfl, hx₁⟩
      have h2 : x₂ = y := hy_uniq x₂ ⟨fun i => (congrFun hfeq i).symm, hx₂⟩
      exact h1.trans h2.symm
    · intro xext hxext
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxext
      obtain ⟨x, ⟨hext, hsat⟩, _⟩ := (hpar.2 xext).1 hxext
      refine ⟨x, ?_, funext hext⟩
      simp only [Sat, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsat
  have hcard_lt : (Finset.univ.filter R).card < 2 ^ P0 := by
    rw [← hcard_eq]
    have hle : Sat.card ≤ 2 ^ G.nE := by
      calc Sat.card ≤ (Finset.univ : Finset (Fin G.nE → Bool)).card := Finset.card_le_univ Sat
        _ = 2 ^ G.nE := by simp
    have hlt : 2 ^ G.nE < 2 ^ P0 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hP0
    exact lt_of_le_of_lt hle hlt
  refine ⟨hcard_lt, ?_⟩
  unfold BTNContract
  rw [truncPolyOfCoeffs_one_eq_natCast, ← hcard_eq]
  have hterm : ∀ x : Fin G.nE → Bool,
      (∏ v : Fin G.nV, truncPolyOfCoeffs P0 1
        (fun _ => if T v (fun i => x ((G.ports v).get i)) then 1 else 0)) =
      if x ∈ Sat then (1 : TruncPoly P0 1) else 0 := by
    intro x
    have hv : ∀ v : Fin G.nV,
        truncPolyOfCoeffs P0 1 (fun _ => if T v (fun i => x ((G.ports v).get i)) then 1 else 0) =
        if T v (fun i => x ((G.ports v).get i)) = true then (1 : TruncPoly P0 1) else 0 := by
      intro v
      rw [truncPolyOfCoeffs_one_eq_natCast]
      cases T v (fun i => x ((G.ports v).get i)) <;> simp
    simp_rw [hv]
    by_cases hx : x ∈ Sat
    · rw [if_pos hx]
      simp only [Sat, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.prod_eq_one fun v _ => by rw [if_pos (hx v)]
    · rw [if_neg hx]
      simp only [Sat, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hx
      obtain ⟨v₀, hv₀⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ v₀) (by rw [if_neg hv₀])
  simp_rw [hterm]
  simp [Sat]

private lemma sBTN_bounds (enet Δnet : ℕ) :
    let sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
    2 ≤ sBTN ∧ enet < sBTN ∧ Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10)) := by
  dsimp only
  set sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
  have h2 : 2 ≤ sBTN := le_max_left _ _
  have henet : enet < sBTN := by
    have : enet + 1 ≤ sBTN := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hΔ : Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10)) := by
    have hceil_le : Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9)) ≤ sBTN :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hleR : (Δnet : ℝ) ^ ((10 : ℝ) / 9) ≤ (sBTN : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hceil_le)
    have hrpow : ((Δnet : ℝ) ^ ((10 : ℝ) / 9)) ^ ((9 : ℝ) / 10) ≤ (sBTN : ℝ) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow (by positivity) hleR (by norm_num)
    rw [← Real.rpow_mul (Nat.cast_nonneg Δnet)] at hrpow
    have h1 : ((10 : ℝ) / 9) * ((9 : ℝ) / 10) = 1 := by norm_num
    rw [h1, Real.rpow_one] at hrpow
    have hle_ceil : (Δnet : ℝ) ≤ (Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10)) : ℝ) :=
      le_trans hrpow (Nat.le_ceil _)
    exact_mod_cast hle_ceil
  exact ⟨h2, henet, hΔ⟩

private lemma cross_mul_cond_exp
    (p n T m gord H₀ H₁ A₀ B₀ J₀ A₁ B₁ J₁ : ℕ)
    (hp : 0 < p) (hn : 0 < n) (hT : 0 < T) (hH₀ : 0 < H₀) (hH₁ : 0 < H₁) :
    let μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
    (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ) + 64 * μ ^ 2 * (H₀ : ℝ)) /
        (μ ^ 2 * (H₀ : ℝ)) ≤
      ((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ) + 64 * μ ^ 2 * (H₁ : ℝ)) /
        (μ ^ 2 * (H₁ : ℝ))) ↔
    (((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
        64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
        128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) ≤
      ((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
        64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
        128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ)) := by
  dsimp only
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hH₀R : (0 : ℝ) < (H₀ : ℝ) := by exact_mod_cast hH₀
  have hH₁R : (0 : ℝ) < (H₁ : ℝ) := by exact_mod_cast hH₁
  set μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
  have hμ_pos : 0 < μ := by positivity
  have hden₀ : 0 < μ ^ 2 * (H₀ : ℝ) := by positivity
  have hden₁ : 0 < μ ^ 2 * (H₁ : ℝ) := by positivity
  set X₀ : ℝ := (gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ)
  set X₁ : ℝ := (gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ)
  have hsplit₀ : (X₀ + 64 * μ ^ 2 * (H₀ : ℝ)) / (μ ^ 2 * (H₀ : ℝ)) = X₀ / (μ ^ 2 * (H₀ : ℝ)) + 64 := by
    rw [add_div, mul_assoc 64 (μ ^ 2) (H₀ : ℝ), mul_div_cancel_right₀ 64 (ne_of_gt hden₀)]
  have hsplit₁ : (X₁ + 64 * μ ^ 2 * (H₁ : ℝ)) / (μ ^ 2 * (H₁ : ℝ)) = X₁ / (μ ^ 2 * (H₁ : ℝ)) + 64 := by
    rw [add_div, mul_assoc 64 (μ ^ 2) (H₁ : ℝ), mul_div_cancel_right₀ 64 (ne_of_gt hden₁)]
  rw [hsplit₀, hsplit₁, add_le_add_iff_right, div_le_div_iff₀ hden₀ hden₁]
  have hcancel_μ2 :
      (X₀ * (μ ^ 2 * (H₁ : ℝ)) ≤ X₁ * (μ ^ 2 * (H₀ : ℝ))) ↔
      (X₀ * (H₁ : ℝ) ≤ X₁ * (H₀ : ℝ)) := by
    have h0 : X₀ * (μ ^ 2 * (H₁ : ℝ)) = (X₀ * (H₁ : ℝ)) * μ ^ 2 := by ring
    have h1 : X₁ * (μ ^ 2 * (H₀ : ℝ)) = (X₁ * (H₀ : ℝ)) * μ ^ 2 := by ring
    rw [h0, h1]
    exact mul_le_mul_iff_of_pos_right (pow_pos hμ_pos 2)
  rw [hcancel_μ2]
  have hp2m_pos : 0 < (p : ℝ) ^ (2 * m) := by positivity
  rw [← mul_le_mul_iff_of_pos_left hp2m_pos]
  have hpm_μ : (p : ℝ) ^ m * μ = ((n : ℝ) * (T : ℝ)) ^ m := by
    dsimp only [μ]
    rw [← mul_pow, mul_div_cancel₀ _ (ne_of_gt hpR)]
  have hp2m_split : (p : ℝ) ^ (2 * m) = (p : ℝ) ^ m * (p : ℝ) ^ m := by
    rw [two_mul, pow_add]
  have hL : (p : ℝ) ^ (2 * m) * (X₀ * (H₁ : ℝ)) =
      ((((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
          64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
          128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) : ℤ) : ℝ) := by
    dsimp only [X₀]
    push_cast
    calc (p : ℝ) ^ (2 * m) * (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ)) * (H₁ : ℝ))
        = ((p : ℝ) ^ (2 * m) * (gord : ℝ) * (J₀ : ℝ) +
            64 * (p : ℝ) ^ (2 * m) * (B₀ : ℝ) -
            128 * (p : ℝ) ^ m * ((p : ℝ) ^ m * μ) * (A₀ : ℝ)) * (H₁ : ℝ) := by
          rw [hp2m_split]; ring
      _ = ((p : ℝ) ^ (2 * m) * (gord : ℝ) * (J₀ : ℝ) +
            64 * (p : ℝ) ^ (2 * m) * (B₀ : ℝ) -
            128 * (p : ℝ) ^ m * ((n : ℝ) * (T : ℝ)) ^ m * (A₀ : ℝ)) * (H₁ : ℝ) := by
          rw [hpm_μ]
  have hR : (p : ℝ) ^ (2 * m) * (X₁ * (H₀ : ℝ)) =
      ((((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
          64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
          128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ) : ℤ) : ℝ) := by
    dsimp only [X₁]
    push_cast
    calc (p : ℝ) ^ (2 * m) * (((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ)) * (H₀ : ℝ))
        = ((p : ℝ) ^ (2 * m) * (gord : ℝ) * (J₁ : ℝ) +
            64 * (p : ℝ) ^ (2 * m) * (B₁ : ℝ) -
            128 * (p : ℝ) ^ m * ((p : ℝ) ^ m * μ) * (A₁ : ℝ)) * (H₀ : ℝ) := by
          rw [hp2m_split]; ring
      _ = ((p : ℝ) ^ (2 * m) * (gord : ℝ) * (J₁ : ℝ) +
            64 * (p : ℝ) ^ (2 * m) * (B₁ : ℝ) -
            128 * (p : ℝ) ^ m * ((n : ℝ) * (T : ℝ)) ^ m * (A₁ : ℝ)) * (H₀ : ℝ) := by
          rw [hpm_μ]
  rw [hL, hR]
  exact Int.cast_le

private lemma subcube_completion_counts (b r v p : ℕ) (_hr : r ≤ b) (hp : p ≤ 2 ^ b) :
    ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ u < p)).card =
      min ((v + 1) * 2 ^ (b - r)) p - min (v * 2 ^ (b - r)) p ∧
    ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ 1 ≤ u ∧ u < p)).card =
      min ((v + 1) * 2 ^ (b - r)) p - min (max (v * 2 ^ (b - r)) 1) p := by
  set K := 2 ^ (b - r)
  have hK_pos : 0 < K := Nat.pos_of_ne_zero (by positivity)
  have hdiv_iff : ∀ u : ℕ, u / K = v ↔ v * K ≤ u ∧ u < (v + 1) * K := by
    intro u
    constructor
    · intro h
      have h1 : v * K ≤ u := by
        rw [← h, mul_comm]
        exact Nat.mul_div_le u K
      have h2 : u < (v + 1) * K := by
        rw [← h, add_mul, one_mul, mul_comm _ K]
        exact Nat.lt_mul_div_succ u hK_pos
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Nat.div_eq_of_lt_le h1 h2
  have hset1 :
      (Finset.range (2 ^ b)).filter (fun u => u / K = v ∧ u < p) =
      Finset.Ico (min (v * K) p) (min ((v + 1) * K) p) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hdiv_iff]
    omega
  have hset2 :
      (Finset.range (2 ^ b)).filter (fun u => u / K = v ∧ 1 ≤ u ∧ u < p) =
      Finset.Ico (min (max (v * K) 1) p) (min ((v + 1) * K) p) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hdiv_iff]
    omega
  rw [hset1, hset2, Nat.card_Ico, Nat.card_Ico]
  exact ⟨rfl, rfl⟩

theorem solution :
    (∀ (G : BipartiteMultigraph)
       (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
       {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
       (P0 : ℕ),
       IsParsimonious G T ext R →
       G.nE < P0 →
       (Finset.univ.filter R).card < 2 ^ P0 ∧
       BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
         truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) ∧
    (∀ (enet Δnet : ℕ),
       let sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
       2 ≤ sBTN ∧ enet < sBTN ∧ Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10))) ∧
    (∀ (p n T m gord H₀ H₁ A₀ B₀ J₀ A₁ B₁ J₁ : ℕ),
       0 < p → 0 < n → 0 < T → 0 < H₀ → 0 < H₁ →
       let μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
       (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ) + 64 * μ ^ 2 * (H₀ : ℝ)) /
           (μ ^ 2 * (H₀ : ℝ)) ≤
         ((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ) + 64 * μ ^ 2 * (H₁ : ℝ)) /
           (μ ^ 2 * (H₁ : ℝ))) ↔
       (((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
           64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
           128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) ≤
         ((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
           64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
           128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ))) ∧
    (∀ (b r v p : ℕ), r ≤ b → p ≤ 2 ^ b →
       ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ u < p)).card =
         min ((v + 1) * 2 ^ (b - r)) p - min (v * 2 ^ (b - r)) p ∧
       ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ 1 ≤ u ∧ u < p)).card =
         min ((v + 1) * 2 ^ (b - r)) p - min (max (v * 2 ^ (b - r)) 1) p) :=
  ⟨btn_parsimonious_count,
   sBTN_bounds,
   cross_mul_cond_exp,
   subcube_completion_counts⟩
