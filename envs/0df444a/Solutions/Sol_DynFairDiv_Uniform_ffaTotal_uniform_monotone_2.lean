-- Prove2me | solution 2 for DynFairDiv.Uniform.ffaTotal_uniform_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:34:45.57881+00:00
-- url     : https://prove2.me/submissions/ae943db4-b1eb-409c-b253-dbba87670a01

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

set_option autoImplicit false
open DynFairDiv.Uniform

theorem ffa_closed (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (ℓ i : ℕ) (hi : i ≤ d) :
    ffa (uniformCV d) σ (ℓ * (d + 1) + i) =
      List.replicate i (σ / ((ℓ * d + i : ℕ) : ℝ)) ++
      (List.range ℓ).flatMap
        (fun k => List.replicate (d + 1) (σ / ((ℓ * d + i + k + 1 : ℕ) : ℝ))) := by
  have hsucc : ∀ t : ℕ, ffa (uniformCV d) σ (t + 1) =
      (ffa (uniformCV d) σ t).drop d ++
        List.replicate (min d t + 1) (σ / ((t + 1 : ℕ) : ℝ)) := fun t => rfl
  have hc : ∀ a b : ℕ, a = b → σ / (a : ℝ) = σ / (b : ℝ) := fun a b h => by rw [h]
  have hdrop : ∀ (i : ℕ) (a b : ℝ) (r : List ℝ), i ≤ d →
      (List.replicate i a ++ (List.replicate (d + 1) b ++ r)).drop d =
        List.replicate (i + 1) b ++ r := by
    intro i a b r hid
    have e : List.replicate (d + 1) b = List.replicate (d - i) b ++ List.replicate (i + 1) b := by
      rw [← List.replicate_add]; congr 1; omega
    have e2 : List.replicate i a ++ (List.replicate (d + 1) b ++ r) =
        (List.replicate i a ++ List.replicate (d - i) b) ++ (List.replicate (i + 1) b ++ r) := by
      rw [e]; simp only [List.append_assoc]
    rw [e2, List.drop_left']
    simp; omega
  -- step within a block
  have step1 : ∀ ℓ i : ℕ, i < d →
      ffa (uniformCV d) σ (ℓ * (d + 1) + i) =
        List.replicate i (σ / ((ℓ * d + i : ℕ) : ℝ)) ++
        (List.range ℓ).flatMap
          (fun k => List.replicate (d + 1) (σ / ((ℓ * d + i + k + 1 : ℕ) : ℝ))) →
      ffa (uniformCV d) σ (ℓ * (d + 1) + (i + 1)) =
        List.replicate (i + 1) (σ / ((ℓ * d + (i + 1) : ℕ) : ℝ)) ++
        (List.range ℓ).flatMap
          (fun k => List.replicate (d + 1) (σ / ((ℓ * d + (i + 1) + k + 1 : ℕ) : ℝ))) := by
    intro ℓ i hid ih
    rw [← add_assoc, hsucc]
    rcases ℓ with _ | ℓ'
    · rw [ih]
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.zero_mul, zero_add]
      rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp only [List.nil_append]
      have : min d i = i := min_eq_right hid.le
      rw [this]
    · rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map] at ih
      rw [ih, List.range_succ, List.flatMap_append]
      simp only [Nat.add_zero]
      rw [hdrop i _ _ _ hid.le]
      have hm : min d ((ℓ' + 1) * (d + 1) + i) = d := by
        apply min_eq_left; nlinarith
      rw [hm]
      simp only [List.append_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have e1 : σ / (((ℓ' + 1) * d + i + 1 : ℕ) : ℝ) = σ / (((ℓ' + 1) * d + (i + 1) : ℕ) : ℝ) :=
        hc _ _ (by ring)
      have e2 : σ / (((ℓ' + 1) * (d + 1) + i + 1 : ℕ) : ℝ) =
          σ / (((ℓ' + 1) * d + (i + 1) + ℓ' + 1 : ℕ) : ℝ) := hc _ _ (by ring)
      rw [e1, e2]
      congr 3
      funext k
      rw [hc ((ℓ' + 1) * d + i + k.succ + 1) ((ℓ' + 1) * d + (i + 1) + k + 1) (by simp; ring)]
  have step2 : ∀ ℓ : ℕ,
      ffa (uniformCV d) σ (ℓ * (d + 1) + d) =
        List.replicate d (σ / ((ℓ * d + d : ℕ) : ℝ)) ++
        (List.range ℓ).flatMap
          (fun k => List.replicate (d + 1) (σ / ((ℓ * d + d + k + 1 : ℕ) : ℝ))) →
      ffa (uniformCV d) σ ((ℓ + 1) * (d + 1) + 0) =
        List.replicate 0 (σ / (((ℓ + 1) * d + 0 : ℕ) : ℝ)) ++
        (List.range (ℓ + 1)).flatMap
          (fun k => List.replicate (d + 1) (σ / (((ℓ + 1) * d + 0 + k + 1 : ℕ) : ℝ))) := by
    intro ℓ ih
    have : (ℓ + 1) * (d + 1) + 0 = (ℓ * (d + 1) + d) + 1 := by ring
    rw [this, hsucc, ih]
    rw [List.drop_left' (by simp)]
    have hm : min d (ℓ * (d + 1) + d) = d := by
      apply min_eq_left; nlinarith
    rw [hm, List.range_succ, List.flatMap_append]
    simp only [List.replicate_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    have e2 : σ / ((ℓ * (d + 1) + d + 1 : ℕ) : ℝ) =
        σ / (((ℓ + 1) * d + 0 + ℓ + 1 : ℕ) : ℝ) := hc _ _ (by ring)
    rw [e2]
    congr 2
    funext k
    rw [hc (ℓ * d + d + k + 1) ((ℓ + 1) * d + 0 + k + 1) (by ring)]
  -- assemble
  induction ℓ generalizing i with
  | zero =>
    induction i with
    | zero => simp [ffa]
    | succ j ih =>
      exact step1 0 j (by omega) (ih (by omega)) |> fun h => by simpa using h
  | succ ℓ ihℓ =>
    have h0 := step2 ℓ (ihℓ d le_rfl)
    induction i with
    | zero => simpa using h0
    | succ j ih =>
      exact step1 (ℓ + 1) j (by omega) (ih (by omega))

theorem solution (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
    Monotone (ffaTotal (uniformCV d) σ) := by
  apply monotone_nat_of_le_succ
  intro t
  have hsucc : ffa (uniformCV d) σ (t + 1) =
      (ffa (uniformCV d) σ t).drop d ++
        List.replicate (min d t + 1) (σ / ((t + 1 : ℕ) : ℝ)) := rfl
  have hsplit := List.sum_take_add_sum_drop (ffa (uniformCV d) σ t) d
  unfold ffaTotal
  rw [hsucc, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  suffices htake : ((ffa (uniformCV d) σ t).take d).sum ≤
      ((min d t + 1 : ℕ) : ℝ) * (σ / ((t + 1 : ℕ) : ℝ)) by linarith
  obtain ⟨ℓ, i, hi, rfl⟩ : ∃ ℓ i : ℕ, i ≤ d ∧ t = ℓ * (d + 1) + i :=
    ⟨t / (d + 1), t % (d + 1), by have := Nat.mod_lt t (show 0 < d + 1 by omega); omega,
      by have := Nat.div_add_mod t (d + 1); rw [mul_comm] at this; exact this.symm⟩
  rw [ffa_closed d hd σ ℓ i hi]
  rcases ℓ with _ | ℓ'
  · simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.zero_mul, Nat.zero_add,
      List.take_replicate, List.sum_replicate, nsmul_eq_mul]
    rw [min_eq_right hi]
    have hp : ((i + 1 : ℕ) : ℝ) * (σ / ((i + 1 : ℕ) : ℝ)) = σ := by
      have : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hp]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simpa using hσ
    · have : (i : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ this]
  · rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have htk : ∀ (i : ℕ) (a b : ℝ) (r : List ℝ), i ≤ d →
        (List.replicate i a ++ (List.replicate (d + 1) b ++ r)).take d =
          List.replicate i a ++ List.replicate (d - i) b := by
      intro i a b r hid
      have e : List.replicate (d + 1) b = List.replicate (d - i) b ++ List.replicate (i + 1) b := by
        rw [← List.replicate_add]; congr 1; omega
      have e2 : List.replicate i a ++ (List.replicate (d + 1) b ++ r) =
          (List.replicate i a ++ List.replicate (d - i) b) ++ (List.replicate (i + 1) b ++ r) := by
        rw [e]; simp only [List.append_assoc]
      rw [e2, List.take_left']
      simp; omega
    rw [htk i _ _ _ hi]
    have hm : min d ((ℓ' + 1) * (d + 1) + i) = d := by
      apply min_eq_left; nlinarith
    rw [hm]
    simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
    have hid : (i : ℝ) ≤ d := by exact_mod_cast hi
    have hsub : ((d - i : ℕ) : ℝ) = (d : ℝ) - i := by push_cast [Nat.cast_sub hi]; ring
    rw [hsub]
    have hl : (1 : ℝ) ≤ ((ℓ' : ℝ) + 1) := by
      have : (0:ℝ) ≤ ℓ' := by positivity
      linarith
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have hA : (0 : ℝ) < ((ℓ' : ℝ) + 1) * d + i := by nlinarith
    push_cast
    have e1 : ((ℓ' : ℝ) + 1) * d + i + 0 + 1 = ((ℓ' : ℝ) + 1) * d + i + 1 := by ring
    rw [e1]
    have key : (i : ℝ) / (((ℓ' : ℝ) + 1) * d + i) + ((d : ℝ) - i) / (((ℓ' : ℝ) + 1) * d + i + 1) ≤
        ((d : ℝ) + 1) / (((ℓ' : ℝ) + 1) * ((d : ℝ) + 1) + i + 1) := by
      rw [div_add_div _ _ hA.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (ℓ' : ℝ) + 1 by positivity) (sub_nonneg.2 hid)]
    calc (i : ℝ) * (σ / (((ℓ' : ℝ) + 1) * d + i)) + ((d : ℝ) - i) * (σ / (((ℓ' : ℝ) + 1) * d + i + 1))
        = σ * ((i : ℝ) / (((ℓ' : ℝ) + 1) * d + i) + ((d : ℝ) - i) / (((ℓ' : ℝ) + 1) * d + i + 1)) := by ring
      _ ≤ σ * (((d : ℝ) + 1) / (((ℓ' : ℝ) + 1) * ((d : ℝ) + 1) + i + 1)) :=
          mul_le_mul_of_nonneg_left key hσ
      _ = ((d : ℝ) + 1) * (σ / (((ℓ' : ℝ) + 1) * ((d : ℝ) + 1) + i + 1)) := by ring
