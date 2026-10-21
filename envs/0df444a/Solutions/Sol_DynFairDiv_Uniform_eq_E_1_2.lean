-- Prove2me | solution 2 for DynFairDiv.Uniform.eq_E_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:30:57.908785+00:00
-- url     : https://prove2.me/submissions/a2fde7fc-d78a-491b-bc1b-e64dfed351ff

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

theorem solution (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) :
    Filter.Tendsto (fun ℓ : ℕ => ffaTotal (uniformCV d) σ (ℓ * (d + 1))) Filter.atTop
      (nhds (σ * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d))) := by
  have hflat : ∀ (n : ℕ) (g : ℕ → List ℝ),
      ((List.range n).flatMap g).sum = ∑ k ∈ Finset.range n, (g k).sum := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.flatMap_append, List.sum_append, ih,
        Finset.sum_range_succ]; simp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hS : ∀ ℓ : ℕ, ffaTotal (uniformCV d) σ (ℓ * (d + 1)) =
      σ * ((d : ℝ) + 1) * (((harmonic (ℓ * (d + 1)) : ℚ) : ℝ) - ((harmonic (ℓ * d) : ℚ) : ℝ)) := by
    intro ℓ
    have h := ffa_closed d hd σ ℓ 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at h
    unfold ffaTotal
    rw [h]
    simp only [List.replicate_zero, List.nil_append]
    rw [hflat]
    have hh : ℓ * (d + 1) = ℓ * d + ℓ := by ring
    have e : ∀ n : ℕ, ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (((i + 1 : ℕ) : ℝ))⁻¹ := by
      intro n; simp [harmonic]
    rw [e, e, hh, Finset.sum_range_add]
    simp only [List.sum_replicate, nsmul_eq_mul]
    rw [add_sub_cancel_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    field_simp
  have h1 := Real.tendsto_harmonic_sub_log
  have hA : Filter.Tendsto (fun ℓ : ℕ => ℓ * (d + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun ℓ => by simp only [id]; nlinarith) Filter.tendsto_id
  have hB : Filter.Tendsto (fun ℓ : ℕ => ℓ * d) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun ℓ => by simp only [id]; nlinarith [hd]) Filter.tendsto_id
  have h2 := (h1.comp hA).sub (h1.comp hB)
  have h3 := (h2.add_const (Real.log (((d : ℝ) + 1) / d))).const_mul (σ * ((d : ℝ) + 1))
  simp only [sub_self, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with ℓ hℓ
  rw [hS]
  congr 1
  simp only [Function.comp]
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have : Real.log ((ℓ * (d + 1) : ℕ) : ℝ) - Real.log ((ℓ * d : ℕ) : ℝ) = Real.log (((d : ℝ) + 1) / d) := by
    rw [← Real.log_div]
    · congr 1; push_cast; field_simp
    · positivity
    · positivity
  linarith
