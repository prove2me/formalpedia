-- Prove2me | solution 2 for DynFairDiv.Uniform.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:46:27.309285+00:00
-- url     : https://prove2.me/submissions/0d1f5390-8062-49eb-80bd-70ce11ffa750

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

set_option autoImplicit false
open DynFairDiv.Uniform

theorem ffa_length (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) : (ffa ψ σ t).length = t := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, List.length_append, List.length_drop, ih, List.length_replicate]
    omega

theorem ffa_mem_ge (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    ∀ x ∈ ffa ψ σ t, σ / (t : ℝ) ≤ x := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    intro x hx
    rw [ffa, List.mem_append] at hx
    rcases hx with hx | hx
    · have h1 := ih x (List.mem_of_mem_drop hx)
      have h2 : σ / ((t + 1 : ℕ) : ℝ) ≤ σ / (t : ℝ) := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · subst h0; simp [ffa] at hx
        · apply div_le_div_of_nonneg_left hσ (by exact_mod_cast hpos)
          push_cast; linarith
      exact h2.trans h1
    · rw [List.eq_of_mem_replicate hx]

theorem ffa_sorted (ψ : ℕ → ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t : ℕ) :
    (ffa ψ σ t).Pairwise (· ≥ ·) := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, List.pairwise_append]
    refine ⟨ih.sublist (List.drop_sublist _ _), ?_, ?_⟩
    · exact List.pairwise_replicate.2 (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      have h1 := ffa_mem_ge ψ σ hσ t a (List.mem_of_mem_drop ha)
      have h2 : σ / ((t + 1 : ℕ) : ℝ) ≤ σ / (t : ℝ) := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · subst h0; simp [ffa] at ha
        · apply div_le_div_of_nonneg_left hσ (by exact_mod_cast hpos)
          push_cast; linarith
      exact h2.trans h1

/-- counting lemma: for a nonincreasing list, dropping `k` entries lowers the count of
entries `≥ x` by `k` (truncated). -/
theorem countP_drop_sorted (x : ℝ) : ∀ (F : List ℝ) (k : ℕ), F.Pairwise (· ≥ ·) →
    (F.drop k).countP (fun y => decide (x ≤ y)) = F.countP (fun y => decide (x ≤ y)) - k := by
  intro F
  induction F with
  | nil => intro k _; simp
  | cons a F ih =>
    intro k hp
    rcases k with _ | k
    · simp
    · rw [List.pairwise_cons] at hp
      by_cases hax : x ≤ a
      · rw [List.drop_succ_cons, ih k hp.2, List.countP_cons_of_pos (by simpa using hax)]
        omega
      · have h0 : F.countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y hy
          simp; linarith [not_le.1 hax]
        have h1 : (F.drop k).countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y (List.mem_of_mem_drop hy)
          simp; linarith [not_le.1 hax]
        rw [List.drop_succ_cons, h1, List.countP_cons_of_neg (by simpa using hax), h0]
        simp

/-- domination of a nonincreasing list by a family, in terms of counts, implies domination of sums -/
theorem dom_sum : ∀ (F : List ℝ) (s : Finset ℕ) (Y : ℕ → ℝ), F.Pairwise (· ≥ ·) →
    (∀ k ∈ s, 0 ≤ Y k) →
    (∀ x : ℝ, F.countP (fun y => decide (x ≤ y)) ≤ (s.filter (fun k => x ≤ Y k)).card) →
    F.sum ≤ ∑ k ∈ s, Y k := by
  intro F
  induction F with
  | nil =>
    intro s Y _ hY _
    simpa using Finset.sum_nonneg hY
  | cons a F ih =>
    intro s Y hp hY hc
    rw [List.pairwise_cons] at hp
    have h1 := hc a
    rw [List.countP_cons_of_pos (by simp)] at h1
    have hne : (s.filter (fun k => a ≤ Y k)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨k, hk⟩ := hne
    rw [Finset.mem_filter] at hk
    have hsum : ∑ j ∈ s, Y j = Y k + ∑ j ∈ s.erase k, Y j := by
      rw [Finset.add_sum_erase _ _ hk.1]
    rw [List.sum_cons, hsum]
    have := ih (s.erase k) Y hp.2 (fun j hj => hY j (Finset.mem_of_mem_erase hj)) ?_
    · linarith [hk.2]
    · intro x
      by_cases hax : x ≤ a
      · have h2 := hc x
        rw [List.countP_cons_of_pos (by simpa using hax)] at h2
        have h3 : (s.filter (fun j => x ≤ Y j)).card =
            ((s.erase k).filter (fun j => x ≤ Y j)).card + 1 := by
          have : (s.erase k).filter (fun j => x ≤ Y j) = (s.filter (fun j => x ≤ Y j)).erase k := by
            ext j; simp [Finset.mem_filter, Finset.mem_erase]; tauto
          rw [this, Finset.card_erase_add_one]
          rw [Finset.mem_filter]; exact ⟨hk.1, hax.trans hk.2⟩
        omega
      · have h0 : F.countP (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have := hp.1 y hy
          simp; linarith [not_le.1 hax]
        rw [h0]; exact Nat.zero_le _

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

theorem eqE1 (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) :
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

theorem ffaTotal_mono (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) (hσ : 0 ≤ σ) :
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

theorem thm1 (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (X : ℕ → ℕ → ℝ)
    (hσ : 0 ≤ σ) (hX : AchievesRatio ψ n σ X) :
    ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
      (∀ x ∈ ffa ψ σ t, 0 ≤ x) ∧ ffaTotal ψ σ t ≤ 1 := by
  obtain ⟨hf, hr⟩ := hX
  have key : ∀ t : ℕ, (t : ℕ∞) ≤ n → ∀ x : ℝ,
      (ffa ψ σ t).countP (fun y => decide (x ≤ y)) ≤
        ((Finset.range t).filter (fun k => x ≤ X t k)).card := by
    intro t
    induction t with
    | zero => intro _ x; simp [ffa]
    | succ t ih =>
      intro htn x
      have htn' : (t : ℕ∞) ≤ n := le_trans (by exact_mod_cast Nat.le_succ t) htn
      have ih := ih htn' x
      have h1 : 1 ≤ t + 1 := by omega
      obtain ⟨hnn, -, hdis⟩ := hf (t + 1) h1 htn
      have hD : ((Finset.range t).filter (fun k => X (t + 1) k < X t k)).card ≤ ψ (t + 1) := by
        rcases t with _ | t
        · simp
        · have := hdis (by omega)
          simpa using this
      rw [ffa, List.countP_append]
      by_cases hxc : x ≤ σ / ((t + 1 : ℕ) : ℝ)
      · have hall : (Finset.range (t + 1)).filter (fun k => x ≤ X (t + 1) k) = Finset.range (t + 1) := by
          apply Finset.filter_true_of_mem
          intro k hk
          exact hxc.trans (hr (t + 1) h1 htn k (Finset.mem_range.1 hk))
        rw [hall, Finset.card_range]
        have hl := ffa_length ψ σ (t + 1)
        rw [ffa, List.length_append] at hl
        have := List.countP_le_length (p := fun y => decide (x ≤ y)) (l := (ffa ψ σ t).drop (ψ (t + 1)))
        have := List.countP_le_length (p := fun y => decide (x ≤ y))
          (l := List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ)))
        omega
      · have hrep : (List.replicate (min (ψ (t + 1)) t + 1) (σ / ((t + 1 : ℕ) : ℝ))).countP
            (fun y => decide (x ≤ y)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          rw [List.eq_of_mem_replicate hy]
          simpa using hxc
        rw [hrep, Nat.add_zero, countP_drop_sorted x _ _ (ffa_sorted ψ σ hσ t)]
        set A := (Finset.range t).filter (fun k => x ≤ X t k) with hA
        set D := (Finset.range t).filter (fun k => X (t + 1) k < X t k) with hDdef
        have hsub : A \ D ⊆ (Finset.range (t + 1)).filter (fun k => x ≤ X (t + 1) k) := by
          intro k hk
          rw [Finset.mem_sdiff, hA, hDdef, Finset.mem_filter, Finset.mem_filter] at hk
          obtain ⟨⟨hkr, hkx⟩, hkd⟩ := hk
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hkr)), ?_⟩
          have : ¬ (X (t + 1) k < X t k) := fun h => hkd ⟨hkr, h⟩
          linarith [not_lt.1 this]
        have h2 := Finset.card_le_card hsub
        have h3 := Finset.le_card_sdiff D A
        omega
  intro t ht1 htn
  have hlen := ffa_length ψ σ t
  have hnn : ∀ x ∈ ffa ψ σ t, 0 ≤ x := fun x hx =>
    le_trans (div_nonneg hσ (Nat.cast_nonneg _)) (ffa_mem_ge ψ σ hσ t x hx)
  refine ⟨hnn, ?_⟩
  have hfin := dom_sum (ffa ψ σ t) (Finset.range t) (X t) (ffa_sorted ψ σ hσ t)
    (fun k hk => (hf t ht1 htn).1 k (Finset.mem_range.1 hk)) (key t htn)
  exact hfin.trans (hf t ht1 htn).2.1

/-- state of the realization: the list of users ordered by (nonincreasing) share, and the shares -/
noncomputable def realState (ψ : ℕ → ℕ) (σ : ℝ) : ℕ → List ℕ × (ℕ → ℝ)
  | 0 => ([], fun _ => 0)
  | t + 1 =>
    let π := (realState ψ σ t).1
    let v := (realState ψ σ t).2
    let m := min (ψ (t + 1)) t
    (π.drop m ++ π.take m ++ [t],
      fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)

theorem realState_inv (ψ : ℕ → ℕ) (σ : ℝ) (t : ℕ) :
    (realState ψ σ t).1.Perm (List.range t) ∧
      (realState ψ σ t).1.map (realState ψ σ t).2 = ffa ψ σ t := by
  induction t with
  | zero => simp [realState, ffa]
  | succ t ih =>
    obtain ⟨hp, hm⟩ := ih
    set π := (realState ψ σ t).1 with hπ
    set v := (realState ψ σ t).2 with hv
    have hlen : π.length = t := by rw [hp.length_eq]; simp
    have hnd : π.Nodup := hp.nodup_iff.2 (List.nodup_range)
    have hmem : ∀ k ∈ π, k < t := fun k hk => List.mem_range.1 (hp.subset hk)
    have hrs : realState ψ σ (t + 1) =
        (π.drop (min (ψ (t + 1)) t) ++ π.take (min (ψ (t + 1)) t) ++ [t],
          fun k => if k = t ∨ k ∈ π.take (min (ψ (t + 1)) t) then σ / ((t + 1 : ℕ) : ℝ) else v k) := rfl
    rw [hrs]
    set m := min (ψ (t + 1)) t with hmdef
    have hmle : m ≤ t := min_le_right _ _
    constructor
    · -- permutation
      have : (π.drop m ++ π.take m ++ [t]).Perm (π ++ [t]) := by
        refine List.Perm.append_right _ ?_
        exact List.perm_append_comm.trans (by rw [List.take_append_drop])
      refine this.trans ?_
      rw [List.range_succ]
      exact hp.append_right _
    · simp only
      have hdisj : ∀ k ∈ π.drop m, k ≠ t ∧ k ∉ π.take m := by
        intro k hk
        refine ⟨(hmem k (List.mem_of_mem_drop hk)).ne, ?_⟩
        intro hk2
        have := List.disjoint_take_drop hnd (le_refl m)
        exact this hk2 hk
      rw [List.map_append, List.map_append]
      have h1 : (π.drop m).map (fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)
          = (π.drop m).map v := by
        apply List.map_congr_left
        intro k hk
        have := hdisj k hk
        simp [this.1, this.2]
      have h2 : (π.take m).map (fun k => if k = t ∨ k ∈ π.take m then σ / ((t + 1 : ℕ) : ℝ) else v k)
          = List.replicate m (σ / ((t + 1 : ℕ) : ℝ)) := by
        have : (π.take m).length = m := by simp [hlen]; omega
        rw [List.map_congr_left (g := fun _ => σ / ((t + 1 : ℕ) : ℝ))
          (fun k hk => by simp [hk]), List.map_const', this]
      rw [h1, h2, List.map_drop, hm, ffa]
      have hd : (ffa ψ σ t).drop (ψ (t + 1)) = (ffa ψ σ t).drop m := by
        rw [hmdef]
        rcases le_total (ψ (t + 1)) t with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h]
          rw [List.drop_eq_nil_of_le (by rw [ffa_length]; exact h),
              List.drop_eq_nil_of_le (by rw [ffa_length])]
      rw [hd]
      simp only [List.map_cons, List.map_nil, ite_true, true_or]
      rw [List.replicate_succ', List.append_assoc]

theorem ffa_realizes (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (hσ : 0 ≤ σ)
    (hfeas : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n → ffaTotal ψ σ t ≤ 1) :
    ∃ X, AchievesRatio ψ n σ X ∧
      ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
        (List.ofFn (fun k : Fin t => X t k.val)).Perm (ffa ψ σ t) := by
  have hmemv : ∀ t k : ℕ, k < t → σ / (t : ℝ) ≤ (realState ψ σ t).2 k := by
    intro t k hk
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    have hk' : k ∈ (realState ψ σ t).1 := hp.symm.subset (List.mem_range.2 hk)
    have : (realState ψ σ t).2 k ∈ ffa ψ σ t := by
      rw [← hm]; exact List.mem_map_of_mem hk'
    exact ffa_mem_ge ψ σ hσ t _ this
  have hsum : ∀ t, ∑ k ∈ Finset.range t, (realState ψ σ t).2 k = ffaTotal ψ σ t := by
    intro t
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    have h1 : ∀ (f : ℕ → ℝ) (t : ℕ), ∑ k ∈ Finset.range t, f k = ((List.range t).map f).sum := by
      intro f t
      induction t with
      | zero => simp
      | succ t ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp
    rw [h1, ffaTotal, ← hm]
    exact (hp.symm.map _).sum_eq
  refine ⟨fun t => (realState ψ σ t).2, ⟨fun t ht1 htn => ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro k hk
    exact le_trans (div_nonneg hσ (Nat.cast_nonneg _)) (hmemv t k hk)
  · rw [hsum]; exact hfeas t ht1 htn
  · intro h2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hrs : realState ψ σ (s + 1) =
        ((realState ψ σ s).1.drop (min (ψ (s + 1)) s) ++
            (realState ψ σ s).1.take (min (ψ (s + 1)) s) ++ [s],
          fun k => if k = s ∨ k ∈ (realState ψ σ s).1.take (min (ψ (s + 1)) s)
            then σ / ((s + 1 : ℕ) : ℝ) else (realState ψ σ s).2 k) := rfl
    have hsub : (Finset.range s).filter (fun k => (realState ψ σ (s + 1)).2 k < (realState ψ σ s).2 k)
        ⊆ ((realState ψ σ s).1.take (min (ψ (s + 1)) s)).toFinset := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [List.mem_toFinset]
      by_contra hnot
      rw [hrs] at hk
      simp only [hnot, or_false, hk.1.ne] at hk
      simp at hk
    refine (Finset.card_le_card hsub).trans ?_
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_take]
    exact (min_le_left _ _).trans (min_le_left _ _)
  · intro t ht1 htn k hk
    exact hmemv t k hk
  · intro t ht1 htn
    have h1 : List.ofFn (fun k : Fin t => (realState ψ σ t).2 k.val) =
        (List.range t).map (realState ψ σ t).2 := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp
    obtain ⟨hp, hm⟩ := realState_inv ψ σ t
    rw [h1, ← hm]
    exact (hp.symm.map _)


theorem ach_mono {ψ : ℕ → ℕ} {n m : ℕ∞} {σ : ℝ} {X : ℕ → ℕ → ℝ} (h : n ≤ m)
    (hX : AchievesRatio ψ m σ X) : AchievesRatio ψ n σ X := by
  obtain ⟨hf, hr⟩ := hX
  refine ⟨fun t ht1 htn => hf t ht1 (htn.trans h), fun t ht1 htn k hk => hr t ht1 (htn.trans h) k hk⟩

theorem ach_le_one {ψ : ℕ → ℕ} {n : ℕ∞} {σ : ℝ} {X : ℕ → ℕ → ℝ} (hn : 1 ≤ n)
    (hX : AchievesRatio ψ n σ X) : σ ≤ 1 := by
  obtain ⟨hf, hr⟩ := hX
  have h1 : ((1 : ℕ) : ℕ∞) ≤ n := by simpa using hn
  obtain ⟨h0, hs, -⟩ := hf 1 le_rfl h1
  have := hr 1 le_rfl h1 0 (by norm_num)
  simp at this hs
  linarith

theorem ach_down {ψ : ℕ → ℕ} {n : ℕ∞} {σ σ' : ℝ} {X : ℕ → ℕ → ℝ} (h : σ' ≤ σ)
    (hX : AchievesRatio ψ n σ X) : AchievesRatio ψ n σ' X := by
  obtain ⟨hf, hr⟩ := hX
  refine ⟨hf, fun t ht1 htn k hk => le_trans ?_ (hr t ht1 htn k hk)⟩
  have : (0 : ℝ) < t := by exact_mod_cast ht1
  exact div_le_div_of_nonneg_right h this.le

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    (∃ X, AchievesRatio (uniformCV d) ⊤ (uniformRatio d) X) ∧
    (∀ σ : ℝ, uniformRatio d < σ →
      ∃ n : ℕ, 1 ≤ n ∧ ¬ ∃ X, AchievesRatio (uniformCV d) (n : ℕ∞) σ X) ∧
    (⨅ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1) = uniformRatio d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (((d : ℝ) + 1) / d) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hdpos]; linarith
  have hD : (0 : ℝ) < ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d) := by positivity
  have hσs0 : 0 < uniformRatio d := by unfold uniformRatio; positivity
  have hσs1 : uniformRatio d * (((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d)) = 1 := by
    unfold uniformRatio; field_simp
  -- part 1
  have part1 : ∃ X, AchievesRatio (uniformCV d) ⊤ (uniformRatio d) X := by
    refine ffa_realizes (uniformCV d) ⊤ (uniformRatio d) hσs0.le ?_ |>.imp (fun X h => h.1)
    intro t ht1 _
    have hmono := ffaTotal_mono d hd (uniformRatio d) hσs0.le
    have hlim := eqE1 d hd (uniformRatio d)
    have : ffaTotal (uniformCV d) (uniformRatio d) t ≤
        uniformRatio d * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d) := by
      apply ge_of_tendsto hlim
      filter_upwards [Filter.eventually_ge_atTop t] with ℓ hℓ
      apply hmono
      nlinarith
    calc _ ≤ _ := this
      _ = 1 := by rw [mul_assoc]; exact hσs1
  -- part 2
  have part2 : ∀ σ : ℝ, uniformRatio d < σ →
      ∃ n : ℕ, 1 ≤ n ∧ ¬ ∃ X, AchievesRatio (uniformCV d) (n : ℕ∞) σ X := by
    intro σ hσ
    have hlim := eqE1 d hd σ
    have hgt : 1 < σ * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d) := by
      calc (1 : ℝ) = uniformRatio d * (((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d)) := hσs1.symm
        _ < σ * (((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d)) := by
          exact mul_lt_mul_of_pos_right hσ hD
        _ = _ := by ring
    have hev := hlim.eventually (lt_mem_nhds hgt)
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
    refine ⟨ℓ * (d + 1), by nlinarith, ?_⟩
    rintro ⟨X, hX⟩
    have := (thm1 (uniformCV d) ((ℓ * (d + 1) : ℕ) : ℕ∞) σ X (by
      have h0 : (0 : ℝ) < uniformRatio d := hσs0
      linarith) hX (ℓ * (d + 1)) (by nlinarith) le_rfl).2
    linarith
  -- part 3
  have hset : ∀ n : ℕ∞, 1 ≤ n → uniformRatio d ≤ fairnessRatio (uniformCV d) n := by
    intro n hn
    obtain ⟨X, hX⟩ := part1
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro σ ⟨Y, hY⟩
      exact ach_le_one hn hY
    · exact ⟨X, ach_mono le_top hX⟩
  refine ⟨part1, part2, ?_⟩
  haveI : Nonempty {n : ℕ∞ // 1 ≤ n} := ⟨⟨1, le_rfl⟩⟩
  have hbdd : BddBelow (Set.range fun n : {n : ℕ∞ // 1 ≤ n} => fairnessRatio (uniformCV d) n.1) := by
    refine ⟨uniformRatio d, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hset n.1 n.2
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    set m := ⨅ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1 with hm
    obtain ⟨n, hn1, hnX⟩ := part2 ((uniformRatio d + m) / 2) (by linarith)
    have hle : fairnessRatio (uniformCV d) (n : ℕ∞) ≤ (uniformRatio d + m) / 2 := by
      apply csSup_le
      · obtain ⟨X, hX⟩ := part1
        exact ⟨_, X, ach_mono le_top hX⟩
      · rintro s ⟨Y, hY⟩
        by_contra hs
        rw [not_le] at hs
        exact hnX ⟨Y, ach_down hs.le hY⟩
    have h2 : m ≤ fairnessRatio (uniformCV d) (n : ℕ∞) :=
      ciInf_le hbdd ⟨(n : ℕ∞), by exact_mod_cast hn1⟩
    linarith
  · exact le_ciInf (fun n => hset n.1 n.2)
