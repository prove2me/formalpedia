-- Prove2me | solution 1 for BestBothWorlds.SAO.union_event_adversarial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T08:06:33.591983+00:00
-- url     : https://prove2.me/submissions/1f9a16b5-b405-4bae-bf15-b7430b028d39

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Theorems.Thm_BestBothWorlds_SAO_estimate_concentration_adversarial
import Theorems.Thm_BestBothWorlds_SAO_pull_count_bound
import Theorems.Thm_BestBothWorlds_SAO_exp3p_phase_regret
import Definitions.Def_BestBothWorlds_SAO_RunNotation

set_option autoImplicit false

open MeasureTheory

namespace P8092e862

open BestBothWorlds.SAO

/-! ### The inner loop: only active arms are deactivated, with `τ = t` and `q = p`. -/

def Good {K : ℕ} (t : ℕ) (p : Fin K → ℝ) (A0 : Finset (Fin K)) (tau0 : Fin K → ℕ)
    (q0 : Fin K → ℝ) (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool) : Prop :=
  s.1 ⊆ A0 ∧ ∀ j, (j ∈ A0 → j ∉ s.1 → s.2.1 j = t ∧ s.2.2.1 j = p j) ∧
    (j ∈ s.1 ∨ j ∉ A0 → s.2.1 j = tau0 j ∧ s.2.2.1 j = q0 j)

theorem armStep_good (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (A0 : Finset (Fin K)) (tau0 : Fin K → ℕ) (q0 : Fin K → ℝ)
    (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool) (i : Fin K)
    (h : Good t p A0 tau0 q0 s) : Good t p A0 tau0 q0 (armStep K β t p Ht Hh T s i) := by
  obtain ⟨hsub, hj⟩ := h
  rcases s with ⟨A, tau, q, b⟩
  simp only at hsub hj
  dsimp only [armStep]
  split_ifs with hd
  · refine ⟨(Finset.erase_subset _ _).trans hsub, fun j => ?_⟩
    by_cases hji : j = i
    · subst hji
      refine ⟨fun _ _ => by simp, fun h => ?_⟩
      exfalso
      rcases h with h | h
      · simp at h
      · exact h (hsub hd.1)
    · simp only [Finset.mem_erase, Function.update_of_ne hji]
      refine ⟨fun h1 h2 => (hj j).1 h1 (fun h3 => h2 ⟨hji, h3⟩), fun h => (hj j).2 ?_⟩
      rcases h with h | h
      · exact Or.inl h.2
      · exact Or.inr h
  · exact ⟨hsub, hj⟩

theorem fold_good (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (A0 : Finset (Fin K)) (tau0 : Fin K → ℕ) (q0 : Fin K → ℝ) :
    ∀ (l : List (Fin K)) (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool),
      Good t p A0 tau0 q0 s → Good t p A0 tau0 q0 (l.foldl (armStep K β t p Ht Hh T) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons i l ih => intro s h; exact ih _ (armStep_good K β t p Ht Hh T A0 tau0 q0 s i h)

theorem good_init {K : ℕ} (t : ℕ) (p : Fin K → ℝ) (A0 : Finset (Fin K)) (tau0 : Fin K → ℕ)
    (q0 : Fin K → ℝ) : Good t p A0 tau0 q0 (A0, tau0, q0, false) :=
  ⟨subset_refl _, fun j => ⟨fun h1 h2 => absurd h1 h2, fun _ => ⟨rfl, rfl⟩⟩⟩

/-! ### One round of SAO. -/

theorem step_spec (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (hs : s.tau0 = none) :
    ∃ r : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool,
      Good (s.t + 1) s.p s.active s.tau s.q r ∧
      (saoStep K β s o).active = r.1 ∧ (saoStep K β s o).tau = r.2.1 ∧
      (saoStep K β s o).q = r.2.2.1 ∧ (saoStep K β s o).t = s.t + 1 ∧
      ((saoStep K β s o).tau0 = none ∨ (saoStep K β s o).tau0 = some (s.t + 1)) ∧
      (saoStep K β s o).p = fun i => if i ∈ r.1 then
          (1 - ∑ j ∈ Finset.univ \ r.1, r.2.2.1 j * r.2.1 j / (((s.t + 1 : ℕ) : ℝ) + 1)) / r.1.card
        else r.2.2.1 i * r.2.1 i / (((s.t + 1 : ℕ) : ℝ) + 1) := by
  obtain ⟨t, A, tau, q, p, G1, G2, T, tau0⟩ := s
  simp only at hs
  subst hs
  exact ⟨_, fold_good K β (t + 1) p _ _ _ A tau q (List.finRange K) _ (good_init _ _ _ _ _),
    rfl, rfl, rfl, rfl, by dsimp only [saoStep]; split_ifs <;> simp, rfl⟩

theorem step_frozen (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (τ : ℕ)
    (hs : s.tau0 = some τ) : saoStep K β s o = s := by
  obtain ⟨t, A, tau, q, p, G1, G2, T, tau0⟩ := s
  simp only at hs
  subst hs
  rfl

/-! ### The invariant. -/

noncomputable def W {K : ℕ} (s : SAOState K) : ℝ :=
  ∑ j ∈ Finset.univ \ s.active, s.q j * (s.tau j : ℝ)

def Inv {K : ℕ} (s : SAOState K) : Prop :=
  (∀ j, j ∉ s.active → s.tau j ≤ s.t ∧ 0 ≤ s.q j) ∧
  (∀ τ, s.tau0 = some τ → τ ≤ s.t) ∧
  0 ≤ W s ∧ W s ≤ (s.t : ℝ) + 1 ∧
  (∀ i ∈ s.active, s.p i =
    (1 - ∑ j ∈ Finset.univ \ s.active, s.q j * s.tau j / ((s.t : ℝ) + 1)) / s.active.card)

theorem sum_eq_W {K : ℕ} (s : SAOState K) :
    ∑ j ∈ Finset.univ \ s.active, s.q j * s.tau j / ((s.t : ℝ) + 1) = W s / ((s.t : ℝ) + 1) := by
  rw [W, Finset.sum_div]

theorem inv_p_bounds {K : ℕ} (s : SAOState K) (h : Inv s) (i : Fin K) (hi : i ∈ s.active) :
    0 ≤ s.p i ∧ s.p i ≤ 1 / (s.active.card : ℝ) := by
  obtain ⟨_, _, hW0, hW1, hp⟩ := h
  rw [hp i hi, sum_eq_W]
  have ht : (0 : ℝ) < (s.t : ℝ) + 1 := by positivity
  have h1 : W s / ((s.t : ℝ) + 1) ≤ 1 := by rw [div_le_one ht]; exact hW1
  have h2 : 0 ≤ W s / ((s.t : ℝ) + 1) := div_nonneg hW0 ht.le
  constructor
  · apply div_nonneg <;> [linarith; positivity]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

theorem inv_init (K n : ℕ) : Inv (SAOState.init K n) := by
  refine ⟨fun j hj => by simp [SAOState.init] at hj, fun τ h => by simp [SAOState.init] at h,
    by simp [W, SAOState.init], by simp [W, SAOState.init], fun i _ => by simp [SAOState.init]⟩

theorem inv_step (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : Inv s) :
    Inv (saoStep K β s o) := by
  cases hs : s.tau0 with
  | some τ => rw [step_frozen K β s o τ hs]; exact h
  | none =>
    obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, ht, hz, hP⟩ := step_spec K β s o hs
    have hpb := inv_p_bounds s h
    obtain ⟨h1, h2, hW0, hW1, hp⟩ := h
    -- new W
    have hWeq : W (saoStep K β s o) =
        ∑ j ∈ (Finset.univ \ r.1) \ (Finset.univ \ s.active), s.p j * ((s.t : ℝ) + 1) + W s := by
      have hss : Finset.univ \ s.active ⊆ Finset.univ \ r.1 :=
        Finset.sdiff_subset_sdiff (subset_refl _) hsub
      rw [W, hA, hT, hQ, ← Finset.sum_sdiff hss, W]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
        obtain ⟨e1, e2⟩ := (hg j).1 hj.2 hj.1
        rw [e1, e2]; push_cast; ring
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
        obtain ⟨e1, e2⟩ := (hg j).2 (Or.inr hj)
        rw [e1, e2]
    set D := (Finset.univ \ r.1) \ (Finset.univ \ s.active) with hD
    have hDA : D ⊆ s.active := by
      intro j hj
      simp only [hD, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
      exact hj.2
    set P := (1 - W s / ((s.t : ℝ) + 1)) / (s.active.card : ℝ) with hPdef
    have htpos : (0 : ℝ) < (s.t : ℝ) + 1 := by positivity
    have hP0 : 0 ≤ 1 - W s / ((s.t : ℝ) + 1) := by
      have : W s / ((s.t : ℝ) + 1) ≤ 1 := by rw [div_le_one htpos]; exact hW1
      linarith
    have hsumD : ∑ j ∈ D, s.p j * ((s.t : ℝ) + 1) = (D.card : ℝ) * P * ((s.t : ℝ) + 1) := by
      rw [Finset.sum_congr rfl (fun j hj => by rw [hp j (hDA hj), sum_eq_W]),
        Finset.sum_const, nsmul_eq_mul, hPdef]
      ring
    have hcardP : (D.card : ℝ) * P ≤ 1 - W s / ((s.t : ℝ) + 1) := by
      have hc : (D.card : ℝ) ≤ s.active.card := by exact_mod_cast Finset.card_le_card hDA
      rcases Nat.eq_zero_or_pos s.active.card with h0 | h0
      · have : D.card = 0 := by
          have := Finset.card_le_card hDA; omega
        rw [this, Nat.cast_zero, zero_mul]; exact hP0
      · have hAc : (0 : ℝ) < s.active.card := by exact_mod_cast h0
        calc (D.card : ℝ) * P ≤ (s.active.card : ℝ) * P :=
              mul_le_mul_of_nonneg_right hc (div_nonneg hP0 hAc.le)
          _ = 1 - W s / ((s.t : ℝ) + 1) := by rw [hPdef]; field_simp
    have hDnn : 0 ≤ (D.card : ℝ) * P := mul_nonneg (by positivity) (div_nonneg hP0 (by positivity))
    have hmain : (D.card : ℝ) * P * ((s.t : ℝ) + 1) ≤ (s.t : ℝ) + 1 - W s := by
      have := mul_le_mul_of_nonneg_right hcardP htpos.le
      rw [sub_mul, div_mul_cancel₀ _ htpos.ne'] at this
      linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hA] at hj
      rw [hT, hQ, ht]
      by_cases hjA : j ∈ s.active
      · obtain ⟨e1, e2⟩ := (hg j).1 hjA hj
        rw [e1, e2]
        exact ⟨le_refl _, (hpb j hjA).1⟩
      · obtain ⟨e1, e2⟩ := (hg j).2 (Or.inr hjA)
        rw [e1, e2]
        obtain ⟨a1, a2⟩ := h1 j hjA
        exact ⟨by omega, a2⟩
    · intro τ hτ
      rw [ht]
      rcases hz with hz | hz
      · rw [hz] at hτ; exact absurd hτ (by simp)
      · rw [hz] at hτ; simp at hτ; omega
    · rw [hWeq, hsumD]; have := mul_nonneg hDnn htpos.le; linarith
    · rw [hWeq, hsumD, ht]; push_cast; linarith
    · intro i hi
      rw [hP, hA, hT, hQ, ht]
      rw [hA] at hi
      simp only [hi, if_true]

theorem inv_fold (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), Inv s → Inv (l.foldl (saoStep K β) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o l ih => intro s h; exact ih _ (inv_step K β s o h)

theorem t_fold (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), (l.foldl (saoStep K β) s).t ≤ s.t + l.length := by
  intro l
  induction l with
  | nil => intro s; simp
  | cons o l ih =>
    intro s
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (saoStep K β s o)
    have h2 : (saoStep K β s o).t ≤ s.t + 1 := by
      cases hs : s.tau0 with
      | some τ => rw [step_frozen K β s o τ hs]; omega
      | none =>
        obtain ⟨r, _, _, _, _, ht, _⟩ := step_spec K β s o hs
        omega
    omega

theorem persist_fold (K : ℕ) (β : ℝ) (k : Fin K) :
    ∀ (l : History K) (s : SAOState K), k ∉ s.active →
      k ∉ (l.foldl (saoStep K β) s).active ∧ (l.foldl (saoStep K β) s).tau k = s.tau k := by
  intro l
  induction l with
  | nil => intro s h; exact ⟨h, rfl⟩
  | cons o l ih =>
    intro s h
    simp only [List.foldl_cons]
    have hstep : k ∉ (saoStep K β s o).active ∧ (saoStep K β s o).tau k = s.tau k := by
      cases hs : s.tau0 with
      | some τ => rw [step_frozen K β s o τ hs]; exact ⟨h, rfl⟩
      | none =>
        obtain ⟨r, ⟨hsub, hg⟩, hA, hT, _⟩ := step_spec K β s o hs
        rw [hA, hT]
        exact ⟨fun hk => h (hsub hk), ((hg k).2 (Or.inr h)).1⟩
    obtain ⟨a, b⟩ := ih _ hstep.1
    exact ⟨a, b.trans hstep.2⟩

theorem frozen_fold (K : ℕ) (β : ℝ) (τ : ℕ) :
    ∀ (l : History K) (s : SAOState K), s.tau0 = some τ → l.foldl (saoStep K β) s = s := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons o l ih =>
    intro s h
    simp only [List.foldl_cons]
    rw [step_frozen K β s o τ h]
    exact ih s h

theorem later (K n : ℕ) (β : ℝ) (l : History K) (r m : ℕ) (hrm : r ≤ m) :
    ∃ l' : History K, saoState K n β (l.take m) =
      l'.foldl (saoStep K β) (saoState K n β (l.take r)) := by
  refine ⟨(l.take m).drop r, ?_⟩
  unfold saoState
  rw [← List.foldl_append]
  congr 1
  conv_lhs => rw [← List.take_append_drop r (l.take m)]
  rw [List.take_take, Nat.min_eq_left hrm]

/-! ### Harmonic bound. -/

/-! ### New: persistence with `q`, the second invariant. -/

theorem persist_fold2 (K : ℕ) (β : ℝ) (k : Fin K) :
    ∀ (l : History K) (s : SAOState K), k ∉ s.active →
      k ∉ (l.foldl (saoStep K β) s).active ∧ (l.foldl (saoStep K β) s).tau k = s.tau k ∧
        (l.foldl (saoStep K β) s).q k = s.q k := by
  intro l
  induction l with
  | nil => intro s h; exact ⟨h, rfl, rfl⟩
  | cons o l ih =>
    intro s h
    simp only [List.foldl_cons]
    have hstep : k ∉ (saoStep K β s o).active ∧ (saoStep K β s o).tau k = s.tau k ∧
        (saoStep K β s o).q k = s.q k := by
      cases hs : s.tau0 with
      | some τ => rw [step_frozen K β s o τ hs]; exact ⟨h, rfl, rfl⟩
      | none =>
        obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, _⟩ := step_spec K β s o hs
        rw [hA, hT, hQ]
        exact ⟨fun hk => h (hsub hk), ((hg k).2 (Or.inr h)).1, ((hg k).2 (Or.inr h)).2⟩
    obtain ⟨a, b, c⟩ := ih _ hstep.1
    exact ⟨a, b.trans hstep.2.1, c.trans hstep.2.2⟩

def Inv2 {K : ℕ} (n : ℕ) (s : SAOState K) : Prop :=
  W s ≤ ((s.t : ℝ) + 1) * (1 - (s.active.card : ℝ) / K) ∧ ∀ j ∈ s.active, s.tau j = n

theorem inv2_init (K n : ℕ) (hK : 0 < K) : Inv2 n (SAOState.init K n) := by
  refine ⟨?_, fun j _ => rfl⟩
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  simp [W, SAOState.init, Finset.card_univ, Fintype.card_fin, div_self hK']

theorem inv2_step (K n : ℕ) (hK : 0 < K) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : Inv s)
    (h2 : Inv2 n s) : Inv2 n (saoStep K β s o) := by
  cases hs : s.tau0 with
  | some τ => rw [step_frozen K β s o τ hs]; exact h2
  | none =>
    obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, ht, hz, hP⟩ := step_spec K β s o hs
    obtain ⟨h1, _, hW0, hW1, hp⟩ := h
    obtain ⟨hI, hn⟩ := h2
    refine ⟨?_, ?_⟩
    swap
    · intro j hj
      rw [hA] at hj
      rw [hT, ((hg j).2 (Or.inl hj)).1]
      exact hn j (hsub hj)
    have hWeq : W (saoStep K β s o) =
        ∑ j ∈ (Finset.univ \ r.1) \ (Finset.univ \ s.active), s.p j * ((s.t : ℝ) + 1) + W s := by
      have hss : Finset.univ \ s.active ⊆ Finset.univ \ r.1 :=
        Finset.sdiff_subset_sdiff (subset_refl _) hsub
      rw [W, hA, hT, hQ, ← Finset.sum_sdiff hss, W]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
        obtain ⟨e1, e2⟩ := (hg j).1 hj.2 hj.1
        rw [e1, e2]; push_cast; ring
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
        obtain ⟨e1, e2⟩ := (hg j).2 (Or.inr hj)
        rw [e1, e2]
    set D := (Finset.univ \ r.1) \ (Finset.univ \ s.active) with hD
    have hDA : D ⊆ s.active := by
      intro j hj
      simp only [hD, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
      exact hj.2
    have hDeq : D = s.active \ r.1 := by
      ext j; simp only [hD, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]; tauto
    have hcard : (r.1.card : ℝ) = s.active.card - D.card := by
      rw [hDeq, Finset.card_sdiff_of_subset hsub]
      have := Finset.card_le_card hsub
      push_cast [this]; ring
    set c : ℝ := (s.t : ℝ) + 1 with hc
    have hcpos : 0 < c := by positivity
    set y : ℝ := 1 - W s / c with hy
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hya : (s.active.card : ℝ) / K ≤ y := by
      rw [hy]
      have : W s / c ≤ 1 - (s.active.card : ℝ) / K := by
        rw [div_le_iff₀ hcpos]; linarith
      linarith
    have hsumD : ∑ j ∈ D, s.p j * c = (D.card : ℝ) * (y / s.active.card) * c := by
      rw [Finset.sum_congr rfl (fun j hj => by rw [hp j (hDA hj), sum_eq_W]),
        Finset.sum_const, nsmul_eq_mul]
      rw [hy, hc]; ring
    have hrK : (r.1.card : ℝ) ≤ K := by
      have := Finset.card_le_univ r.1
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hnn : 0 ≤ 1 - (r.1.card : ℝ) / K := by
      rw [sub_nonneg, div_le_one hKpos]; exact hrK
    rw [hWeq, hsumD, hA, ht]
    have hWs : W s = c * (1 - y) := by rw [hy]; field_simp; ring
    have key : W s + (D.card : ℝ) * (y / s.active.card) * c ≤ c * (1 - (r.1.card : ℝ) / K) := by
      rcases Nat.eq_zero_or_pos s.active.card with h0 | h0
      · have hD0 : D.card = 0 := by have := Finset.card_le_card hDA; omega
        have hr0 : r.1.card = 0 := by have := Finset.card_le_card hsub; omega
        rw [hr0, hD0]
        simp only [Nat.cast_zero, zero_mul, add_zero, zero_div, sub_zero, mul_one]
        exact hW1
      · have hApos : (0 : ℝ) < s.active.card := by exact_mod_cast h0
        have hDle : (D.card : ℝ) ≤ s.active.card := by exact_mod_cast Finset.card_le_card hDA
        rw [hWs, hcard]
        have e1 : 1 / (K : ℝ) ≤ y / s.active.card := by
          rw [div_le_div_iff₀ hKpos hApos]
          have := (div_le_iff₀ hKpos).1 hya
          linarith
        have e2 : c * (1 - y) + (D.card : ℝ) * (y / s.active.card) * c =
            c * (1 - (s.active.card - D.card) * (y / s.active.card)) := by
          have ha : (s.active.card : ℝ) * (y / s.active.card) = y := by
            rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hApos.ne', mul_one]
          linear_combination c * ha
        rw [e2]
        have e3 : ((s.active.card : ℝ) - D.card) * (1 / K) ≤
            ((s.active.card : ℝ) - D.card) * (y / s.active.card) :=
          mul_le_mul_of_nonneg_left e1 (by linarith)
        have e4 : ((s.active.card : ℝ) - D.card) / K = ((s.active.card : ℝ) - D.card) * (1 / K) := by
          ring
        rw [e4]
        nlinarith
    push_cast
    calc (D.card : ℝ) * (y / s.active.card) * c + W s ≤ c * (1 - (r.1.card : ℝ) / K) := by
          linarith [key]
      _ ≤ (c + 1) * (1 - (r.1.card : ℝ) / K) := by nlinarith

theorem inv12_fold (K n : ℕ) (hK : 0 < K) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), Inv s → Inv2 n s →
      Inv (l.foldl (saoStep K β) s) ∧ Inv2 n (l.foldl (saoStep K β) s) := by
  intro l
  induction l with
  | nil => intro s h h2; exact ⟨h, h2⟩
  | cons o l ih =>
    intro s h h2
    exact ih _ (inv_step K β s o h) (inv2_step K n hK β s o h h2)

theorem active_p_ge (K n : ℕ) (hK : 0 < K) (s : SAOState K) (h : Inv s) (h2 : Inv2 n s)
    (i : Fin K) (hi : i ∈ s.active) : 1 / (K : ℝ) ≤ s.p i := by
  obtain ⟨_, _, _, _, hp⟩ := h
  rw [hp i hi, sum_eq_W]
  have hcpos : (0 : ℝ) < (s.t : ℝ) + 1 := by positivity
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hApos : (0 : ℝ) < s.active.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
  have : W s / ((s.t : ℝ) + 1) ≤ 1 - (s.active.card : ℝ) / K := by
    rw [div_le_iff₀ hcpos]; linarith [h2.1]
  rw [div_le_div_iff₀ hKpos hApos]
  have h3 : (s.active.card : ℝ) / K * K = s.active.card := by field_simp
  nlinarith

/-! ### The inner loop: tracing one arm. -/

abbrev St (K : ℕ) := Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool

def fire (K : ℕ) (β : ℝ) (t : ℕ) (Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s' : St K) (i : Fin K) :
    Prop :=
  (1 ≤ T i ∧
    |Ht i - Hh i| > Real.sqrt (2 * Real.log β / T i) +
      Real.sqrt (4 * (K * (min (s'.2.1 i) t : ℕ) / (t : ℝ) ^ 2 +
        ((t : ℝ) - (min (s'.2.1 i) t : ℕ)) / (s'.2.2.1 i * s'.2.1 i * t)) *
        Real.log β + 5 * (K * Real.log β / (min (s'.2.1 i) t : ℕ)) ^ 2)) ∨
  (i ∉ s'.1 ∧ 2 ≤ s'.2.1 i ∧ maxOver s'.1 Ht - Ht i > 10 * width K β ((s'.2.1 i : ℝ) - 1)) ∨
  (i ∉ s'.1 ∧ maxOver s'.1 Ht - Ht i ≤ 2 * width K β (s'.2.1 i))

theorem armStep_flag (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (i : Fin K) (h : (armStep K β t p Ht Hh T s i).2.2.2 = true) :
    s.2.2.2 = true ∨ fire K β t Ht Hh T (armStep K β t p Ht Hh T s i) i := by
  rcases s with ⟨A, tau, q, b⟩
  unfold armStep at h ⊢
  unfold fire
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

theorem armStep_shrink (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (i : Fin K) : (armStep K β t p Ht Hh T s i).1 ⊆ s.1 := by
  rcases s with ⟨A, tau, q, b⟩
  unfold armStep
  dsimp only
  split_ifs
  · exact Finset.erase_subset _ _
  · exact subset_refl _

theorem armStep_other (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (i k : Fin K) (hik : i ≠ k) : k ∈ (armStep K β t p Ht Hh T s i).1 ↔ k ∈ s.1 := by
  rcases s with ⟨A, tau, q, b⟩
  unfold armStep
  dsimp only
  split_ifs
  · rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨fun e => hik e.symm, h⟩⟩
  · exact Iff.rfl

theorem armStep_self (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (k : Fin K) (hk : k ∈ s.1) :
    k ∉ (armStep K β t p Ht Hh T s k).1 ↔ maxOver s.1 Ht - Ht k > 6 * width K β t := by
  rcases s with ⟨A, tau, q, b⟩
  unfold armStep
  dsimp only at hk ⊢
  by_cases hd : k ∈ A ∧ maxOver A Ht - Ht k > 6 * width K β t
  · rw [if_pos hd]; simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true, true_iff]; exact hd.2
  · rw [if_neg hd]
    constructor
    · intro h; exact absurd hk h
    · intro h; exact absurd ⟨hk, h⟩ hd

theorem fold_shrink (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) :
    ∀ (l : List (Fin K)) (s : St K), (l.foldl (armStep K β t p Ht Hh T) s).1 ⊆ s.1 := by
  intro l
  induction l with
  | nil => intro s; exact subset_refl _
  | cons i l ih => intro s; exact (ih _).trans (armStep_shrink K β t p Ht Hh T s i)

theorem fold_other (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (k : Fin K) :
    ∀ (l : List (Fin K)) (s : St K), k ∉ l →
      (k ∈ (l.foldl (armStep K β t p Ht Hh T) s).1 ↔ k ∈ s.1) := by
  intro l
  induction l with
  | nil => intro s _; exact Iff.rfl
  | cons i l ih =>
    intro s hk
    simp only [List.mem_cons, not_or] at hk
    simp only [List.foldl_cons]
    rw [ih _ hk.2]
    exact armStep_other K β t p Ht Hh T s i k (fun e => hk.1 e.symm)

theorem fold_trace (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (k : Fin K) :
    ∀ (l : List (Fin K)) (s0 : St K), l.Nodup → k ∈ l →
      ∃ s : St K, (∃ l1 : List (Fin K), s = l1.foldl (armStep K β t p Ht Hh T) s0) ∧
        (k ∈ s.1 ↔ k ∈ s0.1) ∧
        (l.foldl (armStep K β t p Ht Hh T) s0).1 ⊆ (armStep K β t p Ht Hh T s k).1 ∧
        (k ∈ (armStep K β t p Ht Hh T s k).1 ↔ k ∈ (l.foldl (armStep K β t p Ht Hh T) s0).1) := by
  intro l
  induction l with
  | nil => intro s0 _ hk; simp at hk
  | cons a l ih =>
    intro s0 hnd hk
    rw [List.nodup_cons] at hnd
    by_cases hka : k = a
    · subst hka
      refine ⟨s0, ⟨[], rfl⟩, Iff.rfl, ?_, ?_⟩
      · simp only [List.foldl_cons]; exact fold_shrink K β t p Ht Hh T l _
      · simp only [List.foldl_cons]; exact (fold_other K β t p Ht Hh T k l _ hnd.1).symm
    · have hkl : k ∈ l := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h hka
        · exact h
      obtain ⟨s, ⟨l1, hs⟩, h1, h2, h3⟩ := ih (armStep K β t p Ht Hh T s0 a) hnd.2 hkl
      refine ⟨s, ⟨a :: l1, by simp [hs]⟩, ?_, ?_, ?_⟩
      · rw [h1]; exact armStep_other K β t p Ht Hh T s0 a k (fun e => hka e.symm)
      · simpa using h2
      · simpa using h3

theorem fold_flag (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) :
    ∀ (l : List (Fin K)) (s0 : St K), s0.2.2.2 = false →
      (l.foldl (armStep K β t p Ht Hh T) s0).2.2.2 = true →
      ∃ s : St K, ∃ k : Fin K, (∃ l1 : List (Fin K), s = l1.foldl (armStep K β t p Ht Hh T) s0) ∧
        (l.foldl (armStep K β t p Ht Hh T) s0).1 ⊆ (armStep K β t p Ht Hh T s k).1 ∧
        fire K β t Ht Hh T (armStep K β t p Ht Hh T s k) k := by
  intro l
  induction l with
  | nil =>
    intro s0 h0 h
    simp only [List.foldl_nil] at h
    rw [h0] at h
    exact absurd h (by decide)
  | cons a l ih =>
    intro s0 h0 h
    simp only [List.foldl_cons] at h ⊢
    cases hb : (armStep K β t p Ht Hh T s0 a).2.2.2 with
    | true =>
      rcases armStep_flag K β t p Ht Hh T s0 a hb with h1 | h1
      · rw [h0] at h1; simp at h1
      · exact ⟨s0, a, ⟨[], rfl⟩, fold_shrink K β t p Ht Hh T l _, h1⟩
    | false =>
      obtain ⟨s, k, ⟨l1, hs⟩, h2, h3⟩ := ih _ hb h
      exact ⟨s, k, ⟨a :: l1, by simp [hs]⟩, h2, h3⟩

/-! ### One round, explicitly. -/

noncomputable def HtF (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) : Fin K → ℝ :=
  fun i => (saoStep K β s o).Gtil i / ((s.t + 1 : ℕ) : ℝ)

noncomputable def HhF (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) : Fin K → ℝ :=
  fun i => (saoStep K β s o).Ghat i / ((saoStep K β s o).T i : ℝ)

noncomputable def rnd (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) : St K :=
  (List.finRange K).foldl
    (armStep K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o) (saoStep K β s o).T)
    (s.active, s.tau, s.q, false)

theorem step_fold (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (hs : s.tau0 = none) :
    (saoStep K β s o).active = (rnd K β s o).1 ∧ (saoStep K β s o).tau = (rnd K β s o).2.1 ∧
    (saoStep K β s o).q = (rnd K β s o).2.2.1 ∧
    (saoStep K β s o).tau0 = (if (rnd K β s o).2.2.2 then some (s.t + 1) else none) ∧
    (saoStep K β s o).t = s.t + 1 ∧
    (saoStep K β s o).Gtil = (fun i => s.Gtil i + (if o.1 = i then o.2 / s.p i else 0)) ∧
    (saoStep K β s o).Ghat = (fun i => s.Ghat i + (if o.1 = i then o.2 else 0)) ∧
    (saoStep K β s o).T = (fun i => s.T i + (if o.1 = i then 1 else 0)) := by
  obtain ⟨t, A, tau, q, p, G1, G2, T, tau0⟩ := s
  simp only at hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### The run along a path. -/

theorem take_succ_hist {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (u : ℕ) (h : u < n) :
    (history adv I).take (u + 1) =
      (history adv I).take u ++ [(I ⟨u, h⟩, reward adv I ⟨u, h⟩ (I ⟨u, h⟩))] := by
  rw [List.take_succ]
  congr 1
  simp [history, h]

theorem sum_succ {n : ℕ} {M : Type} [AddCommMonoid M] (g : Fin n → M) (P : Fin n → Prop)
    [DecidablePred P] (u : ℕ) (h : u < n) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u + 1 ∧ P r), g r =
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u ∧ P r), g r +
        (if P ⟨u, h⟩ then g ⟨u, h⟩ else 0) := by
  have hpt : ∀ r : Fin n, (if (r : ℕ) < u + 1 ∧ P r then g r else 0) =
      (if (r : ℕ) < u ∧ P r then g r else 0) +
        (if (⟨u, h⟩ : Fin n) = r then (if P r then g r else 0) else 0) := by
    intro r
    by_cases hr : (⟨u, h⟩ : Fin n) = r
    · subst hr; simp
    · have hne : (r : ℕ) ≠ u := fun e => hr (Fin.ext e.symm)
      have e2 : ((r : ℕ) < u + 1) ↔ ((r : ℕ) < u) := by omega
      simp only [hr, if_false, add_zero, e2]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_congr rfl (fun r _ => hpt r),
    Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem sao_eq (K n : ℕ) (β : ℝ) (h : History K) (hh : (saoState K n β h).tau0 = none) :
    sao K n β h = (saoState K n β h).p := by
  unfold sao; rw [hh]

theorem track (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) :
    ∀ u, u ≤ n → (∀ v < u, (saoState K n β ((history adv I).take v)).tau0 = none) →
      (saoState K n β ((history adv I).take u)).t = u ∧
      ∀ i, (saoState K n β ((history adv I).take u)).Gtil i = estReward (sao K n β) adv I i u ∧
        (saoState K n β ((history adv I).take u)).Ghat i = algReward adv I i u ∧
        (saoState K n β ((history adv I).take u)).T i = pullCount I i u := by
  intro u
  induction u with
  | zero =>
    intro _ _
    refine ⟨rfl, fun i => ⟨?_, ?_, ?_⟩⟩ <;>
      simp [saoState, SAOState.init, estReward, algReward, pullCount]
  | succ u ih =>
    intro hu hlt
    have hun : u < n := by omega
    obtain ⟨iht, ihg⟩ := ih (by omega) (fun v hv => hlt v (by omega))
    have hnone := hlt u (by omega)
    have hS : saoState K n β ((history adv I).take (u + 1)) =
        saoStep K β (saoState K n β ((history adv I).take u))
          (I ⟨u, hun⟩, reward adv I ⟨u, hun⟩ (I ⟨u, hun⟩)) := by
      unfold saoState; rw [take_succ_hist adv I u hun, List.foldl_append]; rfl
    obtain ⟨_, _, _, _, ht, hG, hGh, hT⟩ := step_fold K β _ (I ⟨u, hun⟩, reward adv I ⟨u, hun⟩ (I ⟨u, hun⟩)) hnone
    rw [hS, ht, hG, hGh, hT, iht]
    refine ⟨rfl, fun i => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨e, -, -⟩ := ihg i
      dsimp only
      rw [e, estReward, estReward, sum_succ _ (fun r : Fin n => I r = i) u hun]
      congr 1
      by_cases hi : I ⟨u, hun⟩ = i
      · rw [if_pos hi, if_pos hi]
        have hp : probAt (sao K n β) adv I ((⟨u, hun⟩ : Fin n) + 1) =
            (saoState K n β ((history adv I).take u)).p := by
          unfold probAt
          simp only [Nat.add_sub_cancel]
          exact sao_eq K n β _ hnone
        rw [hp, hi]
      · rw [if_neg hi, if_neg hi]
    · obtain ⟨-, e, -⟩ := ihg i
      dsimp only
      rw [e, algReward, algReward, sum_succ _ (fun r : Fin n => I r = i) u hun]
      congr 1
      by_cases hi : I ⟨u, hun⟩ = i
      · rw [if_pos hi, if_pos hi, hi]
      · rw [if_neg hi, if_neg hi]
    · obtain ⟨-, -, e⟩ := ihg i
      dsimp only
      rw [e, pullCount, pullCount, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
        sum_succ _ (fun r : Fin n => I r = i) u hun]

/-! ### Algebra of the radii. -/

theorem width_anti (K : ℕ) (β : ℝ) (hL : 0 ≤ Real.log β) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    width K β y ≤ width K β x := by
  unfold width
  apply Real.sqrt_le_sqrt
  have hKL : 0 ≤ (K : ℝ) * Real.log β := mul_nonneg (Nat.cast_nonneg _) hL
  have h1 : 4 * K * Real.log β / y ≤ 4 * K * Real.log β / x := by
    apply div_le_div_of_nonneg_left (by nlinarith) hx hxy
  have h2 : K * Real.log β / y ≤ K * Real.log β / x :=
    div_le_div_of_nonneg_left hKL hx hxy
  have h3 : 0 ≤ K * Real.log β / y := div_nonneg hKL (by linarith)
  have h4 : (K * Real.log β / y) ^ 2 ≤ (K * Real.log β / x) ^ 2 := pow_le_pow_left₀ h3 h2 2
  linarith

theorem width_nonneg (K : ℕ) (β x : ℝ) : 0 ≤ width K β x := Real.sqrt_nonneg _

theorem rad_eq (K : ℕ) (β : ℝ) (τ : ℕ) (q : ℝ) (t : ℕ) (ht : 1 ≤ t) (hτ : t ≤ τ) :
    estRadius K τ q t (Real.log β) = width K β t := by
  unfold estRadius width
  have hmin : min τ t = t := Nat.min_eq_right hτ
  have hmax : max ((t : ℝ) - τ) 0 = 0 := by
    apply max_eq_right
    have : (t : ℝ) ≤ τ := by exact_mod_cast hτ
    linarith
  rw [hmin, hmax]
  congr 1
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  field_simp
  ring

theorem rad_eq' (K : ℕ) (β : ℝ) (τ' : ℕ) (q : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    Real.sqrt (4 * (K * (t : ℝ) / (t : ℝ) ^ 2 + ((t : ℝ) - (t : ℝ)) / (q * τ' * t)) *
        Real.log β + 5 * (K * Real.log β / (t : ℝ)) ^ 2) = width K β t := by
  unfold width
  congr 1
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  rw [sub_self, zero_div, add_zero]
  field_simp

theorem rad_le (K : ℕ) (hK : 0 < K) (β : ℝ) (hL : 0 ≤ Real.log β) (τ : ℕ) (q : ℝ) (t : ℕ)
    (hτ1 : 1 ≤ τ) (hτ : τ ≤ t) (hq : 1 / (K : ℝ) ≤ q) :
    estRadius K τ q t (Real.log β) ≤ width K β τ := by
  unfold estRadius width
  have hmin : min τ t = τ := Nat.min_eq_left hτ
  have hτt : (τ : ℝ) ≤ t := by exact_mod_cast hτ
  have hmax : max ((t : ℝ) - τ) 0 = (t : ℝ) - τ := max_eq_left (by linarith)
  rw [hmin, hmax]
  apply Real.sqrt_le_sqrt
  have hτp : (0 : ℝ) < τ := by exact_mod_cast hτ1
  have htp : (0 : ℝ) < t := by linarith
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  have hqp : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hiq : 1 / q ≤ K := by
    rw [div_le_iff₀ hqp]
    have := (div_le_iff₀ hKp).1 hq
    linarith
  have e1 : ((t : ℝ) - τ) / (q * τ * t) = (1 / q) * (((t : ℝ) - τ) / (τ * t)) := by
    field_simp
  have hnn : 0 ≤ ((t : ℝ) - τ) / (τ * t) := div_nonneg (by linarith) (by positivity)
  have e2 : (1 / q) * (((t : ℝ) - τ) / (τ * t)) ≤ K * (((t : ℝ) - τ) / (τ * t)) :=
    mul_le_mul_of_nonneg_right hiq hnn
  have e3 : (K : ℝ) / τ - (K * τ / (t : ℝ) ^ 2 + K * (((t : ℝ) - τ) / (τ * t))) =
      K * ((t : ℝ) - τ) / (t : ℝ) ^ 2 := by
    field_simp; ring
  have e4 : 0 ≤ K * ((t : ℝ) - τ) / (t : ℝ) ^ 2 := div_nonneg (by nlinarith) (by positivity)
  have key : K * (τ : ℝ) / (t : ℝ) ^ 2 + ((t : ℝ) - τ) / (q * τ * t) ≤ K / τ := by
    rw [e1]; linarith
  have e5 : 4 * K * Real.log β / τ = 4 * ((K : ℝ) / τ) * Real.log β := by ring
  rw [e5]
  have := mul_le_mul_of_nonneg_right key hL
  nlinarith

theorem le_maxOver {K : ℕ} (A : Finset (Fin K)) (f : Fin K → ℝ) (j : Fin K) (hj : j ∈ A) :
    f j ≤ maxOver A f := by
  unfold maxOver
  rw [dif_pos ⟨j, hj⟩]
  exact Finset.le_sup' f hj

theorem maxOver_mem {K : ℕ} (A : Finset (Fin K)) (f : Fin K → ℝ) (hA : A.Nonempty) :
    ∃ j ∈ A, maxOver A f = f j := by
  unfold maxOver
  rw [dif_pos hA]
  obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' hA f
  exact ⟨j, hj, e⟩

/-! ### Round-level facts. -/

theorem rnd_good (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) :
    Good (s.t + 1) s.p s.active s.tau s.q (rnd K β s o) := by
  unfold rnd
  exact fold_good K β _ _ _ _ _ _ _ _ _ _ (good_init _ _ _ _ _)

theorem rnd_deact (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (k : Fin K)
    (hk : k ∈ s.active) (hk' : k ∉ (rnd K β s o).1) :
    ∃ j ∈ s.active, HtF K β s o j - HtF K β s o k > 6 * width K β ((s.t + 1 : ℕ) : ℝ) := by
  unfold rnd at hk'
  obtain ⟨s', ⟨l1, hs⟩, h1, -, h3⟩ := fold_trace K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
    (saoStep K β s o).T k (List.finRange K) (s.active, s.tau, s.q, false)
    (List.nodup_finRange K) (List.mem_finRange k)
  have hks : k ∈ s'.1 := h1.2 hk
  have hks' : k ∉ (armStep K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
      (saoStep K β s o).T s' k).1 := fun h => hk' (h3.1 h)
  have hd := (armStep_self K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o) _ s' k hks).1 hks'
  have hgood : Good (s.t + 1) s.p s.active s.tau s.q s' := by
    rw [hs]; exact fold_good K β _ _ _ _ _ _ _ _ l1 _ (good_init _ _ _ _ _)
  obtain ⟨j, hj, e⟩ := maxOver_mem s'.1 (HtF K β s o) ⟨k, hks⟩
  rw [e] at hd
  exact ⟨j, hgood.1 hj, hd⟩

theorem rnd_keep (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (k j : Fin K)
    (hk : k ∈ s.active) (hk' : k ∈ (rnd K β s o).1) (hj : j ∈ (rnd K β s o).1) :
    HtF K β s o j - HtF K β s o k ≤ 6 * width K β ((s.t + 1 : ℕ) : ℝ) := by
  unfold rnd at hk' hj
  obtain ⟨s', ⟨l1, hs⟩, h1, h2, h3⟩ := fold_trace K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
    (saoStep K β s o).T k (List.finRange K) (s.active, s.tau, s.q, false)
    (List.nodup_finRange K) (List.mem_finRange k)
  have hks : k ∈ s'.1 := h1.2 hk
  have hks' := h3.2 hk'
  have hjs : j ∈ s'.1 := armStep_shrink K β _ _ _ _ _ s' k (h2 hj)
  by_contra hc
  rw [not_le] at hc
  have hm := le_maxOver s'.1 (HtF K β s o) j hjs
  have hd : maxOver s'.1 (HtF K β s o) - HtF K β s o k > 6 * width K β ((s.t + 1 : ℕ) : ℝ) := by
    linarith
  exact (armStep_self K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o) _ s' k hks).2 hd hks'

theorem rnd_fire (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ)
    (hflag : (rnd K β s o).2.2.2 = true) :
    ∃ s' : St K, ∃ k : Fin K, Good (s.t + 1) s.p s.active s.tau s.q s' ∧
      (rnd K β s o).1 ⊆ s'.1 ∧
      fire K β (s.t + 1) (HtF K β s o) (HhF K β s o) (saoStep K β s o).T s' k := by
  unfold rnd at hflag ⊢
  obtain ⟨s', k, ⟨l1, hs⟩, h2, h3⟩ := fold_flag K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
    (saoStep K β s o).T (List.finRange K) (s.active, s.tau, s.q, false) rfl hflag
  refine ⟨_, k, ?_, h2, h3⟩
  apply armStep_good
  rw [hs]; exact fold_good K β _ _ _ _ _ _ _ _ l1 _ (good_init _ _ _ _ _)


/-! ### New for 8092e862: rounds without firing, the max over the active set. -/

theorem maxOver_mono {K : ℕ} (A B : Finset (Fin K)) (f : Fin K → ℝ) (hA : A.Nonempty)
    (hAB : A ⊆ B) : maxOver A f ≤ maxOver B f := by
  obtain ⟨a, ha, e⟩ := maxOver_mem A f hA
  rw [e]; exact le_maxOver B f a (hAB ha)

theorem armStep_max (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (i : Fin K) (hs : s.1.Nonempty) :
    (armStep K β t p Ht Hh T s i).1.Nonempty ∧
      maxOver (armStep K β t p Ht Hh T s i).1 Ht = maxOver s.1 Ht := by
  rcases s with ⟨A, tau, q, b⟩
  unfold armStep
  dsimp only at hs ⊢
  by_cases hd : i ∈ A ∧ maxOver A Ht - Ht i > 6 * width K β t
  · rw [if_pos hd]
    obtain ⟨a, ha, e⟩ := maxOver_mem A Ht hs
    have hw := width_nonneg K β t
    have hai : a ≠ i := by
      intro h; subst h; rw [e] at hd; linarith [hd.2]
    have hae : a ∈ A.erase i := Finset.mem_erase.2 ⟨hai, ha⟩
    refine ⟨⟨a, hae⟩, le_antisymm (maxOver_mono _ _ _ ⟨a, hae⟩ (Finset.erase_subset _ _)) ?_⟩
    rw [e]; exact le_maxOver _ Ht a hae
  · rw [if_neg hd]; exact ⟨hs, rfl⟩

theorem fold_max (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) :
    ∀ (l : List (Fin K)) (s : St K), s.1.Nonempty →
      (l.foldl (armStep K β t p Ht Hh T) s).1.Nonempty ∧
        maxOver (l.foldl (armStep K β t p Ht Hh T) s).1 Ht = maxOver s.1 Ht := by
  intro l
  induction l with
  | nil => intro s hs; exact ⟨hs, rfl⟩
  | cons i l ih =>
    intro s hs
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := armStep_max K β t p Ht Hh T s i hs
    obtain ⟨h3, h4⟩ := ih _ h1
    exact ⟨h3, h4.trans h2⟩

theorem fold_trace2 (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (k : Fin K) :
    ∀ (l : List (Fin K)) (s0 : St K), l.Nodup → k ∈ l →
      ∃ s : St K, (∃ l1 : List (Fin K), s = l1.foldl (armStep K β t p Ht Hh T) s0) ∧
        (k ∈ s.1 ↔ k ∈ s0.1) ∧
        (l.foldl (armStep K β t p Ht Hh T) s0).1 ⊆ (armStep K β t p Ht Hh T s k).1 ∧
        (k ∈ (armStep K β t p Ht Hh T s k).1 ↔ k ∈ (l.foldl (armStep K β t p Ht Hh T) s0).1) ∧
        ∃ l2 : List (Fin K), l.foldl (armStep K β t p Ht Hh T) s0 =
          l2.foldl (armStep K β t p Ht Hh T) (armStep K β t p Ht Hh T s k) := by
  intro l
  induction l with
  | nil => intro s0 _ hk; simp at hk
  | cons a l ih =>
    intro s0 hnd hk
    rw [List.nodup_cons] at hnd
    by_cases hka : k = a
    · subst hka
      refine ⟨s0, ⟨[], rfl⟩, Iff.rfl, ?_, ?_, ⟨l, rfl⟩⟩
      · simp only [List.foldl_cons]; exact fold_shrink K β t p Ht Hh T l _
      · simp only [List.foldl_cons]; exact (fold_other K β t p Ht Hh T k l _ hnd.1).symm
    · have hkl : k ∈ l := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h hka
        · exact h
      obtain ⟨s, ⟨l1, hs⟩, h1, h2, h3, ⟨l2, h4⟩⟩ := ih (armStep K β t p Ht Hh T s0 a) hnd.2 hkl
      refine ⟨s, ⟨a :: l1, by simp [hs]⟩, ?_, ?_, ?_, ⟨l2, ?_⟩⟩
      · rw [h1]; exact armStep_other K β t p Ht Hh T s0 a k (fun e => hka e.symm)
      · simpa using h2
      · simpa using h3
      · simpa using h4

theorem fold_flag_true (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) :
    ∀ (l : List (Fin K)) (s : St K), s.2.2.2 = true →
      (l.foldl (armStep K β t p Ht Hh T) s).2.2.2 = true := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons i l ih =>
    intro s h
    simp only [List.foldl_cons]
    apply ih
    rcases s with ⟨A, tau, q, b⟩
    dsimp only at h
    subst h
    unfold armStep
    simp

theorem armStep_noflag (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) (s : St K)
    (i : Fin K) (h : (armStep K β t p Ht Hh T s i).2.2.2 = false) :
    ¬ fire K β t Ht Hh T (armStep K β t p Ht Hh T s i) i := by
  intro hf
  cases hb : (armStep K β t p Ht Hh T s i).2.2.2 with
  | false =>
    rcases s with ⟨A, tau, q, b⟩
    unfold armStep at hb hf
    unfold fire at hf
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    exact hb.2 hf
  | true => rw [h] at hb; exact absurd hb (by decide)

theorem rnd_nofire (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ)
    (hflag : (rnd K β s o).2.2.2 = false) (hne : s.active.Nonempty) (k : Fin K) :
    ∃ s' : St K, Good (s.t + 1) s.p s.active s.tau s.q s' ∧
      (rnd K β s o).1 ⊆ s'.1 ∧ (k ∈ s'.1 ↔ k ∈ (rnd K β s o).1) ∧
      (k ∈ s.active → k ∈ s'.1 → k ∈ (rnd K β s o).1) ∧
      maxOver s'.1 (HtF K β s o) = maxOver s.active (HtF K β s o) ∧
      ¬ fire K β (s.t + 1) (HtF K β s o) (HhF K β s o) (saoStep K β s o).T s' k := by
  unfold rnd at hflag ⊢
  obtain ⟨s0, ⟨l1, hs⟩, h1, h2, h3, ⟨l2, h4⟩⟩ := fold_trace2 K β (s.t + 1) s.p (HtF K β s o)
    (HhF K β s o) (saoStep K β s o).T k (List.finRange K) (s.active, s.tau, s.q, false)
    (List.nodup_finRange K) (List.mem_finRange k)
  refine ⟨_, ?_, h2, h3, fun _ h => h3.1 h, ?_, ?_⟩
  · apply armStep_good
    rw [hs]; exact fold_good K β _ _ _ _ _ _ _ _ l1 _ (good_init _ _ _ _ _)
  · have e1 := fold_max K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o) (saoStep K β s o).T
      (l1 ++ [k]) (s.active, s.tau, s.q, false) hne
    rw [List.foldl_append, ← hs] at e1
    exact e1.2
  · apply armStep_noflag
    cases hb : (armStep K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
        (saoStep K β s o).T s0 k).2.2.2 with
    | false => rfl
    | true =>
      have := fold_flag_true K β (s.t + 1) s.p (HtF K β s o) (HhF K β s o)
        (saoStep K β s o).T l2 _ hb
      rw [← h4, hflag] at this
      exact absurd this (by decide)

theorem rnd_max (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (hne : s.active.Nonempty) :
    (rnd K β s o).1.Nonempty ∧
      maxOver (rnd K β s o).1 (HtF K β s o) = maxOver s.active (HtF K β s o) := by
  unfold rnd
  exact fold_max K β _ _ _ _ _ _ _ hne

theorem ne_fold (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), s.active.Nonempty →
      (l.foldl (saoStep K β) s).active.Nonempty := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o l ih =>
    intro s h
    simp only [List.foldl_cons]
    apply ih
    cases hs : s.tau0 with
    | some τ => rw [step_frozen K β s o τ hs]; exact h
    | none =>
      rw [(step_fold K β s o hs).1]
      exact (rnd_max K β s o h).1


end P8092e862

namespace P925e7ff2

open BestBothWorlds.SAO P8092e862

/-! ### Exp3.P sampling vectors (from b0242b1c). -/

theorem exp3P_bounds (K : ℕ) (hK : 1 ≤ K) (m : ℕ) (δ' : ℝ) (h : History K) (i : Fin K) :
    0 ≤ exp3P K (exp3PTuned K m δ') h i ∧ exp3P K (exp3PTuned K m δ') h i ≤ 1 := by
  set prm := exp3PTuned K m δ' with hprm
  have hγ0 : 0 ≤ prm.gamma := le_min zero_le_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hγ1 : prm.gamma ≤ 1 := min_le_left _ _
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have key : ∀ (l : History K) (s : (Fin K → ℝ) × (Fin K → ℝ)),
      (∀ j, 0 ≤ s.1 j ∧ s.1 j ≤ 1) →
        ∀ j, 0 ≤ (l.foldl (exp3PStep K prm) s).1 j ∧ (l.foldl (exp3PStep K prm) s).1 j ≤ 1 := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons o l ih =>
      intro s _
      apply ih
      intro j
      simp only [exp3PStep]
      set G : Fin K → ℝ := fun i => s.2 i + ((if o.1 = i then o.2 else 0) + prm.betaP) / s.1 i
        with hG
      have hpos : 0 < ∑ k, Real.exp (prm.eta * G k) :=
        Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
      have hle : Real.exp (prm.eta * G j) ≤ ∑ k, Real.exp (prm.eta * G k) :=
        Finset.single_le_sum (f := fun k => Real.exp (prm.eta * G k))
          (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
      have hx0 : 0 ≤ Real.exp (prm.eta * G j) / ∑ k, Real.exp (prm.eta * G k) :=
        div_nonneg (Real.exp_pos _).le hpos.le
      have hx1 : Real.exp (prm.eta * G j) / ∑ k, Real.exp (prm.eta * G k) ≤ 1 :=
        (div_le_one hpos).mpr hle
      have hg : prm.gamma / K ≤ prm.gamma := div_le_self hγ0 hK'
      have hg0 : 0 ≤ prm.gamma / K := div_nonneg hγ0 (by linarith)
      rw [mul_div_assoc]
      have e1 := mul_nonneg (sub_nonneg.mpr hγ1) hx0
      have e2 := mul_le_mul_of_nonneg_left hx1 (sub_nonneg.mpr hγ1)
      constructor <;> linarith
  have h0 : ∀ _j : Fin K, 0 ≤ (1 / (K : ℝ)) ∧ 1 / (K : ℝ) ≤ 1 := fun _ =>
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hK'⟩
  unfold exp3P exp3PState
  exact key h (fun _ => 1 / (K : ℝ), fun _ => 0) h0 i



theorem exp3P_sum (K : ℕ) (hK : 1 ≤ K) (prm : Exp3PParams) (h : History K) :
    ∑ j, exp3P K prm h j = 1 := by
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  have key : ∀ (l : History K) (s : (Fin K → ℝ) × (Fin K → ℝ)),
      ∑ j, s.1 j = 1 → ∑ j, (l.foldl (exp3PStep K prm) s).1 j = 1 := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons o l ih =>
      intro s _
      apply ih
      simp only [exp3PStep]
      set G : Fin K → ℝ := fun i => s.2 i + ((if o.1 = i then o.2 else 0) + prm.betaP) / s.1 i
        with hG
      have hpos : 0 < ∑ k, Real.exp (prm.eta * G k) :=
        Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
      rw [Finset.sum_add_distrib]
      simp only [mul_div_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_div, div_self hpos.ne', Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
  unfold exp3P exp3PState
  apply key
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp


/-! ### Inactive arms: `p = q τ / (t + 1)`. -/

def Inv3 {K : ℕ} (s : SAOState K) : Prop :=
  ∀ j, j ∉ s.active → s.p j = s.q j * s.tau j / ((s.t : ℝ) + 1)

theorem inv3_init (K n : ℕ) : Inv3 (SAOState.init K n) := by
  intro j hj; simp [SAOState.init] at hj

theorem inv3_step (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : Inv3 s) :
    Inv3 (saoStep K β s o) := by
  cases hs : s.tau0 with
  | some τ => rw [step_frozen K β s o τ hs]; exact h
  | none =>
    obtain ⟨r, -, hA, hT, hQ, ht, -, hP⟩ := step_spec K β s o hs
    intro j hj
    rw [hA] at hj
    rw [hP, hT, hQ, ht]
    simp only [hj, if_false]

theorem inv3_fold (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), Inv3 s → Inv3 (l.foldl (saoStep K β) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o l ih => intro s h; exact ih _ (inv3_step K β s o h)

theorem sao_nonneg (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (h : History K) (i : Fin K) :
    0 ≤ sao K n β h i := by
  unfold sao
  cases hz : (saoState K n β h).tau0 with
  | some τ => exact (exp3P_bounds K hK _ _ _ i).1
  | none =>
    show 0 ≤ (saoState K n β h).p i
    have hI : Inv (saoState K n β h) := inv_fold K β h _ (inv_init K n)
    have hI3 : Inv3 (saoState K n β h) := inv3_fold K β h _ (inv3_init K n)
    by_cases hi : i ∈ (saoState K n β h).active
    · exact (inv_p_bounds _ hI i hi).1
    · rw [hI3 i hi]
      exact div_nonneg (mul_nonneg (hI.1 i hi).2 (Nat.cast_nonneg _)) (by positivity)

theorem sao_sum (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (h : History K) : ∑ j, sao K n β h j = 1 := by
  unfold sao
  cases hz : (saoState K n β h).tau0 with
  | some τ => exact exp3P_sum K hK _ _
  | none =>
    show ∑ j, (saoState K n β h).p j = 1
    have hI : Inv (saoState K n β h) := inv_fold K β h _ (inv_init K n)
    have hI3 : Inv3 (saoState K n β h) := inv3_fold K β h _ (inv3_init K n)
    have hne : (saoState K n β h).active.Nonempty := by
      have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
      exact ne_fold K β h _ Finset.univ_nonempty
    set s := saoState K n β h with hs
    obtain ⟨_, _, _, _, hp⟩ := hI
    rw [← Finset.sum_sdiff (Finset.subset_univ s.active)]
    have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hne).ne'
    have e1 : ∑ x ∈ s.active, s.p x =
        1 - ∑ j ∈ Finset.univ \ s.active, s.q j * s.tau j / ((s.t : ℝ) + 1) := by
      rw [Finset.sum_congr rfl hp, Finset.sum_const, nsmul_eq_mul]
      field_simp
    have e2 : ∑ x ∈ Finset.univ \ s.active, s.p x =
        ∑ j ∈ Finset.univ \ s.active, s.q j * s.tau j / ((s.t : ℝ) + 1) :=
      Finset.sum_congr rfl (fun j hj => hI3 j (Finset.mem_sdiff.mp hj).2)
    rw [e1, e2]
    ring

/-! ### Active probabilities never decrease (before the switch). -/

theorem mono_step (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : Inv s)
    (hs : s.tau0 = none) (i : Fin K) (hi : i ∈ (saoStep K β s o).active) :
    s.p i ≤ (saoStep K β s o).p i := by
  obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, ht, hz, hP⟩ := step_spec K β s o hs
  have hpb := inv_p_bounds s h
  obtain ⟨h1, _, hW0, hW1, hp⟩ := h
  have hi' : i ∈ r.1 := by rw [← hA]; exact hi
  have hiA : i ∈ s.active := hsub hi'
  have hss : Finset.univ \ s.active ⊆ Finset.univ \ r.1 :=
    Finset.sdiff_subset_sdiff (subset_refl _) hsub
  have hWr : ∑ j ∈ Finset.univ \ r.1, r.2.2.1 j * (r.2.1 j : ℝ) =
      ∑ j ∈ (Finset.univ \ r.1) \ (Finset.univ \ s.active), s.p j * ((s.t : ℝ) + 1) + W s := by
    rw [← Finset.sum_sdiff hss, W]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
      obtain ⟨e1, e2⟩ := (hg j).1 hj.2 hj.1
      rw [e1, e2]; push_cast; ring
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
      obtain ⟨e1, e2⟩ := (hg j).2 (Or.inr hj)
      rw [e1, e2]
  set D := (Finset.univ \ r.1) \ (Finset.univ \ s.active) with hD
  have hDA : D ⊆ s.active := by
    intro j hj
    simp only [hD, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj
    exact hj.2
  have hDeq : D = s.active \ r.1 := by
    ext j; simp only [hD, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]; tauto
  have hcardD : (s.active.card : ℝ) = r.1.card + D.card := by
    have := Finset.card_sdiff_add_card_eq_card hsub
    rw [hDeq]
    exact_mod_cast (by omega : s.active.card = r.1.card + (s.active \ r.1).card)
  set P := s.p i with hPdef
  have hP0 : 0 ≤ P := (hpb i hiA).1
  have hc : (0 : ℝ) < (s.t : ℝ) + 1 := by positivity
  have hAc : (0 : ℝ) < s.active.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hiA⟩
  have e1 : (s.active.card : ℝ) * P = 1 - W s / ((s.t : ℝ) + 1) := by
    rw [hPdef, hp i hiA, sum_eq_W]
    field_simp
  have hW : W s = ((s.t : ℝ) + 1) * (1 - s.active.card * P) := by
    have h' : W s / ((s.t : ℝ) + 1) = 1 - s.active.card * P := by linarith
    rw [div_eq_iff hc.ne'] at h'
    rw [h']; ring
  have hpD : ∀ j ∈ D, s.p j = P := fun j hj => by rw [hp j (hDA hj), hPdef, hp i hiA]
  have hsumD : ∑ j ∈ D, s.p j * ((s.t : ℝ) + 1) = D.card * P * ((s.t : ℝ) + 1) := by
    rw [Finset.sum_congr rfl (fun j hj => by rw [hpD j hj]), Finset.sum_const, nsmul_eq_mul]
    ring
  have hnew : (saoStep K β s o).p i =
      (1 - (D.card * P * ((s.t : ℝ) + 1) + W s) / ((s.t : ℝ) + 2)) / r.1.card := by
    rw [hP]
    simp only [hi', if_true]
    rw [← Finset.sum_div, hWr, hsumD]
    push_cast; ring
  have hr1 : (1 : ℝ) ≤ r.1.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi'⟩
  have hAP : (s.active.card : ℝ) * P ≤ 1 := by
    rw [e1]; have := div_nonneg hW0 hc.le; linarith
  have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  have hPr : P * r.1.card ≤ 1 := by
    have : P * r.1.card ≤ P * s.active.card :=
      mul_le_mul_of_nonneg_left (by rw [hcardD]; linarith) hP0
    linarith [mul_comm P (s.active.card : ℝ)]
  have ht2 : (0 : ℝ) < (s.t : ℝ) + 2 := by positivity
  have key : (D.card * P * ((s.t : ℝ) + 1) + W s) / ((s.t : ℝ) + 2) ≤ 1 - P * r.1.card := by
    rw [div_le_iff₀ ht2, hW, hcardD]
    nlinarith
  rw [hnew, le_div_iff₀ (by linarith)]
  linarith

/-! ### Paths: splitting off the last round, for any adaptive adversary. -/

theorem ofFn_snoc {K m : ℕ} (I : Fin m → Fin K) (j : Fin K) :
    List.ofFn (Fin.snoc I j : Fin (m + 1) → Fin K) = List.ofFn I ++ [j] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

theorem hist_snoc {K m : ℕ} (adv : Adversary K) (I : Fin m → Fin K) (j : Fin K) :
    history adv (Fin.snoc I j : Fin (m + 1) → Fin K) =
      history adv I ++ [(j, adv (List.ofFn I) j)] := by
  have hlen : (List.ofFn I).length = m := List.length_ofFn
  unfold history
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · congr 1
    funext r
    simp only [Fin.snoc_castSucc]
    congr 1
    unfold reward
    rw [ofFn_snoc, Fin.val_castSucc, List.take_append_of_le_length (by rw [hlen]; exact r.isLt.le)]
  · simp only [Fin.snoc_last]
    unfold reward
    rw [ofFn_snoc, Fin.val_last, List.take_append_of_le_length (le_of_eq hlen.symm),
      List.take_of_length_le (le_of_eq hlen)]

theorem take_hist_snoc {K m : ℕ} (adv : Adversary K) (I : Fin m → Fin K) (j : Fin K) (r : ℕ)
    (hr : r ≤ m) :
    (history adv (Fin.snoc I j : Fin (m + 1) → Fin K)).take r = (history adv I).take r := by
  have hlen : (history adv I).length = m := by simp [history]
  rw [hist_snoc, List.take_append_of_le_length (by rw [hlen]; exact hr)]

theorem pathProb_snoc' {K m : ℕ} (π : Policy K) (adv : Adversary K) (I : Fin m → Fin K)
    (j : Fin K) :
    pathProb π adv (Fin.snoc I j : Fin (m + 1) → Fin K) =
      pathProb π adv I * π (history adv I) j := by
  have hlen : (history adv I).length = m := by simp [history]
  unfold pathProb probAt
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, Nat.add_sub_cancel]
    rw [take_hist_snoc adv I j r r.isLt.le]
  · simp only [Fin.val_last, Fin.snoc_last, Nat.add_sub_cancel]
    rw [take_hist_snoc adv I j m le_rfl, List.take_of_length_le (le_of_eq hlen)]

theorem sum_snoc {K m : ℕ} (f : (Fin (m + 1) → Fin K) → ℝ) :
    ∑ I, f I = ∑ I : Fin m → Fin K, ∑ j : Fin K, f (Fin.snoc I j) := by
  rw [← (Fin.snocEquiv (fun _ => Fin K)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem sum_pathProb' {K : ℕ} (π : Policy K) (hπ : ∀ h, ∑ j, π h j = 1) (adv : Adversary K) :
    ∀ m : ℕ, ∑ I : Fin m → Fin K, pathProb π adv I = 1 := by
  intro m
  induction m with
  | zero => simp [pathProb]
  | succ m ih =>
    rw [sum_snoc]
    simp only [pathProb_snoc', ← Finset.mul_sum, hπ, mul_one]
    exact ih


end P925e7ff2

namespace P169808da

open BestBothWorlds.SAO P8092e862 P925e7ff2

/-- Union bound for `probEvent` with nonnegative path weights of total mass `1`. -/
theorem ub {K n : ℕ} (π : Policy K) (adv : Adversary K)
    (hw : ∀ I : Fin n → Fin K, 0 ≤ pathProb π adv I)
    (htot : ∑ I : Fin n → Fin K, pathProb π adv I = 1)
    {ι : Type} (S : Finset ι) (E : ι → (Fin n → Fin K) → Prop) (F : (Fin n → Fin K) → Prop)
    (hF : ∀ I, (∀ j ∈ S, E j I) → F I) (d : ι → ℝ)
    (hE : ∀ j ∈ S, 1 - d j ≤ probEvent n π adv (E j)) :
    1 - ∑ j ∈ S, d j ≤ probEvent n π adv F := by
  classical
  unfold probEvent at hE ⊢
  have hg : ∀ j I, 0 ≤ pathProb π adv I - (if E j I then pathProb π adv I else 0) := by
    intro j I
    split_ifs
    · simp
    · simpa using hw I
  have key : ∀ I, pathProb π adv I -
      ∑ j ∈ S, (pathProb π adv I - (if E j I then pathProb π adv I else 0)) ≤
        (if F I then pathProb π adv I else 0) := by
    intro I
    by_cases hFI : F I
    · rw [if_pos hFI]
      have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hg j I)
      linarith
    · rw [if_neg hFI]
      have hex : ∃ j ∈ S, ¬ E j I := by
        by_contra hc
        push Not at hc
        exact hFI (hF I hc)
      obtain ⟨j, hj, hnE⟩ := hex
      have h1 := Finset.single_le_sum (f := fun j =>
        pathProb π adv I - (if E j I then pathProb π adv I else 0))
        (fun j _ => hg j I) hj
      simp only [if_neg hnE, sub_zero] at h1
      linarith
  have hsum := Finset.sum_le_sum (fun I (_ : I ∈ Finset.univ) => key I)
  have e : ∑ I : Fin n → Fin K, (pathProb π adv I -
      ∑ j ∈ S, (pathProb π adv I - (if E j I then pathProb π adv I else 0))) =
      1 - ∑ j ∈ S, (1 - ∑ I : Fin n → Fin K, (if E j I then pathProb π adv I else 0)) := by
    rw [Finset.sum_sub_distrib, htot, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_sub_distrib, htot]
  have hd : ∑ j ∈ S, (1 - ∑ I : Fin n → Fin K, (if E j I then pathProb π adv I else 0)) ≤
      ∑ j ∈ S, d j := Finset.sum_le_sum (fun j hj => by linarith [hE j hj])
  linarith

theorem tau0_le (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) :
    tau0 K n β adv I ≤ n := by
  have hinv : Inv (runState K n β adv I n) := inv_fold K β _ _ (inv_init K n)
  have hSt : (runState K n β adv I n).t ≤ n := by
    have h1 := t_fold K β ((history adv I).take n) (SAOState.init K n)
    have h2 : ((history adv I).take n).length ≤ n := by simp [List.length_take]
    have h3 : (SAOState.init K n).t = 0 := rfl
    show (saoState K n β _).t ≤ n
    unfold saoState
    omega
  have hdef : tau0 K n β adv I =
      (match (runState K n β adv I n).tau0 with | some τ => τ | none => n) := rfl
  rw [hdef]
  cases hz : (runState K n β adv I n).tau0 with
  | none => exact le_rfl
  | some τ => exact (hinv.2.1 τ hz).trans hSt

theorem qEff_nonneg (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) : 0 ≤ qEff K n β adv I i := by
  unfold qEff probAt
  exact sao_nonneg K n hK β _ i

theorem estRadius_mono (K τ : ℕ) (q : ℝ) (hq : 0 ≤ q) (t : ℕ) (L1 L2 : ℝ) (h0 : 0 ≤ L1)
    (h12 : L1 ≤ L2) : estRadius K τ q t L1 ≤ estRadius K τ q t L2 := by
  unfold estRadius
  apply Real.sqrt_le_sqrt
  have hA : 0 ≤ (K : ℝ) * (min τ t : ℕ) / (t : ℝ) ^ 2 +
      max ((t : ℝ) - τ) 0 / (q * τ * t) := by
    have h1 : 0 ≤ (K : ℝ) * (min τ t : ℕ) / (t : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ max ((t : ℝ) - τ) 0 / (q * τ * t) :=
      div_nonneg (le_max_right _ _) (mul_nonneg (mul_nonneg hq (Nat.cast_nonneg _))
        (Nat.cast_nonneg _))
    linarith
  have hm : (0 : ℝ) ≤ ((min τ t : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hb1 : 0 ≤ (K : ℝ) * L1 / (min τ t : ℕ) := div_nonneg (mul_nonneg hK h0) hm
  have hb2 : (K : ℝ) * L1 / (min τ t : ℕ) ≤ (K : ℝ) * L2 / (min τ t : ℕ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h12 hK) hm
  have hsq := pow_le_pow_left₀ hb1 hb2 2
  have hl := mul_le_mul_of_nonneg_left h12 hA
  nlinarith

theorem pullBound_mono (q : ℝ) (hq : 0 ≤ q) (τ t : ℕ) (ht : 1 ≤ t) (L1 L2 : ℝ) (h0 : 0 ≤ L1)
    (h12 : L1 ≤ L2) : pullBound q τ t L1 ≤ pullBound q τ t L2 := by
  unfold pullBound
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht)
  have hc : 0 ≤ 4 * q * τ * (1 + Real.log t) := by
    have : 0 ≤ 4 * q * τ := mul_nonneg (mul_nonneg (by norm_num) hq) (Nat.cast_nonneg _)
    exact mul_nonneg this (by linarith)
  have hl := mul_le_mul_of_nonneg_left h12 hc
  have hsq := pow_le_pow_left₀ h0 h12 2
  have : Real.sqrt (4 * q * τ * (1 + Real.log t) * L1 + 5 * L1 ^ 2) ≤
      Real.sqrt (4 * q * τ * (1 + Real.log t) * L2 + 5 * L2 ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- `0 ≤ log x ≤ log β` for `1 ≤ x ≤ β`. -/
theorem log_window (x β : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ β) :
    0 ≤ Real.log x ∧ Real.log x ≤ Real.log β :=
  ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) h2⟩

end P169808da

open BestBothWorlds.SAO P8092e862 P925e7ff2 P169808da in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded) :
    1 - δ ≤ probEvent n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv (fun I =>
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
        |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv I i t - fixedAvg adv I i t| ≤
            estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t
              (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ∧
        (pullCount I i t : ℝ) ≤
            pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t
              (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) ∧
      regretFrom adv I (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) ≤
        5.15 * Real.sqrt (((n : ℝ) - tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) := by
  have hn : 2 ≤ n := le_trans hK hKn
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hKpos : (0 : ℝ) < K := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set δe : ℝ := δ / (3 * K * n) with hδe
  set δx : ℝ := δ / (10 * (n : ℝ) ^ 3) with hδx
  have hδe0 : 0 < δe := by positivity
  have hn3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnr 3
    norm_num at this
    linarith
  have hδx0 : 0 < δx := by positivity
  have hδx1 : δx < 1 := by
    rw [hδx, div_lt_one (by positivity)]
    linarith
  have hKδ : (K : ℝ) / δx = 10 * (K : ℝ) * (n : ℝ) ^ 3 / δ := by
    rw [hδx]; field_simp
  have hX := exp3p_phase_regret K n hK hKn δx hδx0 hδx1 adv hadv
  rw [hKδ] at hX
  generalize hβ : 10 * (K : ℝ) * (n : ℝ) ^ 3 / δ = β at hX ⊢
  have hβ1 : 1 < β := by
    rw [← hβ, one_lt_div hδ0]
    nlinarith
  -- logarithm windows
  have hwinE : ∀ t : ℕ, 1 ≤ t → t ≤ n →
      0 ≤ Real.log (2 * (t : ℝ) ^ 2 / δe) ∧ Real.log (2 * (t : ℝ) ^ 2 / δe) ≤ Real.log β := by
    intro t ht htn
    have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have htnr : (t : ℝ) ≤ n := by exact_mod_cast htn
    have e : 2 * (t : ℝ) ^ 2 / δe = 6 * K * n * (t : ℝ) ^ 2 / δ := by
      rw [hδe]; field_simp; ring
    rw [e]
    apply log_window
    · rw [le_div_iff₀ hδ0]
      have : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
      have h4 : (4 : ℝ) ≤ K * n := by nlinarith
      nlinarith
    · rw [← hβ]
      apply div_le_div_of_nonneg_right _ hδ0.le
      have ht2 : (t : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) htnr 2
      have h6 : (0 : ℝ) ≤ 6 * K * n := by positivity
      have := mul_le_mul_of_nonneg_left ht2 h6
      have h7 : (0 : ℝ) ≤ K * n ^ 3 := by positivity
      nlinarith
  have hwinP : ∀ t : ℕ, 1 ≤ t → t ≤ n →
      0 ≤ Real.log ((t : ℝ) / δe) ∧ Real.log ((t : ℝ) / δe) ≤ Real.log β := by
    intro t ht htn
    have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have htnr : (t : ℝ) ≤ n := by exact_mod_cast htn
    have e : (t : ℝ) / δe = 3 * K * n * (t : ℝ) / δ := by
      rw [hδe]; field_simp
    rw [e]
    apply log_window
    · rw [le_div_iff₀ hδ0]
      have h4 : (4 : ℝ) ≤ K * n := by nlinarith
      nlinarith
    · rw [← hβ]
      apply div_le_div_of_nonneg_right _ hδ0.le
      have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have h3 : (0 : ℝ) ≤ 3 * K * n := by positivity
      have := mul_le_mul_of_nonneg_left (htnr.trans hn2) h3
      have h7 : (0 : ℝ) ≤ K * n ^ 3 := by positivity
      nlinarith
  -- the union bound
  have hw : ∀ I : Fin n → Fin K, 0 ≤ pathProb (sao K n β) adv I := fun I =>
    Finset.prod_nonneg (fun r _ => sao_nonneg K n (by omega) β _ _)
  have htot : ∑ I : Fin n → Fin K, pathProb (sao K n β) adv I = 1 :=
    sum_pathProb' (sao K n β) (fun h => sao_sum K n (by omega) β h) adv n
  let T : Finset (Fin K × ℕ × Bool) := Finset.univ ×ˢ (Finset.Icc 1 n ×ˢ Finset.univ)
  let Rx : (Fin n → Fin K) → Prop := fun I => regretFrom adv I (tau0 K n β adv I) ≤
        5.15 * Real.sqrt (((n : ℝ) - tau0 K n β adv I) * K * Real.log β)
  let Es : Fin K → ℕ → (Fin n → Fin K) → Prop := fun i t I =>
    t ≤ tau0 K n β adv I →
        |estAvg (sao K n β) adv I i t - fixedAvg adv I i t| ≤
          estRadius K (tauEff K n β adv I i) (qEff K n β adv I i) t
            (Real.log (2 * (t : ℝ) ^ 2 / δe))
  let Pu : Fin K → ℕ → (Fin n → Fin K) → Prop := fun i t I =>
    t ≤ tau0 K n β adv I →
        (pullCount I i t : ℝ) ≤
          pullBound (qEff K n β adv I i) (tauEff K n β adv I i) t (Real.log (t / δe))
  let E : Option (Fin K × ℕ × Bool) → (Fin n → Fin K) → Prop := fun j I =>
    Option.elim j (Rx I) (fun p => cond p.2.2 (Es p.1 p.2.1 I) (Pu p.1 p.2.1 I))
  let d : Option (Fin K × ℕ × Bool) → ℝ := fun j => Option.elim j δx (fun _ => δe)
  have hmem : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 n, ∀ b : Bool, some (i, t, b) ∈ T.insertNone := by
    intro i t ht b
    exact Finset.some_mem_insertNone.2
      (Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩⟩)
  refine le_trans ?_ (ub (sao K n β) adv hw htot T.insertNone E _ ?_ d ?_)
  · -- total failure mass
    have hsum : ∑ j ∈ T.insertNone, d j = δx + (K * (n * 2) : ℕ) * δe := by
      rw [Finset.sum_insertNone]
      simp [d, T, Finset.sum_const, Finset.card_product]
    have hmass : δx + (K * (n * 2) : ℕ) * δe ≤ δ := by
      have e2 : ((K * (n * 2) : ℕ) : ℝ) * δe = 2 * δ / 3 := by
        rw [hδe]; push_cast; field_simp
      rw [e2, hδx]
      have : δ / (10 * (n : ℝ) ^ 3) ≤ δ / 3 :=
        div_le_div_of_nonneg_left hδ0.le (by norm_num) (by linarith)
      linarith
    linarith
  · intro I h
    refine ⟨fun i t ht => ?_, ?_⟩
    · obtain ⟨ht1, htt⟩ := Finset.mem_Icc.1 ht
      have htn : t ≤ n := htt.trans (tau0_le K n β adv I)
      have htI : t ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨ht1, htn⟩
      have hq := qEff_nonneg K n (by omega) β adv I i
      have hEs : Es i t I := h _ (hmem i t htI true)
      have hPu : Pu i t I := h _ (hmem i t htI false)
      obtain ⟨hE0, hE1⟩ := hwinE t ht1 htn
      obtain ⟨hP0, hP1⟩ := hwinP t ht1 htn
      exact ⟨(hEs htt).trans (estRadius_mono _ _ _ hq _ _ _ hE0 hE1),
        (hPu htt).trans (pullBound_mono _ hq _ _ ht1 _ _ hP0 hP1)⟩
    · exact h none Finset.none_mem_insertNone
  · intro j hj
    rcases j with _ | ⟨i, t, b⟩
    · exact hX
    · have hT := Finset.some_mem_insertNone.1 hj
      obtain ⟨-, hT2⟩ := Finset.mem_product.1 hT
      obtain ⟨ht, -⟩ := Finset.mem_product.1 hT2
      obtain ⟨ht1, htn⟩ := Finset.mem_Icc.1 ht
      cases b
      · exact pull_count_bound K n hK hKn β hβ1 adv hadv i t ht1 htn δe hδe0
      · exact estimate_concentration_adversarial K n hK hKn β hβ1 adv hadv i t ht1 htn δe hδe0
