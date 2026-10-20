-- Prove2me | solution 1 for BestBothWorlds.SAO.stochastic_no_switch
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T04:48:27.640589+00:00
-- url     : https://prove2.me/submissions/780bffd8-9325-4d46-a081-5d4d0b46f127

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

set_option autoImplicit false

open MeasureTheory

namespace P6f9ffc20

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

/-! ### The main argument. -/

theorem main (K n : ℕ) (hK : 0 < K) (β : ℝ) (hL : 0 ≤ Real.log β) (adv : Adversary K)
    (I : Fin n → Fin K) (μ : Fin K → ℝ)
    (h21 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β adv I),
      |estAvg (sao K n β) adv I i t - μ i| ≤
        estRadius K (tauEff K n β adv I i) (qEff K n β adv I i) t (Real.log β))
    (h23 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β adv I),
      1 ≤ pullCount I i t →
        |algAvg adv I i t - μ i| ≤ Real.sqrt (2 * Real.log β / pullCount I i t)) :
    tau0 K n β adv I = n := by
  classical
  set S : ℕ → SAOState K := fun u => saoState K n β ((history adv I).take u) with hSdef
  have hS0 : S 0 = SAOState.init K n := rfl
  have hlater : ∀ a b, a ≤ b → ∃ l : History K, S b = l.foldl (saoStep K β) (S a) :=
    fun a b hab => later K n β (history adv I) a b hab
  have hstep : ∀ u (h : u < n),
      S (u + 1) = saoStep K β (S u) (I ⟨u, h⟩, reward adv I ⟨u, h⟩ (I ⟨u, h⟩)) := by
    intro u h
    show saoState K n β _ = _
    unfold saoState
    rw [take_succ_hist adv I u h, List.foldl_append]
    rfl
  have hinv : ∀ u, Inv (S u) ∧ Inv2 n (S u) :=
    fun u => inv12_fold K n hK β _ _ (inv_init K n) (inv2_init K n hK)
  have htau0def : tau0 K n β adv I = (match (S n).tau0 with | some τ => τ | none => n) := rfl
  by_cases hfin : (S n).tau0 = none
  · rw [htau0def, hfin]
  exfalso
  have hex : ∃ u, (S u).tau0 ≠ none := ⟨n, hfin⟩
  obtain ⟨m, hmn, hlt, hm⟩ : ∃ m, m + 1 ≤ n ∧ (∀ v ≤ m, (S v).tau0 = none) ∧
      (S (m + 1)).tau0 ≠ none := by
    have h1 := Nat.find_spec hex
    have h2 : Nat.find hex ≤ n := Nat.find_min' hex hfin
    have h3 : ∀ v < Nat.find hex, (S v).tau0 = none := fun v hv => by
      have := Nat.find_min hex hv; simpa using this
    have h0 : Nat.find hex ≠ 0 := by
      intro e; rw [e, hS0] at h1; exact h1 rfl
    refine ⟨Nat.find hex - 1, by omega, fun v hv => h3 v (by omega), ?_⟩
    have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [e]; exact h1
  have hmn' : m < n := by omega
  have htr : ∀ u ≤ m + 1, (S u).t = u ∧ ∀ i, (S u).Gtil i = estReward (sao K n β) adv I i u ∧
      (S u).Ghat i = algReward adv I i u ∧ (S u).T i = pullCount I i u :=
    fun u hu => track K n β adv I u (by omega) (fun v hv => hlt v (by omega))
  have hG : ∀ k u, u ≤ m + 1 → (S u).Gtil k / ((u : ℕ) : ℝ) = estAvg (sao K n β) adv I k u := by
    intro k u hu; rw [((htr u hu).2 k).1]; rfl
  have hround : ∀ u ≤ m, ∃ o, S (u + 1) = saoStep K β (S u) o ∧
      (∀ i, HtF K β (S u) o i = estAvg (sao K n β) adv I i (u + 1)) ∧ (S u).t = u := by
    intro u hu
    refine ⟨_, hstep u (by omega), fun i => ?_, (htr u (by omega)).1⟩
    unfold HtF
    rw [← hstep u (by omega), (htr u (by omega)).1]
    exact hG i (u + 1) (by omega)
  -- the firing round
  obtain ⟨o, hso, hHtm, htm⟩ := hround m le_rfl
  obtain ⟨hA1, hT1, hQ1, hz1, ht1, -, -, -⟩ := step_fold K β (S m) o (hlt m le_rfl)
  rw [← hso] at hA1 hT1 hQ1 hz1 ht1
  have hflag : (rnd K β (S m) o).2.2.2 = true := by
    by_contra hb
    rw [Bool.not_eq_true] at hb
    apply hm
    rw [hz1, hb]
    simp
  have hSm1 : (S (m + 1)).tau0 = some (m + 1) := by rw [hz1, if_pos hflag, htm]
  have hSn : S n = S (m + 1) := by
    obtain ⟨l, hl⟩ := hlater (m + 1) n hmn
    rw [hl]; exact frozen_fold K β (m + 1) l _ hSm1
  have hT0 : tau0 K n β adv I = m + 1 := by rw [htau0def, hSn, hSm1]
  have htE : ∀ k, tauEff K n β adv I k = min ((S (m + 1)).tau k) (m + 1) := by
    intro k
    unfold tauEff
    rw [hT0]
    show min ((S n).tau k) (m + 1) = _
    rw [hSn]
  have hqE : ∀ k, qEff K n β adv I k = probAt (sao K n β) adv I (tauEff K n β adv I k) k :=
    fun k => rfl
  have h21' : ∀ k u, 1 ≤ u → u ≤ m + 1 → |estAvg (sao K n β) adv I k u - μ k| ≤
      estRadius K (tauEff K n β adv I k) (qEff K n β adv I k) u (Real.log β) :=
    fun k u h1 h2 => h21 k u (by rw [hT0]; exact Finset.mem_Icc.2 ⟨h1, h2⟩)
  have h23' : ∀ k, 1 ≤ pullCount I k (m + 1) → |algAvg adv I k (m + 1) - μ k| ≤
      Real.sqrt (2 * Real.log β / pullCount I k (m + 1)) :=
    fun k h => h23 k (m + 1) (by rw [hT0]; exact Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) h
  -- deactivation rounds
  have hdr : ∀ k w, w ≤ m + 1 → k ∉ (S w).active → ∃ v, 1 ≤ v ∧ v ≤ w ∧
      (∀ u < v, k ∈ (S u).active) ∧ ∀ w', v ≤ w' →
        k ∉ (S w').active ∧ (S w').tau k = v ∧ (S w').q k = (S (v - 1)).p k := by
    intro k w hw hk
    have hex' : ∃ v, k ∉ (S v).active := ⟨w, hk⟩
    have hv := Nat.find_spec hex'
    have hvw : Nat.find hex' ≤ w := Nat.find_min' hex' hk
    have hmin : ∀ u < Nat.find hex', k ∈ (S u).active := fun u hu => by
      have := Nat.find_min hex' hu; simpa using this
    have hv0 : Nat.find hex' ≠ 0 := by
      intro e; rw [e, hS0] at hv; simp [SAOState.init] at hv
    set v := Nat.find hex' with hvdef
    obtain ⟨v1, hv1⟩ : ∃ v1, v = v1 + 1 := ⟨v - 1, by omega⟩
    have hkA : k ∈ (S v1).active := hmin v1 (by omega)
    have hv1n : v1 < n := by omega
    obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, _⟩ := step_spec K β (S v1)
      (I ⟨v1, hv1n⟩, reward adv I ⟨v1, hv1n⟩ (I ⟨v1, hv1n⟩)) (hlt v1 (by omega))
    have hvS : k ∉ (S (v1 + 1)).active := by rw [← hv1]; exact hv
    rw [hstep v1 hv1n, hA] at hvS
    obtain ⟨e1, e2⟩ := (hg k).1 hkA hvS
    refine ⟨v, by omega, hvw, hmin, fun w' hw' => ?_⟩
    obtain ⟨l, hl⟩ := hlater v w' hw'
    obtain ⟨a, b, c⟩ := persist_fold2 K β k l (S v) hv
    rw [hl]
    refine ⟨a, ?_, ?_⟩
    · rw [b, hv1, hstep v1 hv1n, hT, e1, (htr v1 (by omega)).1]
    · rw [c, hv1, Nat.add_sub_cancel, hstep v1 hv1n, hQ, e2]
  have hge : ∀ k u, u ≤ m → k ∈ (S u).active → u + 1 ≤ (S (m + 1)).tau k := by
    intro k u hu hk
    by_cases hkF : k ∈ (S (m + 1)).active
    · rw [(hinv (m + 1)).2.2 k hkF]; omega
    · obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k (m + 1) le_rfl hkF
      have hvu : u + 1 ≤ v := by
        by_contra hc
        exact (hpost u (by omega)).1 hk
      rw [(hpost (m + 1) hvw).2.1]; exact hvu
  have hR1 : ∀ k u, 1 ≤ u → u ≤ m + 1 → k ∈ (S (u - 1)).active →
      estRadius K (tauEff K n β adv I k) (qEff K n β adv I k) u (Real.log β) = width K β u := by
    intro k u h1 h2 hk
    apply rad_eq K β _ _ u h1
    rw [htE]
    have := hge k (u - 1) (by omega) hk
    omega
  have hR2 : ∀ k, k ∉ (S (m + 1)).active → ∀ u, (S (m + 1)).tau k ≤ u → u ≤ m + 1 →
      estRadius K (tauEff K n β adv I k) (qEff K n β adv I k) u (Real.log β) ≤
        width K β ((S (m + 1)).tau k) := by
    intro k hkF u hu1 hu2
    obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k (m + 1) le_rfl hkF
    have hFv : (S (m + 1)).tau k = v := (hpost (m + 1) hvw).2.1
    have hEv : tauEff K n β adv I k = v := by rw [htE, hFv]; omega
    rw [hFv] at hu1 ⊢
    rw [hqE, hEv]
    apply rad_le K hK β hL v _ u hv1 hu1
    have hkv : k ∈ (S (v - 1)).active := hmin (v - 1) (by omega)
    have hp : probAt (sao K n β) adv I v = (S (v - 1)).p := by
      unfold probAt; exact sao_eq K n β _ (hlt (v - 1) (by omega))
    rw [hp]
    exact active_p_ge K n hK _ (hinv _).1 (hinv _).2 k hkv
  -- the best arm
  obtain ⟨istar, -, hmax⟩ := Finset.exists_max_image Finset.univ μ ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hmax' : ∀ j, μ j ≤ μ istar := fun j => hmax j (Finset.mem_univ _)
  have hgap : ∀ k, k ∉ (S (m + 1)).active →
      μ istar - μ k > 4 * width K β ((S (m + 1)).tau k) := by
    intro k hkF
    obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k (m + 1) le_rfl hkF
    rw [(hpost (m + 1) hvw).2.1]
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    have hkA : k ∈ (S u).active := hmin u (by omega)
    have hkB : k ∉ (S (u + 1)).active := (hpost (u + 1) le_rfl).1
    obtain ⟨o', hso, hHt, hut⟩ := hround u (by omega)
    obtain ⟨hA, -⟩ := step_fold K β (S u) o' (hlt u (by omega))
    rw [hso, hA] at hkB
    obtain ⟨j, hj, hd⟩ := rnd_deact K β (S u) o' k hkA hkB
    rw [hHt, hHt, hut] at hd
    have bj := h21' j (u + 1) (by omega) (by omega)
    have bk := h21' k (u + 1) (by omega) (by omega)
    rw [hR1 j (u + 1) (by omega) (by omega) (by simpa using hj)] at bj
    rw [hR1 k (u + 1) (by omega) (by omega) (by simpa using hkA)] at bk
    rw [abs_le] at bj bk
    have := hmax' j
    linarith
  have hstarF : istar ∈ (S (m + 1)).active := by
    by_contra h
    have h1 := hgap istar h
    have h2 := width_nonneg K β ((S (m + 1)).tau istar)
    linarith
  have hstarS : ∀ u ≤ m + 1, istar ∈ (S u).active := by
    intro u hu
    by_contra h
    obtain ⟨l, hl⟩ := hlater u (m + 1) hu
    have := (persist_fold2 K β istar l (S u) h).1
    rw [← hl] at this
    exact this hstarF
  have hnd : ∀ k, k ∉ (S (m + 1)).active → 2 ≤ (S (m + 1)).tau k →
      μ istar - μ k ≤ 8 * width K β (((S (m + 1)).tau k - 1 : ℕ) : ℝ) := by
    intro k hkF h2
    obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k (m + 1) le_rfl hkF
    rw [(hpost (m + 1) hvw).2.1] at h2 ⊢
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 2 := ⟨v - 2, by omega⟩
    have hk0 : k ∈ (S u).active := hmin u (by omega)
    have hk1 : k ∈ (S (u + 1)).active := hmin (u + 1) (by omega)
    have hs1 : istar ∈ (S (u + 1)).active := hstarS (u + 1) (by omega)
    obtain ⟨o', hso, hHt, hut⟩ := hround u (by omega)
    obtain ⟨hA, -⟩ := step_fold K β (S u) o' (hlt u (by omega))
    rw [hso, hA] at hk1 hs1
    have hd := rnd_keep K β (S u) o' k istar hk0 hk1 hs1
    rw [hHt, hHt, hut] at hd
    have bj := h21' istar (u + 1) (by omega) (by omega)
    have bk := h21' k (u + 1) (by omega) (by omega)
    rw [hR1 istar (u + 1) (by omega) (by omega) (by simpa using hstarS u (by omega))] at bj
    rw [hR1 k (u + 1) (by omega) (by omega) (by simpa using hk0)] at bk
    rw [abs_le] at bj bk
    have e : u + 2 - 1 = u + 1 := by omega
    rw [e]
    linarith
  -- the firing arm
  obtain ⟨s', k, hgood', hsub', hfire⟩ := rnd_fire K β (S m) o hflag
  have hgr := rnd_good K β (S m) o
  rw [htm] at hgood' hgr hfire
  have hHt : HtF K β (S m) o = fun i => estAvg (sao K n β) adv I i (m + 1) := by
    funext i
    exact hHtm i
  have hHh : HhF K β (S m) o = fun i => algAvg adv I i (m + 1) := by
    funext i
    unfold HhF
    rw [← hso, ((htr (m + 1) le_rfl).2 i).2.1, ((htr (m + 1) le_rfl).2 i).2.2]
    rfl
  have hTT : (saoStep K β (S m) o).T = fun i => pullCount I i (m + 1) := by
    funext i
    rw [← hso, ((htr (m + 1) le_rfl).2 i).2.2]
  rw [hHt, hHh, hTT] at hfire
  beta_reduce at hfire
  rw [← hA1] at hsub'
  unfold fire at hfire
  have hstarm : istar ∈ (S m).active := hstarS m (by omega)
  rcases hfire with ⟨hT1', hgt⟩ | ⟨hkn, h2, hgt⟩ | ⟨hkn, hle⟩
  · -- test (13)
    have bA := h23' k hT1'
    have bE := h21' k (m + 1) (by omega) le_rfl
    by_cases hkA0 : k ∈ (S m).active
    · have hge' := hge k m le_rfl hkA0
      have hEm : tauEff K n β adv I k = m + 1 := by rw [htE]; omega
      rw [hEm, rad_eq K β _ _ (m + 1) (by omega) le_rfl] at bE
      have hmin' : min (s'.2.1 k) (m + 1) = m + 1 := by
        by_cases hks : k ∈ s'.1
        · have e := ((hgood'.2 k).2 (Or.inl hks)).1
          rw [e, (hinv m).2.2 k hkA0]; omega
        · have e := ((hgood'.2 k).1 hkA0 hks).1
          rw [e]; omega
      rw [hmin', rad_eq' K β _ _ (m + 1) (by omega)] at hgt
      have := abs_sub_le (estAvg (sao K n β) adv I k (m + 1)) (μ k) (algAvg adv I k (m + 1))
      rw [abs_sub_comm (μ k)] at this
      linarith
    · obtain ⟨e1, e2⟩ := (hgood'.2 k).2 (Or.inr hkA0)
      obtain ⟨v, hv1, hvm, hmin, hpost⟩ := hdr k m (by omega) hkA0
      have hFv : (S (m + 1)).tau k = v := (hpost (m + 1) (by omega)).2.1
      have hmv : (S m).tau k = v := (hpost m hvm).2.1
      have hqv : (S m).q k = (S (v - 1)).p k := (hpost m hvm).2.2
      have hEv : tauEff K n β adv I k = v := by rw [htE, hFv]; omega
      have hp : probAt (sao K n β) adv I v = (S (v - 1)).p := by
        unfold probAt; exact sao_eq K n β _ (hlt (v - 1) (by omega))
      rw [hqE, hEv, hp] at bE
      rw [e1, e2, hmv, hqv] at hgt
      unfold estRadius at bE
      have hvle : v ≤ m + 1 := by omega
      have hmax0 : max (((m + 1 : ℕ) : ℝ) - (v : ℝ)) 0 = ((m + 1 : ℕ) : ℝ) - (v : ℝ) := by
        apply max_eq_left
        have : (v : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hvle
        linarith
      rw [Nat.min_eq_left hvle] at bE hgt
      rw [hmax0] at bE
      have := abs_sub_le (estAvg (sao K n β) adv I k (m + 1)) (μ k) (algAvg adv I k (m + 1))
      rw [abs_sub_comm (μ k)] at this
      linarith
  all_goals
    -- tests (14), (15): the arm `k` is inactive after its step
    have hkF : k ∉ (S (m + 1)).active := fun h => hkn (hsub' h)
    have hτ : s'.2.1 k = (S (m + 1)).tau k := by
      by_cases hkA0 : k ∈ (S m).active
      · rw [((hgood'.2 k).1 hkA0 hkn).1, hT1]
        have hkr : k ∉ (rnd K β (S m) o).1 := by rw [← hA1]; exact hkF
        rw [((hgr.2 k).1 hkA0 hkr).1]
      · rw [((hgood'.2 k).2 (Or.inr hkA0)).1, hT1]
        have hkr : k ∉ (rnd K β (S m) o).1 := by rw [← hA1]; exact hkF
        rw [((hgr.2 k).2 (Or.inr hkA0)).1]
    obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k (m + 1) le_rfl hkF
    have hFv : (S (m + 1)).tau k = v := (hpost (m + 1) hvw).2.1
    have hgapk := hgap k hkF
    rw [hFv] at hτ hgapk
    have hRk := hR2 k hkF (m + 1) (by omega) le_rfl
    rw [hFv] at hRk
    have bk := h21' k (m + 1) (by omega) le_rfl
    have bs := h21' istar (m + 1) (by omega) le_rfl
    rw [hR1 istar (m + 1) (by omega) le_rfl (by simpa using hstarm)] at bs
    have hvpos : (0 : ℝ) < v := by exact_mod_cast hv1
    have hvm1 : (v : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hvw
    have hwv := width_anti K β hL (v : ℝ) ((m + 1 : ℕ) : ℝ) hvpos hvm1
    rw [abs_le] at bk bs
    have hstar' : istar ∈ s'.1 := hsub' hstarF
    have hmaxS := le_maxOver s'.1 (fun i => estAvg (sao K n β) adv I i (m + 1)) istar hstar'
    have hsS : ∀ j ∈ s'.1, estAvg (sao K n β) adv I j (m + 1) ≤ μ istar + width K β v := by
      intro j hj
      have bj := h21' j (m + 1) (by omega) le_rfl
      rw [hR1 j (m + 1) (by omega) le_rfl (by simpa using hgood'.1 hj)] at bj
      rw [abs_le] at bj
      have := hmax' j
      linarith
    first
    | -- test (15)
      rw [hτ] at hle
      beta_reduce at hmaxS hle
      linarith
    | -- test (14)
      rw [hτ] at h2 hgt
      obtain ⟨j, hj, e⟩ := maxOver_mem s'.1 (fun i => estAvg (sao K n β) adv I i (m + 1))
        ⟨istar, hstar'⟩
      rw [e] at hgt
      have hj' := hsS j hj
      have hndk := hnd k hkF (by rw [hFv]; exact h2)
      rw [hFv] at hndk
      have hc : (((v - 1 : ℕ) : ℝ)) = (v : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hc] at hndk
      have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast h2
      have hwv1 := width_anti K β hL ((v : ℝ) - 1) (v : ℝ) (by linarith) (by linarith)
      beta_reduce at hgt
      linarith

end P6f9ffc20

open MeasureTheory BestBothWorlds.SAO in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (ω : Fin n → Fin K → ℝ)
    (hω : ∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1) (I : Fin n → Fin K)
    (h21 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
      |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) (tableAdv ω) I i t - mean ν i| ≤
        estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t
          (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h23 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
      1 ≤ pullCount I i t →
        |algAvg (tableAdv ω) I i t - mean ν i| ≤
          Real.sqrt (2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / pullCount I i t)) :
    tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I = n := by
  apply P6f9ffc20.main K n (by omega) _ ?_ (tableAdv ω) I (mean ν) h21 h23
  apply Real.log_nonneg
  rw [le_div_iff₀ hδ0]
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hK hKn)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hn3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hn 3
    norm_num at this
    linarith
  nlinarith
