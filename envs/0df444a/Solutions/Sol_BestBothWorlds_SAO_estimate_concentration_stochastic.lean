-- Prove2me | solution 1 for BestBothWorlds.SAO.estimate_concentration_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T03:56:27.935172+00:00
-- url     : https://prove2.me/submissions/dc1329af-2663-428b-ac86-728a441e95ea

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
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

/-- The exponential supermartingale: with per-round factors whose conditional mean is at most `1`,
the expected product is at most `1`. -/
theorem supermart {K : ℕ} (π : Policy K) (hπ0 : ∀ h j, 0 ≤ π h j) (adv : Adversary K)
    (c : ℕ → History K → Fin K → ℝ) (hc0 : ∀ r h j, 0 ≤ c r h j)
    (hc : ∀ r h, ∑ j, π h j * c r h j ≤ 1) :
    ∀ m : ℕ, ∑ I : Fin m → Fin K, pathProb π adv I *
      ∏ r : Fin m, c r ((history adv I).take r) (I r) ≤ 1 := by
  intro m
  induction m with
  | zero => simp [pathProb]
  | succ m ih =>
    rw [sum_snoc]
    have hpp : ∀ I : Fin m → Fin K, 0 ≤ pathProb π adv I * ∏ r : Fin m, c r ((history adv I).take r) (I r) :=
      fun I => mul_nonneg (Finset.prod_nonneg (fun r _ => hπ0 _ _))
        (Finset.prod_nonneg (fun r _ => hc0 _ _ _))
    have hlen : ∀ I : Fin m → Fin K, (history adv I).length = m := fun I => by simp [history]
    calc ∑ I : Fin m → Fin K, ∑ j : Fin K, pathProb π adv (Fin.snoc I j : Fin (m + 1) → Fin K) *
          ∏ r : Fin (m + 1), c r ((history adv (Fin.snoc I j : Fin (m + 1) → Fin K)).take r)
            ((Fin.snoc I j : Fin (m + 1) → Fin K) r)
        = ∑ I : Fin m → Fin K, (pathProb π adv I * ∏ r : Fin m, c r ((history adv I).take r) (I r)) *
            ∑ j, π (history adv I) j * c m (history adv I) j := by
          refine Finset.sum_congr rfl (fun I _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [pathProb_snoc', Fin.prod_univ_castSucc]
          have e1 : ∏ r : Fin m, c (Fin.castSucc r : ℕ)
              ((history adv (Fin.snoc I j : Fin (m + 1) → Fin K)).take (Fin.castSucc r : ℕ))
              ((Fin.snoc I j : Fin (m + 1) → Fin K) (Fin.castSucc r)) =
              ∏ r : Fin m, c r ((history adv I).take r) (I r) := by
            refine Finset.prod_congr rfl (fun r _ => ?_)
            simp only [Fin.val_castSucc, Fin.snoc_castSucc]
            rw [take_hist_snoc adv I j r r.isLt.le]
          have e2 : c (Fin.last m : ℕ)
              ((history adv (Fin.snoc I j : Fin (m + 1) → Fin K)).take (Fin.last m : ℕ))
              ((Fin.snoc I j : Fin (m + 1) → Fin K) (Fin.last m)) =
              c m (history adv I) j := by
            simp only [Fin.val_last, Fin.snoc_last]
            rw [take_hist_snoc adv I j m le_rfl, List.take_of_length_le (le_of_eq (hlen I))]
          rw [e1, e2]
          ring
      _ ≤ ∑ I : Fin m → Fin K, (pathProb π adv I * ∏ r : Fin m, c r ((history adv I).take r) (I r)) * 1 := by
          apply Finset.sum_le_sum
          intro I _
          exact mul_le_mul_of_nonneg_left (hc _ _) (hpp I)
      _ ≤ 1 := by simpa using ih

/-! ### The Bernoulli exponential factor. -/

theorem factor_ok {K : ℕ} (p : Fin K → ℝ) (hp1 : ∑ j, p j = 1) (i : Fin K) (lam : ℝ) :
    ∑ j, p j * Real.exp (lam * (if j = i then 1 else 0) - (Real.exp lam - 1) * p i) ≤ 1 := by
  set a := (Real.exp lam - 1) * p i with ha
  have e : ∀ j, p j * Real.exp (lam * (if j = i then 1 else 0) - a) =
      Real.exp (-a) * (p j + if j = i then p i * (Real.exp lam - 1) else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [if_true, mul_one]
      rw [sub_eq_add_neg, Real.exp_add]; ring
    · simp only [hj, if_false, mul_zero, zero_sub, add_zero]
      ring
  rw [Finset.sum_congr rfl (fun j _ => e j), ← Finset.mul_sum, Finset.sum_add_distrib, hp1,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h1 := Real.add_one_le_exp a
  have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have h3 : 1 + p i * (Real.exp lam - 1) = a + 1 := by rw [ha]; ring
  rw [h3]
  calc Real.exp (-a) * (a + 1) ≤ Real.exp (-a) * Real.exp a :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 1 := h2

noncomputable def cfac (K n : ℕ) (β lam : ℝ) (i : Fin K) (t : ℕ) (r : ℕ) (h : History K)
    (j : Fin K) : ℝ :=
  Real.exp (if r < t then lam * (if j = i then 1 else 0) - (Real.exp lam - 1) * sao K n β h i
    else 0)

theorem cfac_ok (K n : ℕ) (hK : 1 ≤ K) (β lam : ℝ) (i : Fin K) (t r : ℕ) (h : History K) :
    ∑ j, sao K n β h j * cfac K n β lam i t r h j ≤ 1 := by
  unfold cfac
  by_cases hr : r < t
  · simp only [hr, if_true]
    exact factor_ok (sao K n β h) (sao_sum K n hK β h) i lam
  · simp only [hr, if_false, Real.exp_zero, mul_one]
    rw [sao_sum K n hK β h]

noncomputable def Vsum (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (t : ℕ)
    (I : Fin n → Fin K) : ℝ :=
  ∑ r ∈ Finset.range t, sao K n β ((history adv I).take r) i

theorem fin_sum_range {n t : ℕ} (htn : t ≤ n) (g : ℕ → ℝ) :
    ∑ r : Fin n, (if (r : ℕ) < t then g r else 0) = ∑ r ∈ Finset.range t, g r := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if r < t then g r else 0) n, ← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem exp_Y (K n : ℕ) (β lam : ℝ) (adv : Adversary K) (i : Fin K) (t : ℕ) (htn : t ≤ n)
    (I : Fin n → Fin K) :
    Real.exp (lam * (pullCount I i t : ℝ) - (Real.exp lam - 1) * Vsum K n β adv i t I) =
      ∏ r : Fin n, cfac K n β lam i t r ((history adv I).take r) (I r) := by
  unfold cfac
  rw [← Real.exp_sum]
  congr 1
  have e1 : ∀ r : Fin n, (if (r : ℕ) < t then lam * (if I r = i then 1 else 0) -
      (Real.exp lam - 1) * sao K n β ((history adv I).take r) i else 0) =
      lam * (if (r : ℕ) < t ∧ I r = i then 1 else 0) -
        (Real.exp lam - 1) * (if (r : ℕ) < t then sao K n β ((history adv I).take r) i else 0) := by
    intro r
    by_cases h1 : (r : ℕ) < t <;> by_cases h2 : I r = i <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun r _ => e1 r), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hA : ∑ r : Fin n, (if (r : ℕ) < t ∧ I r = i then (1 : ℝ) else 0) = (pullCount I i t : ℝ) := by
    unfold pullCount
    rw [Finset.natCast_card_filter]
  have hB : ∑ r : Fin n, (if (r : ℕ) < t then sao K n β ((history adv I).take r) i else 0) =
      Vsum K n β adv i t I :=
    fin_sum_range htn (fun r => sao K n β ((history adv I).take r) i)
  rw [hA, hB]

theorem pullCount_le {K n : ℕ} (I : Fin n → Fin K) (i : Fin K) (t : ℕ) : pullCount I i t ≤ t := by
  unfold pullCount
  calc (Finset.univ.filter (fun r : Fin n => (r : ℕ) < t ∧ I r = i)).card
      ≤ (Finset.range t).card := by
        apply Finset.card_le_card_of_injOn (fun r : Fin n => (r : ℕ))
        · intro r hr
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr
          simp only [Finset.coe_range, Set.mem_Iio]
          exact hr.1
        · intro a _ b _ h
          exact Fin.ext h
    _ = t := Finset.card_range t

/-! ### Markov and the union bound. -/

theorem markov {K n : ℕ} (π : Policy K) (adv : Adversary K) (hpp : ∀ I : Fin n → Fin K, 0 ≤ pathProb π adv I)
    (Y : (Fin n → Fin K) → ℝ) (L : ℝ) (hY : ∑ I : Fin n → Fin K, pathProb π adv I * Real.exp (Y I) ≤ 1) :
    probEvent n π adv (fun I => L ≤ Y I) ≤ Real.exp (-L) := by
  unfold probEvent
  calc ∑ I : Fin n → Fin K, (if L ≤ Y I then pathProb π adv I else 0)
      ≤ ∑ I, pathProb π adv I * Real.exp (Y I - L) := by
        apply Finset.sum_le_sum
        intro I _
        by_cases h : L ≤ Y I
        · rw [if_pos h]
          have : 1 ≤ Real.exp (Y I - L) := Real.one_le_exp (by linarith)
          nlinarith [hpp I]
        · rw [if_neg h]
          exact mul_nonneg (hpp I) (Real.exp_pos _).le
    _ = Real.exp (-L) * ∑ I, pathProb π adv I * Real.exp (Y I) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I _ => ?_)
        rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (-L) * 1 := mul_le_mul_of_nonneg_left hY (Real.exp_pos _).le
    _ = Real.exp (-L) := mul_one _

theorem prob_ge {K n : ℕ} (π : Policy K) (adv : Adversary K) (E : (Fin n → Fin K) → Prop)
    (htot : ∑ I : Fin n → Fin K, pathProb π adv I = 1) (hpp : ∀ I : Fin n → Fin K, 0 ≤ pathProb π adv I)
    (B : ℕ → (Fin n → Fin K) → Prop) (m : ℕ) (ε : ℝ)
    (hB : ∀ I, ¬ E I → ∃ k < m, B k I)
    (hBp : ∀ k < m, probEvent n π adv (B k) ≤ ε) :
    1 - m * ε ≤ probEvent n π adv E := by
  classical
  have hsum : ∑ k ∈ Finset.range m, probEvent n π adv (B k) ≤ m * ε := by
    calc ∑ k ∈ Finset.range m, probEvent n π adv (B k) ≤ ∑ k ∈ Finset.range m, ε :=
          Finset.sum_le_sum (fun k hk => hBp k (Finset.mem_range.1 hk))
      _ = m * ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold probEvent at hsum ⊢
  rw [Finset.sum_comm] at hsum
  have hpt : ∀ I, pathProb π adv I ≤ (if E I then pathProb π adv I else 0) +
      ∑ k ∈ Finset.range m, (if B k I then pathProb π adv I else 0) := by
    intro I
    have hnn : 0 ≤ ∑ k ∈ Finset.range m, (if B k I then pathProb π adv I else 0) :=
      Finset.sum_nonneg (fun k _ => by split_ifs; exacts [hpp I, le_rfl])
    by_cases hE : E I
    · rw [if_pos hE]; linarith
    · rw [if_neg hE]
      obtain ⟨k, hk, hb⟩ := hB I hE
      have := Finset.single_le_sum (f := fun k => if B k I then pathProb π adv I else 0)
        (fun k _ => by split_ifs; exacts [hpp I, le_rfl]) (Finset.mem_range.2 hk)
      simp only [if_pos hb] at this
      linarith
  have := Finset.sum_le_sum (fun I (_ : I ∈ Finset.univ) => hpt I)
  rw [Finset.sum_add_distrib, htot] at this
  linarith

/-! ### The analytic choice of `λ`. -/

theorem exp_le_quad (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x - 1 ≤ x + 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have h3 : x ^ 3 ≤ x ^ 2 := by nlinarith
  nlinarith

theorem lam_exists (k L : ℝ) (hL : 0 < L) : ∃ lam : ℝ, 0 ≤ lam ∧ ∀ V : ℝ, 0 ≤ V →
    V + Real.sqrt (4 * V * L + 5 * L ^ 2) < k → L ≤ lam * k - (Real.exp lam - 1) * V := by
  by_cases hk : 0 ≤ k
  swap
  · refine ⟨0, le_rfl, fun V hV h => ?_⟩
    have := Real.sqrt_nonneg (4 * V * L + 5 * L ^ 2)
    exfalso; linarith
  set S := Real.sqrt (4 * k * L + 9 * L ^ 2) with hS
  have hS2 : S ^ 2 = 4 * k * L + 9 * L ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS3 : 3 * L ≤ S := by nlinarith
  set d := S - 2 * L with hd
  set v := k - d with hv
  have hdL : L ≤ d := by linarith
  have hd2 : d ^ 2 = 4 * v * L + 5 * L ^ 2 := by rw [hv, hd]; nlinarith
  have hVv : ∀ V, 0 ≤ V → V + Real.sqrt (4 * V * L + 5 * L ^ 2) < k → V ≤ v := by
    intro V hV h
    by_contra hc
    push_neg at hc
    set e := k - V with he
    have hed : e < d := by linarith
    by_cases he0 : e ≤ 0
    · have := Real.sqrt_nonneg (4 * V * L + 5 * L ^ 2); linarith
    · push_neg at he0
      have hsq : e ≤ Real.sqrt (4 * V * L + 5 * L ^ 2) := by
        apply le_trans (le_abs_self e)
        apply Real.abs_le_sqrt
        have h1 : (e + 2 * L) ^ 2 ≤ S ^ 2 := by
          apply pow_le_pow_left₀ (by linarith)
          linarith
        have h2 : e * L = k * L - V * L := by rw [he]; ring
        nlinarith
      linarith
  refine ⟨if d ≤ 2 * v ∧ 0 < v then d / (2 * v) else 1, ?_, fun V hV h => ?_⟩
  · split_ifs with hc
    · exact div_nonneg (by linarith) (by linarith [hc.2])
    · norm_num
  have hVle := hVv V hV h
  have hv0 : 0 ≤ v := le_trans hV hVle
  have chain : ∀ lam, 0 ≤ lam → lam ≤ 1 → L ≤ lam * d - 3 / 4 * lam ^ 2 * v →
      L ≤ lam * k - (Real.exp lam - 1) * V := by
    intro lam h0 h1 hmain
    have he := exp_le_quad lam h0 h1
    have hc0 : 0 ≤ lam + 3 / 4 * lam ^ 2 := by positivity
    have h2 : (Real.exp lam - 1) * V ≤ (lam + 3 / 4 * lam ^ 2) * v :=
      le_trans (mul_le_mul_of_nonneg_right he hV) (mul_le_mul_of_nonneg_left hVle hc0)
    have hx : (lam + 3 / 4 * lam ^ 2) * v = lam * v + 3 / 4 * lam ^ 2 * v := by ring
    have hk' : lam * k = lam * v + lam * d := by rw [hv]; ring
    linarith
  split_ifs with hc
  · obtain ⟨hc1, hc2⟩ := hc
    apply chain
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; exact hc1
    · have hl : d / (2 * v) * (2 * v) = d := div_mul_cancel₀ d (by linarith)
      set lam := d / (2 * v)
      have h4 : lam ^ 2 * v * (4 * v) = d ^ 2 := by rw [← hl]; ring
      have h5 : L ≤ lam ^ 2 * v := by
        by_contra hcon
        push_neg at hcon
        have : lam ^ 2 * v * (4 * v) < L * (4 * v) := mul_lt_mul_of_pos_right hcon (by linarith)
        nlinarith [sq_nonneg L]
      have h6 : lam * d = 2 * (lam ^ 2 * v) := by rw [← hl]; ring
      nlinarith
  · apply chain 1 (by norm_num) le_rfl
    push_neg at hc
    by_cases hd2v : d ≤ 2 * v
    · have hv' := hc hd2v
      have : v = 0 := le_antisymm hv' hv0
      rw [this]; norm_num; linarith
    · push_neg at hd2v
      have h2L : 2 * L ≤ d := by nlinarith [mul_nonneg hv0 hL.le]
      norm_num
      linarith

/-! ### Small harmonic step. -/

theorem inv_le_log_diff (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hm0.ne']
  have h := Real.one_sub_inv_le_log_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
  have e : 1 - (((m : ℝ) + 1) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by
    rw [inv_div]; field_simp; ring
  rw [e] at h
  exact h

end P925e7ff2

namespace P925e7ff2

open BestBothWorlds.SAO P8092e862

/-! ### The compensator `∑_{s ≤ t} p_{i,s}` is at most `q_i τ_i (1 + log t)` on `{t ≤ τ₀}`. -/

set_option maxHeartbeats 1000000 in
theorem vbound (K n : ℕ) (hK : 2 ≤ K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (htt : t ≤ tau0 K n β adv I) :
    Vsum K n β adv i t I ≤
      qEff K n β adv I i * (tauEff K n β adv I i : ℝ) * (1 + Real.log t) := by
  classical
  have hK0 : 0 < K := by omega
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
    fun u => inv12_fold K n hK0 β _ _ (inv_init K n) (inv2_init K n hK0)
  have hinv3 : ∀ u, Inv3 (S u) := fun u => inv3_fold K β _ _ (inv3_init K n)
  have htau0def : tau0 K n β adv I = (match (S n).tau0 with | some τ => τ | none => n) := rfl
  have hback : ∀ u v, v ≤ u → (S u).tau0 = none → (S v).tau0 = none := by
    intro u v hvu hu
    cases hz : (S v).tau0 with
    | none => rfl
    | some τ =>
      exfalso
      obtain ⟨l, hl⟩ := hlater v u hvu
      rw [hl, frozen_fold K β τ l _ hz, hz] at hu
      exact absurd hu (by simp)
  have htr : ∀ u, u ≤ n → (S u).tau0 = none → (S u).t = u ∧
      ∀ i, (S u).Gtil i = estReward (sao K n β) adv I i u ∧
        (S u).Ghat i = algReward adv I i u ∧ (S u).T i = pullCount I i u :=
    fun u hu hz => track K n β adv I u hu (fun v hv => hback u v hv.le hz)
  have hSt : ∀ u, (S u).t ≤ u := by
    intro u
    have h1 := t_fold K β ((history adv I).take u) (SAOState.init K n)
    have h2 : ((history adv I).take u).length ≤ u := by simp [List.length_take]
    have h3 : (SAOState.init K n).t = 0 := rfl
    show (saoState K n β _).t ≤ u
    unfold saoState
    omega
  set T0 := tau0 K n β adv I with hT0
  have hT0n : T0 ≤ n := by
    rw [htau0def]
    cases hz : (S n).tau0 with
    | none => exact le_rfl
    | some τ => exact ((hinv n).1.2.1 τ hz).trans (hSt n)
  have hlt : ∀ u, u < T0 → (S u).tau0 = none := by
    intro u hu
    cases hz : (S u).tau0 with
    | none => rfl
    | some τ =>
      exfalso
      have hτu : τ ≤ u := ((hinv u).1.2.1 τ hz).trans (hSt u)
      obtain ⟨l, hl⟩ := hlater u n (by omega)
      have hSn : S n = S u := by rw [hl]; exact frozen_fold K β τ l _ hz
      have : T0 = τ := by rw [htau0def, hSn, hz]
      omega
  have hpr : ∀ r, r < T0 → sao K n β ((history adv I).take r) = (S r).p :=
    fun r hr => sao_eq K n β _ (hlt r hr)
  have htS : ∀ u, u < T0 → (S u).t = u := fun u hu => (htr u (by omega) (hlt u hu)).1
  have hact : ∀ a b, a ≤ b → i ∈ (S b).active → i ∈ (S a).active := by
    intro a b hab hb
    by_contra ha
    obtain ⟨l, hl⟩ := hlater a b hab
    rw [hl] at hb
    exact (persist_fold2 K β i l (S a) ha).1 hb
  have hmono : ∀ d a, a + d < T0 → i ∈ (S (a + d)).active → (S a).p i ≤ (S (a + d)).p i := by
    intro d
    induction d with
    | zero => intro a _ _; exact le_rfl
    | succ d ih =>
      intro a had hi
      have e : a + (d + 1) = a + d + 1 := by omega
      rw [e] at had hi ⊢
      have hn' : a + d < n := by omega
      have h1 := ih a (by omega) (hact (a + d) (a + d + 1) (by omega) hi)
      have h2 : (S (a + d)).p i ≤ (S (a + d + 1)).p i := by
        rw [hstep (a + d) hn'] at hi ⊢
        exact mono_step K β _ _ (hinv (a + d)).1 (hlt (a + d) (by omega)) i hi
      exact h1.trans h2
  have hdr : ∀ k w, w ≤ n → k ∉ (S w).active → ∃ v, 1 ≤ v ∧ v ≤ w ∧
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
    have hnone : (S v1).tau0 = none := by
      cases hz : (S v1).tau0 with
      | none => rfl
      | some τ =>
        exfalso
        have hvS : k ∉ (S (v1 + 1)).active := by rw [← hv1]; exact hv
        rw [hstep v1 hv1n, step_frozen K β _ _ τ hz] at hvS
        exact hvS hkA
    obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, _⟩ := step_spec K β (S v1)
      (I ⟨v1, hv1n⟩, reward adv I ⟨v1, hv1n⟩ (I ⟨v1, hv1n⟩)) hnone
    have hvS : k ∉ (S (v1 + 1)).active := by rw [← hv1]; exact hv
    rw [hstep v1 hv1n, hA] at hvS
    obtain ⟨e1, e2⟩ := (hg k).1 hkA hvS
    refine ⟨v, by omega, hvw, hmin, fun w' hw' => ?_⟩
    obtain ⟨l, hl⟩ := hlater v w' hw'
    obtain ⟨a, b, c⟩ := persist_fold2 K β k l (S v) hv
    rw [hl]
    refine ⟨a, ?_, ?_⟩
    · rw [b, hv1, hstep v1 hv1n, hT, e1, (htr v1 hv1n.le hnone).1]
    · rw [c, hv1, Nat.add_sub_cancel, hstep v1 hv1n, hQ, e2]
  -- the effective time and probability of arm `i`
  set τ := tauEff K n β adv I i with hτ
  set q := qEff K n β adv I i with hq
  have htE : τ = min ((S n).tau i) T0 := rfl
  have hT0pos : 1 ≤ T0 := le_trans ht htt
  obtain ⟨hτ1, hτT, hiact, hlate⟩ : 1 ≤ τ ∧ τ ≤ T0 ∧ i ∈ (S (τ - 1)).active ∧
      (∀ r, τ ≤ r → r < T0 → (S r).p i = (S (τ - 1)).p i * τ / ((r : ℝ) + 1)) := by
    by_cases hin : i ∈ (S n).active
    · have hτn : (S n).tau i = n := (hinv n).2.2 i hin
      have hτeq : τ = T0 := by rw [htE, hτn]; omega
      refine ⟨by omega, by omega, hact (τ - 1) n (by omega) hin, fun r h1 h2 => by omega⟩
    · obtain ⟨v, hv1, hvn, hmin, hpost⟩ := hdr i n le_rfl hin
      have hτeq : τ = min v T0 := by rw [htE, (hpost n hvn).2.1]
      refine ⟨by omega, by omega, hmin (τ - 1) (by omega), fun r h1 h2 => ?_⟩
      have hτv : τ = v := by omega
      obtain ⟨a, b, c⟩ := hpost r (by omega)
      rw [hinv3 r i a, b, c, htS r h2, hτv]
  have hqeq : q = (S (τ - 1)).p i := by
    show probAt (sao K n β) adv I τ i = _
    unfold probAt
    rw [hpr (τ - 1) (by omega)]
  have hq0 : 0 ≤ q := by rw [hqeq]; exact (inv_p_bounds _ (hinv _).1 i hiact).1
  have hF : ∀ r, r < t → sao K n β ((history adv I).take r) i = (S r).p i :=
    fun r hr => by rw [hpr r (by omega)]
  have hF1 : ∀ r, r < t → r + 1 ≤ τ → sao K n β ((history adv I).take r) i ≤ q := by
    intro r hr hrτ
    rw [hF r hr, hqeq]
    have e : r + (τ - 1 - r) = τ - 1 := by omega
    have := hmono (τ - 1 - r) r (by omega) (by rw [e]; exact hiact)
    rwa [e] at this
  have hF2 : ∀ r, r < t → τ ≤ r →
      sao K n β ((history adv I).take r) i = q * τ / ((r : ℝ) + 1) := fun r hr hrτ => by
    rw [hF r hr, hqeq]; exact hlate r hrτ (by omega)
  have ph1 : ∀ t', t' ≤ t → t' ≤ τ →
      ∑ r ∈ Finset.range t', sao K n β ((history adv I).take r) i ≤ t' * q := by
    intro t'
    induction t' with
    | zero => intro _ _; simp
    | succ m ih =>
      intro h1 h2
      rw [Finset.sum_range_succ]
      have h3 := ih (by omega) (by omega)
      have h4 := hF1 m (by omega) (by omega)
      push_cast; linarith
  have hqτ : 0 ≤ q * τ := mul_nonneg hq0 (Nat.cast_nonneg _)
  have ph2 : ∀ d, τ + d ≤ t →
      ∑ r ∈ Finset.range (τ + d), sao K n β ((history adv I).take r) i ≤
        q * τ * (1 + Real.log ((τ + d : ℕ) : ℝ) - Real.log τ) := by
    intro d
    induction d with
    | zero =>
      intro h
      have := ph1 τ (by omega) le_rfl
      simp only [Nat.add_zero, sub_self, add_zero, mul_one]
      linarith [mul_comm (τ : ℝ) q]
    | succ d ih =>
      intro h
      rw [show τ + (d + 1) = (τ + d) + 1 by omega, Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hF2 (τ + d) (by omega) (by omega)
      have h3 := inv_le_log_diff (τ + d) (by omega)
      rw [h2]
      have h4 : q * τ / (((τ + d : ℕ) : ℝ) + 1) ≤
          q * τ * (Real.log (((τ + d : ℕ) : ℝ) + 1) - Real.log ((τ + d : ℕ) : ℝ)) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h3 hqτ
      push_cast at h1 h4 ⊢
      linarith
  unfold Vsum
  have hlogt : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  by_cases htτ : t ≤ τ
  · have h1 := ph1 t le_rfl htτ
    have h2 : (t : ℝ) ≤ τ := by exact_mod_cast htτ
    have h3 : (t : ℝ) * q ≤ q * τ := by nlinarith
    have h4 : 0 ≤ q * τ * Real.log t := mul_nonneg hqτ hlogt
    nlinarith
  · push_neg at htτ
    have h1 := ph2 (t - τ) (by omega)
    rw [show τ + (t - τ) = t by omega] at h1
    have hlogτ : 0 ≤ Real.log τ := Real.log_natCast_nonneg τ
    have h2 : 0 ≤ q * τ * Real.log τ := mul_nonneg hqτ hlogτ
    nlinarith

end P925e7ff2

namespace P9236924e

open BestBothWorlds.SAO P8092e862 P925e7ff2

set_option maxHeartbeats 1000000 in
theorem pstruct (K n : ℕ) (hK : 2 ≤ K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (htt : t ≤ tau0 K n β adv I) :
    1 ≤ tauEff K n β adv I i ∧ 1 / (K : ℝ) ≤ qEff K n β adv I i ∧
    (∀ r, r < t → r + 1 ≤ tauEff K n β adv I i →
      1 / (K : ℝ) ≤ sao K n β ((history adv I).take r) i) ∧
    (∀ r, r < t → tauEff K n β adv I i ≤ r →
      sao K n β ((history adv I).take r) i =
        qEff K n β adv I i * (tauEff K n β adv I i : ℝ) / ((r : ℝ) + 1)) := by
  classical
  have hK0 : 0 < K := by omega
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
    fun u => inv12_fold K n hK0 β _ _ (inv_init K n) (inv2_init K n hK0)
  have hinv3 : ∀ u, Inv3 (S u) := fun u => inv3_fold K β _ _ (inv3_init K n)
  have htau0def : tau0 K n β adv I = (match (S n).tau0 with | some τ => τ | none => n) := rfl
  have hback : ∀ u v, v ≤ u → (S u).tau0 = none → (S v).tau0 = none := by
    intro u v hvu hu
    cases hz : (S v).tau0 with
    | none => rfl
    | some τ =>
      exfalso
      obtain ⟨l, hl⟩ := hlater v u hvu
      rw [hl, frozen_fold K β τ l _ hz, hz] at hu
      exact absurd hu (by simp)
  have htr : ∀ u, u ≤ n → (S u).tau0 = none → (S u).t = u ∧
      ∀ i, (S u).Gtil i = estReward (sao K n β) adv I i u ∧
        (S u).Ghat i = algReward adv I i u ∧ (S u).T i = pullCount I i u :=
    fun u hu hz => track K n β adv I u hu (fun v hv => hback u v hv.le hz)
  have hSt : ∀ u, (S u).t ≤ u := by
    intro u
    have h1 := t_fold K β ((history adv I).take u) (SAOState.init K n)
    have h2 : ((history adv I).take u).length ≤ u := by simp [List.length_take]
    have h3 : (SAOState.init K n).t = 0 := rfl
    show (saoState K n β _).t ≤ u
    unfold saoState
    omega
  set T0 := tau0 K n β adv I with hT0
  have hT0n : T0 ≤ n := by
    rw [htau0def]
    cases hz : (S n).tau0 with
    | none => exact le_rfl
    | some τ => exact ((hinv n).1.2.1 τ hz).trans (hSt n)
  have hlt : ∀ u, u < T0 → (S u).tau0 = none := by
    intro u hu
    cases hz : (S u).tau0 with
    | none => rfl
    | some τ =>
      exfalso
      have hτu : τ ≤ u := ((hinv u).1.2.1 τ hz).trans (hSt u)
      obtain ⟨l, hl⟩ := hlater u n (by omega)
      have hSn : S n = S u := by rw [hl]; exact frozen_fold K β τ l _ hz
      have : T0 = τ := by rw [htau0def, hSn, hz]
      omega
  have hpr : ∀ r, r < T0 → sao K n β ((history adv I).take r) = (S r).p :=
    fun r hr => sao_eq K n β _ (hlt r hr)
  have htS : ∀ u, u < T0 → (S u).t = u := fun u hu => (htr u (by omega) (hlt u hu)).1
  have hact : ∀ a b, a ≤ b → i ∈ (S b).active → i ∈ (S a).active := by
    intro a b hab hb
    by_contra ha
    obtain ⟨l, hl⟩ := hlater a b hab
    rw [hl] at hb
    exact (persist_fold2 K β i l (S a) ha).1 hb
  have hdr : ∀ k w, w ≤ n → k ∉ (S w).active → ∃ v, 1 ≤ v ∧ v ≤ w ∧
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
    have hnone : (S v1).tau0 = none := by
      cases hz : (S v1).tau0 with
      | none => rfl
      | some τ =>
        exfalso
        have hvS : k ∉ (S (v1 + 1)).active := by rw [← hv1]; exact hv
        rw [hstep v1 hv1n, step_frozen K β _ _ τ hz] at hvS
        exact hvS hkA
    obtain ⟨r, ⟨hsub, hg⟩, hA, hT, hQ, _⟩ := step_spec K β (S v1)
      (I ⟨v1, hv1n⟩, reward adv I ⟨v1, hv1n⟩ (I ⟨v1, hv1n⟩)) hnone
    have hvS : k ∉ (S (v1 + 1)).active := by rw [← hv1]; exact hv
    rw [hstep v1 hv1n, hA] at hvS
    obtain ⟨e1, e2⟩ := (hg k).1 hkA hvS
    refine ⟨v, by omega, hvw, hmin, fun w' hw' => ?_⟩
    obtain ⟨l, hl⟩ := hlater v w' hw'
    obtain ⟨a, b, c⟩ := persist_fold2 K β k l (S v) hv
    rw [hl]
    refine ⟨a, ?_, ?_⟩
    · rw [b, hv1, hstep v1 hv1n, hT, e1, (htr v1 hv1n.le hnone).1]
    · rw [c, hv1, Nat.add_sub_cancel, hstep v1 hv1n, hQ, e2]
  -- the effective time and probability of arm `i`
  set τ := tauEff K n β adv I i with hτ
  set q := qEff K n β adv I i with hq
  have htE : τ = min ((S n).tau i) T0 := rfl
  have hT0pos : 1 ≤ T0 := le_trans ht htt
  obtain ⟨hτ1, hτT, hiact, hlate⟩ : 1 ≤ τ ∧ τ ≤ T0 ∧ i ∈ (S (τ - 1)).active ∧
      (∀ r, τ ≤ r → r < T0 → (S r).p i = (S (τ - 1)).p i * τ / ((r : ℝ) + 1)) := by
    by_cases hin : i ∈ (S n).active
    · have hτn : (S n).tau i = n := (hinv n).2.2 i hin
      have hτeq : τ = T0 := by rw [htE, hτn]; omega
      refine ⟨by omega, by omega, hact (τ - 1) n (by omega) hin, fun r h1 h2 => by omega⟩
    · obtain ⟨v, hv1, hvn, hmin, hpost⟩ := hdr i n le_rfl hin
      have hτeq : τ = min v T0 := by rw [htE, (hpost n hvn).2.1]
      refine ⟨by omega, by omega, hmin (τ - 1) (by omega), fun r h1 h2 => ?_⟩
      have hτv : τ = v := by omega
      obtain ⟨a, b, c⟩ := hpost r (by omega)
      rw [hinv3 r i a, b, c, htS r h2, hτv]
  have hqeq : q = (S (τ - 1)).p i := by
    show probAt (sao K n β) adv I τ i = _
    unfold probAt
    rw [hpr (τ - 1) (by omega)]
  have hq0 : 0 ≤ q := by rw [hqeq]; exact (inv_p_bounds _ (hinv _).1 i hiact).1
  have hF : ∀ r, r < t → sao K n β ((history adv I).take r) i = (S r).p i :=
    fun r hr => by rw [hpr r (by omega)]
  have hF2 : ∀ r, r < t → τ ≤ r →
      sao K n β ((history adv I).take r) i = q * τ / ((r : ℝ) + 1) := fun r hr hrτ => by
    rw [hF r hr, hqeq]; exact hlate r hrτ (by omega)
  have hF1' : ∀ r, r < t → r + 1 ≤ τ → 1 / (K : ℝ) ≤ sao K n β ((history adv I).take r) i := by
    intro r hr hrτ
    rw [hF r hr]
    exact active_p_ge K n hK0 _ (hinv r).1 (hinv r).2 i (hact r (τ - 1) (by omega) hiact)
  have hqK : 1 / (K : ℝ) ≤ q := by
    rw [hqeq]; exact active_p_ge K n hK0 _ (hinv _).1 (hinv _).2 i hiact
  exact ⟨hτ1, hqK, hF1', hF2⟩

/-! ### Arms of a history prefix. -/

theorem map_fst_take {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (r : ℕ) :
    ((history adv I).take r).map Prod.fst = (List.ofFn I).take r := by
  unfold history
  rw [List.map_take, List.map_ofFn]
  rfl

/-! ### The two-point exponential bound (Freedman-type factor). -/

theorem exp_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.mp h).2
  linarith

theorem two_point (p y g : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hy : |y| ≤ p) :
    p * Real.exp (y * (g / p - g) - y ^ 2 / p) + (1 - p) * Real.exp (y * (0 - g) - y ^ 2 / p) ≤ 1 := by
  set c1 := g / p - g with hc1
  have hpc : p * c1 = g * (1 - p) := by
    rw [hc1, mul_sub, mul_div_cancel₀ g hp0.ne']; ring
  have hc10 : 0 ≤ c1 := by
    have : g ≤ g / p := by rw [le_div_iff₀ hp0]; nlinarith
    linarith
  have hc11 : p * c1 ≤ 1 := by rw [hpc]; nlinarith
  set a := y ^ 2 / p with ha
  have hx1 : |y * c1| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hc10]
    calc |y| * c1 ≤ p * c1 := mul_le_mul_of_nonneg_right hy hc10
      _ ≤ 1 := hc11
  have hx0 : |y * (0 - g)| ≤ 1 := by
    rw [abs_mul, zero_sub, abs_neg, abs_of_nonneg hg0]
    calc |y| * g ≤ p * 1 := mul_le_mul hy hg1 hg0 hp0.le
      _ ≤ 1 := by linarith
  have e1 : Real.exp (y * c1 - a) ≤ Real.exp (-a) * (1 + y * c1 + (y * c1) ^ 2) := by
    rw [show y * c1 - a = -a + y * c1 by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad _ hx1) (Real.exp_pos _).le
  have e0 : Real.exp (y * (0 - g) - a) ≤
      Real.exp (-a) * (1 + y * (0 - g) + (y * (0 - g)) ^ 2) := by
    rw [show y * (0 - g) - a = -a + y * (0 - g) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad _ hx0) (Real.exp_pos _).le
  have hQ : p * (y * c1) ^ 2 + (1 - p) * (y * (0 - g)) ^ 2 ≤ a := by
    rw [ha, le_div_iff₀ hp0]
    have e : (p * (y * c1) ^ 2 + (1 - p) * (y * (0 - g)) ^ 2) * p = y ^ 2 * (g ^ 2 * (1 - p)) := by
      linear_combination y ^ 2 * (p * c1 + g * (1 - p)) * hpc
    rw [e]
    have h1 : g ^ 2 ≤ 1 := by nlinarith
    have h2 : g ^ 2 * (1 - p) ≤ 1 := by nlinarith
    nlinarith [sq_nonneg y]
  have hlin : p * (y * c1) + (1 - p) * (y * (0 - g)) = 0 := by
    linear_combination y * hpc
  have hea : Real.exp (-a) * (1 + a) ≤ 1 := by
    have h1 := Real.add_one_le_exp a
    have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := h2
  have hp1' : 0 ≤ 1 - p := by linarith
  have hE := Real.exp_pos (-a)
  calc p * Real.exp (y * c1 - a) + (1 - p) * Real.exp (y * (0 - g) - a)
      ≤ p * (Real.exp (-a) * (1 + y * c1 + (y * c1) ^ 2)) +
        (1 - p) * (Real.exp (-a) * (1 + y * (0 - g) + (y * (0 - g)) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hp0.le) (mul_le_mul_of_nonneg_left e0 hp1')
    _ = Real.exp (-a) * (1 + (p * (y * c1) + (1 - p) * (y * (0 - g))) +
          (p * (y * c1) ^ 2 + (1 - p) * (y * (0 - g)) ^ 2)) := by ring
    _ ≤ Real.exp (-a) * (1 + a) := by
        rw [hlin]
        exact mul_le_mul_of_nonneg_left (by linarith) hE.le
    _ ≤ 1 := hea

theorem factor2 {K : ℕ} (p : Fin K → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (i : Fin K)
    (g ℓ t : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (ht : 0 < t) (hpi : 0 < p i)
    (hℓ : |ℓ| ≤ p i * t) :
    ∑ j, p j * Real.exp (ℓ * ((if j = i then g / p i else 0) - g) / t - ℓ ^ 2 / (p i * t ^ 2)) ≤ 1 := by
  have hpi1 : p i ≤ 1 := by
    rw [← hp1]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  set y := ℓ / t with hy
  have hyb : |y| ≤ p i := by
    rw [hy, abs_div, abs_of_pos ht, div_le_iff₀ ht]; exact hℓ
  have ea : ℓ ^ 2 / (p i * t ^ 2) = y ^ 2 / p i := by
    rw [hy, div_pow, div_div, mul_comm (t ^ 2) (p i)]
  have ex : ∀ j, ℓ * ((if j = i then g / p i else 0) - g) / t =
      y * ((if j = i then g / p i else 0) - g) := by
    intro j; rw [hy]; ring
  simp only [ex, ea]
  rw [Fintype.sum_eq_add_sum_compl i]
  have hrest : ∑ j ∈ ({i}ᶜ : Finset (Fin K)),
      p j * Real.exp (y * ((if j = i then g / p i else 0) - g) - y ^ 2 / p i) =
      (1 - p i) * Real.exp (y * (0 - g) - y ^ 2 / p i) := by
    have hs : ∑ j ∈ ({i}ᶜ : Finset (Fin K)), p j = 1 - p i := by
      rw [← hp1, Fintype.sum_eq_add_sum_compl i p]; ring
    rw [← hs, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := by simpa using hj
    simp only [hji, if_false]
  rw [hrest, if_pos rfl]
  exact two_point (p i) y g hpi hpi1 hg0 hg1 hyb

/-! ### The per-round exponent and its supermartingale. -/

noncomputable def ex (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (ℓ : ℝ) (t r : ℕ)
    (h : History K) (j : Fin K) : ℝ :=
  if r < t ∧ 0 < sao K n β h i ∧ |ℓ| ≤ sao K n β h i * t then
    ℓ * ((if j = i then adv (h.map Prod.fst) i / sao K n β h i else 0) - adv (h.map Prod.fst) i) / t -
      ℓ ^ 2 / (sao K n β h i * (t : ℝ) ^ 2)
  else 0

theorem ex_ok (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (hadv : adv.IsBounded)
    (i : Fin K) (ℓ : ℝ) (t r : ℕ) (h : History K) :
    ∑ j, sao K n β h j * Real.exp (ex K n β adv i ℓ t r h j) ≤ 1 := by
  unfold ex
  by_cases hc : r < t ∧ 0 < sao K n β h i ∧ |ℓ| ≤ sao K n β h i * t
  · simp only [if_pos hc]
    have ht : (0 : ℝ) < t := by have := hc.1; exact_mod_cast (show 0 < t by omega)
    exact factor2 (sao K n β h) (sao_nonneg K n hK β h) (sao_sum K n hK β h) i _ ℓ t
      (hadv _ i).1 (hadv _ i).2 ht hc.2.1 hc.2.2
  · simp only [if_neg hc, Real.exp_zero, mul_one]
    rw [sao_sum K n hK β h]

noncomputable def Ysum (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (ℓ : ℝ) (t : ℕ)
    (I : Fin n → Fin K) : ℝ :=
  ∑ r : Fin n, ex K n β adv i ℓ t r ((history adv I).take r) (I r)

theorem Ysum_mart (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (hadv : adv.IsBounded)
    (i : Fin K) (ℓ : ℝ) (t : ℕ) :
    ∑ I : Fin n → Fin K, pathProb (sao K n β) adv I * Real.exp (Ysum K n β adv i ℓ t I) ≤ 1 := by
  have hc := supermart (sao K n β) (fun h j => sao_nonneg K n hK β h j) adv
    (fun r h j => Real.exp (ex K n β adv i ℓ t r h j)) (fun r h j => (Real.exp_pos _).le)
    (fun r h => ex_ok K n hK β adv hadv i ℓ t r h) n
  unfold Ysum
  simpa only [Real.exp_sum] using hc

theorem Y_eq (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (ℓ : ℝ) (t : ℕ) (htn : t ≤ n)
    (I : Fin n → Fin K)
    (hgood : ∀ r, r < t → 0 < sao K n β ((history adv I).take r) i ∧
      |ℓ| ≤ sao K n β ((history adv I).take r) i * t) :
    Ysum K n β adv i ℓ t I = ℓ * (estAvg (sao K n β) adv I i t - fixedAvg adv I i t) -
      ℓ ^ 2 * ∑ r ∈ Finset.range t, 1 / (sao K n β ((history adv I).take r) i * (t : ℝ) ^ 2) := by
  have e : ∀ r : Fin n, ex K n β adv i ℓ t r ((history adv I).take r) (I r) =
      ℓ / t * ((if (r : ℕ) < t ∧ I r = i then
          reward adv I r i / probAt (sao K n β) adv I (r + 1) i else 0) -
        (if (r : ℕ) < t then reward adv I r i else 0)) -
      ℓ ^ 2 * (if (r : ℕ) < t then
          1 / (sao K n β ((history adv I).take r) i * (t : ℝ) ^ 2) else 0) := by
    intro r
    have hp : probAt (sao K n β) adv I (r + 1) i = sao K n β ((history adv I).take r) i := by
      unfold probAt; rw [Nat.add_sub_cancel]
    have hg : adv (((history adv I).take r).map Prod.fst) i = reward adv I r i := by
      rw [map_fst_take]; rfl
    unfold ex
    by_cases hr : (r : ℕ) < t
    · rw [if_pos ⟨hr, hgood r hr⟩, hg, hp]
      by_cases hi : I r = i
      · simp only [hi, hr, and_self, if_true]; ring
      · simp only [hi, hr, and_false, if_false, if_true]; ring
    · simp only [hr, false_and, if_false]; ring
  have hV := fin_sum_range htn (fun r => 1 / (sao K n β ((history adv I).take r) i * (t : ℝ) ^ 2))
  unfold Ysum estAvg fixedAvg estReward cumReward
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter, hV]
  ring

/-! ### The predictable variance. -/

theorem wsum_le (K : ℕ) (hK : 1 ≤ K) (t τ : ℕ) (q : ℝ) (P : ℕ → ℝ) (ht : 1 ≤ t) (hτ : 1 ≤ τ)
    (hq : 1 / (K : ℝ) ≤ q)
    (h1 : ∀ r, r < t → r + 1 ≤ τ → 1 / (K : ℝ) ≤ P r)
    (h2 : ∀ r, r < t → τ ≤ r → P r = q * τ / ((r : ℝ) + 1)) :
    ∑ r ∈ Finset.range t, 1 / (P r * (t : ℝ) ^ 2) ≤
      K * (min τ t : ℕ) / (t : ℝ) ^ 2 + max ((t : ℝ) - τ) 0 / (q * τ * t) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  set C := (t : ℝ) / (q * τ) with hC
  have hC0 : 0 ≤ C := div_nonneg ht0.le (mul_pos hq0 hτ0).le
  have claim : ∀ m, m ≤ t → ∑ r ∈ Finset.range m, 1 / P r ≤
      K * ((min τ m : ℕ) : ℝ) + ((m - τ : ℕ) : ℝ) * C := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      have ih' := ih (by omega)
      by_cases hmτ : m + 1 ≤ τ
      · have e1 : min τ (m + 1) = min τ m + 1 := by omega
        have e2 : m + 1 - τ = m - τ := by omega
        rw [e1, e2]
        have hPm := h1 m (by omega) hmτ
        have hb : 1 / P m ≤ K := by
          have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / K) hPm
          simpa using this
        push_cast at ih' ⊢
        linarith
      · push_neg at hmτ
        have e1 : min τ (m + 1) = min τ m := by omega
        have e2 : m + 1 - τ = (m - τ) + 1 := by omega
        rw [e1, e2]
        have hPm := h2 m (by omega) (by omega)
        have hb : 1 / P m ≤ C := by
          rw [hPm, one_div_div, hC]
          have : ((m : ℕ) : ℝ) + 1 ≤ t := by exact_mod_cast (show m + 1 ≤ t by omega)
          exact div_le_div_of_nonneg_right this (mul_pos hq0 hτ0).le
        push_cast at ih' ⊢
        linarith
  have hcl := claim t le_rfl
  have hsum : ∑ r ∈ Finset.range t, 1 / (P r * (t : ℝ) ^ 2) =
      (∑ r ∈ Finset.range t, 1 / P r) / (t : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [div_div]
  rw [hsum, div_le_iff₀ (by positivity)]
  have hmax : ((t - τ : ℕ) : ℝ) = max ((t : ℝ) - τ) 0 := by
    by_cases h : τ ≤ t
    · have : (τ : ℝ) ≤ t := by exact_mod_cast h
      rw [Nat.cast_sub h, max_eq_left (by linarith)]
    · push_neg at h
      have : (t : ℝ) < τ := by exact_mod_cast h
      rw [Nat.sub_eq_zero_of_le h.le, max_eq_right (by linarith)]
      simp
  have e : (K * (min τ t : ℕ) / (t : ℝ) ^ 2 + max ((t : ℝ) - τ) 0 / (q * τ * t)) * (t : ℝ) ^ 2 =
      K * ((min τ t : ℕ) : ℝ) + max ((t : ℝ) - τ) 0 * C := by
    rw [hC]; field_simp
  rw [e, ← hmax]
  exact hcl

theorem vh_le (K : ℕ) (hK : 1 ≤ K) (τ t : ℕ) (q : ℝ) (hτ : 1 ≤ τ) (ht : 1 ≤ t)
    (hq : 1 / (K : ℝ) ≤ q) :
    ((K : ℝ) * (min τ t : ℕ) / (t : ℝ) ^ 2 + max ((t : ℝ) - τ) 0 / (q * τ * t)) *
      ((min τ t : ℕ) : ℝ) ^ 2 ≤ K * t := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hKq : 1 ≤ K * q := by
    rw [div_le_iff₀ hK0] at hq; linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  by_cases h : t ≤ τ
  · rw [Nat.min_eq_right h]
    have : (t : ℝ) ≤ τ := by exact_mod_cast h
    rw [max_eq_right (by linarith)]
    field_simp
    nlinarith
  · push_neg at h
    rw [Nat.min_eq_left h.le]
    have hτt : (τ : ℝ) < t := by exact_mod_cast h
    rw [max_eq_left (by linarith)]
    have T1 : (K : ℝ) * τ / (t : ℝ) ^ 2 * (τ : ℝ) ^ 2 ≤ K * τ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (τ : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith
      have h3 : 0 ≤ (K : ℝ) * τ := by positivity
      nlinarith
    have T2 : ((t : ℝ) - τ) / (q * τ * t) * (τ : ℝ) ^ 2 ≤ K * ((t : ℝ) - τ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h1 : 0 ≤ ((t : ℝ) - τ) * τ * t := by
        have : 0 ≤ (t : ℝ) - τ := by linarith
        positivity
      have h2 : ((t : ℝ) - τ) * τ * τ ≤ ((t : ℝ) - τ) * τ * t := by
        have : 0 ≤ ((t : ℝ) - τ) * τ := by
          have : 0 ≤ (t : ℝ) - τ := by linarith
          positivity
        exact mul_le_mul_of_nonneg_left hτt.le this
      have h3 : ((t : ℝ) - τ) * τ * t ≤ ((t : ℝ) - τ) * τ * t * (K * q) := by
        nlinarith
      nlinarith
    rw [add_mul]
    nlinarith

/-! ### The choice of `λ` on a grid of step `5/4` in the normalized variance. -/

noncomputable def mu (k : ℕ) : ℝ :=
  Real.sqrt (4 * ((k : ℝ) * (5 / 4)) + 5) / (2 * ((k : ℝ) * (5 / 4) + 5 / 4))

theorem mu_bounds (k : ℕ) : 0 ≤ mu k ∧ mu k ≤ 1 := by
  have hv : (0 : ℝ) ≤ (k : ℝ) * (5 / 4) := by positivity
  have hd : (0 : ℝ) < 2 * ((k : ℝ) * (5 / 4) + 5 / 4) := by positivity
  refine ⟨div_nonneg (Real.sqrt_nonneg _) hd.le, ?_⟩
  rw [mu, div_le_one hd, Real.sqrt_le_left hd.le]
  nlinarith

theorem key_ineq (D V Vh L c : ℝ) (k : ℕ) (hc : 0 < c) (hL : 0 < L) (hV : V ≤ Vh)
    (hk1 : (k : ℝ) * (5 / 4) * L ≤ Vh * c ^ 2)
    (hk2 : Vh * c ^ 2 ≤ ((k : ℝ) * (5 / 4) + 5 / 4) * L)
    (hD : Real.sqrt (4 * Vh * L + 5 * (L / c) ^ 2) < |D|) :
    ∃ s : Bool, L ≤ ((if s then 1 else -1) * mu k * c) * D -
      ((if s then 1 else -1) * mu k * c) ^ 2 * V := by
  have hv0 : (0 : ℝ) ≤ (k : ℝ) * (5 / 4) := by positivity
  have hw : (0 : ℝ) < (k : ℝ) * (5 / 4) + 5 / 4 := by positivity
  obtain ⟨hm0, -⟩ := mu_bounds k
  have hmu : mu k = Real.sqrt (4 * ((k : ℝ) * (5 / 4)) + 5) / (2 * ((k : ℝ) * (5 / 4) + 5 / 4)) := rfl
  set v := (k : ℝ) * (5 / 4) with hv
  set S := Real.sqrt (4 * v + 5) with hS
  have hS2 : S ^ 2 = 4 * v + 5 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set m := mu k with hm
  have hid : m * S - m ^ 2 * (v + 5 / 4) = 1 := by
    rw [hmu]
    field_simp
    nlinarith [hS2]
  have hR : S * L / c ≤ Real.sqrt (4 * Vh * L + 5 * (L / c) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have e : (S * L / c) ^ 2 = (4 * v + 5) * (L / c) ^ 2 := by rw [← hS2]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hk1 hL.le
    have : v * (L / c) ^ 2 ≤ Vh * L := by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [h1]
    nlinarith [this]
  have hD' : S * L / c ≤ |D| := le_of_lt (lt_of_le_of_lt hR hD)
  have hA : m * S * L ≤ m * c * |D| := by
    have h := mul_le_mul_of_nonneg_left hD' (mul_nonneg hm0 hc.le)
    have e : m * c * (S * L / c) = m * S * L := by field_simp
    linarith
  have hB : (m * c) ^ 2 * V ≤ m ^ 2 * ((v + 5 / 4) * L) := by
    have h1 : (m * c) ^ 2 * V ≤ (m * c) ^ 2 * Vh := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
    have h2 : (m * c) ^ 2 * Vh = m ^ 2 * (Vh * c ^ 2) := by ring
    have h3 : m ^ 2 * (Vh * c ^ 2) ≤ m ^ 2 * ((v + 5 / 4) * L) :=
      mul_le_mul_of_nonneg_left hk2 (sq_nonneg _)
    linarith
  have hL1 : m * S * L - m ^ 2 * ((v + 5 / 4) * L) = L := by linear_combination L * hid
  have key : ∀ σ : ℝ, σ ^ 2 = 1 → σ * D = |D| → L ≤ (σ * m * c) * D - (σ * m * c) ^ 2 * V := by
    intro σ hσ2 hσD
    have e1 : (σ * m * c) * D = m * c * |D| := by rw [← hσD]; ring
    have e2 : (σ * m * c) ^ 2 * V = (m * c) ^ 2 * V := by
      rw [show (σ * m * c) ^ 2 = σ ^ 2 * (m * c) ^ 2 by ring, hσ2, one_mul]
    rw [e1, e2]
    linarith
  by_cases hD0 : 0 ≤ D
  · refine ⟨true, ?_⟩
    have := key 1 (by norm_num) (by rw [one_mul, abs_of_nonneg hD0])
    simpa using this
  · push_neg at hD0
    refine ⟨false, ?_⟩
    have := key (-1) (by norm_num) (by rw [abs_of_neg hD0]; ring)
    simpa using this

/-! ### Union bound over a finite index type. -/

theorem prob_ge2 {K n : ℕ} {ι : Type} [Fintype ι] (π : Policy K) (adv : Adversary K)
    (E : (Fin n → Fin K) → Prop)
    (htot : ∑ I : Fin n → Fin K, pathProb π adv I = 1) (hpp : ∀ I : Fin n → Fin K, 0 ≤ pathProb π adv I)
    (B : ι → (Fin n → Fin K) → Prop) (ε : ℝ)
    (hB : ∀ I, ¬ E I → ∃ k, B k I)
    (hBp : ∀ k, probEvent n π adv (B k) ≤ ε) :
    1 - Fintype.card ι * ε ≤ probEvent n π adv E := by
  classical
  have hsum : ∑ k, probEvent n π adv (B k) ≤ Fintype.card ι * ε := by
    calc ∑ k, probEvent n π adv (B k) ≤ ∑ _k : ι, ε := Finset.sum_le_sum (fun k _ => hBp k)
      _ = Fintype.card ι * ε := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold probEvent at hsum ⊢
  rw [Finset.sum_comm] at hsum
  have hpt : ∀ I, pathProb π adv I ≤ (if E I then pathProb π adv I else 0) +
      ∑ k, (if B k I then pathProb π adv I else 0) := by
    intro I
    have hnn : 0 ≤ ∑ k, (if B k I then pathProb π adv I else 0) :=
      Finset.sum_nonneg (fun k _ => by split_ifs; exacts [hpp I, le_rfl])
    by_cases hE : E I
    · rw [if_pos hE]; linarith
    · rw [if_neg hE]
      obtain ⟨k, hb⟩ := hB I hE
      have := Finset.single_le_sum (f := fun k => if B k I then pathProb π adv I else 0)
        (fun k _ => by split_ifs; exacts [hpp I, le_rfl]) (Finset.mem_univ k)
      simp only [if_pos hb] at this
      linarith
  have := Finset.sum_le_sum (fun I (_ : I ∈ Finset.univ) => hpt I)
  rw [Finset.sum_add_distrib, htot] at this
  linarith

end P9236924e
/-! Copied from our accepted proof of `BestBothWorlds.SAO.sum_q_le_harmonic` (5292263e). -/

namespace P5292263e

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


end P5292263e

namespace Pd1470854

open BestBothWorlds.SAO

section DMsec

variable {Ω : Type} [MeasurableSpace Ω]

/-- A map into a discrete type all of whose fibres are measurable. -/
def DM {D : Type} (c : Ω → D) : Prop := ∀ d, MeasurableSet (c ⁻¹' {d})

theorem DM.const {D : Type} (d0 : D) : DM (fun _ : Ω => d0) := by
  intro d
  by_cases h : d0 = d
  · subst h; simp
  · have : (fun _ : Ω => d0) ⁻¹' {d} = ∅ := by ext; simp [h]
    rw [this]; exact MeasurableSet.empty

theorem DM.pre {D : Type} [Countable D] {c : Ω → D} (hc : DM c) (s : Set D) :
    MeasurableSet (c ⁻¹' s) := by
  have : c ⁻¹' s = ⋃ d ∈ s, c ⁻¹' {d} := by ext ω; simp
  rw [this]; exact MeasurableSet.biUnion (Set.to_countable s) (fun d _ => hc d)

theorem DM.map {D E : Type} [Countable D] {c : Ω → D} (hc : DM c) (φ : D → E) :
    DM (fun ω => φ (c ω)) :=
  fun e => hc.pre (φ ⁻¹' {e})

theorem DM.pair {D E : Type} {c : Ω → D} {c' : Ω → E} (hc : DM c) (hc' : DM c') :
    DM (fun ω => (c ω, c' ω)) := by
  intro ⟨d, e⟩
  have : (fun ω => (c ω, c' ω)) ⁻¹' {(d, e)} = c ⁻¹' {d} ∩ c' ⁻¹' {e} := by ext ω; simp
  rw [this]; exact (hc d).inter (hc' e)

theorem DM.piece {D E : Type} [Countable D] {c : Ω → D} (hc : DM c) {f : Ω → E}
    (g : D → Ω → E) (hg : ∀ d, DM (g d)) (hf : ∀ ω, f ω = g (c ω) ω) : DM f := by
  intro e
  have : f ⁻¹' {e} = ⋃ d, c ⁻¹' {d} ∩ g d ⁻¹' {e} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff, hf]
    constructor
    · intro h; exact ⟨c ω, rfl, h⟩
    · rintro ⟨d, rfl, h⟩; exact h
  rw [this]; exact MeasurableSet.iUnion (fun d => (hc d).inter (hg d e))

theorem meas_piece {D : Type} [Countable D] {c : Ω → D} (hc : DM c) {f : Ω → ℝ}
    (g : D → Ω → ℝ) (hg : ∀ d, Measurable (g d)) (hf : ∀ ω, f ω = g (c ω) ω) :
    Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ d, c ⁻¹' {d} ∩ g d ⁻¹' s := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff, hf]
    constructor
    · intro h; exact ⟨c ω, rfl, h⟩
    · rintro ⟨d, rfl, h⟩; exact h
  rw [this]; exact MeasurableSet.iUnion (fun d => (hc d).inter (hg d hs))

theorem DM.ite {D : Type} {P : Ω → Prop} {_ : DecidablePred P} (hP : MeasurableSet {ω | P ω})
    {f g : Ω → D} (hf : DM f) (hg : DM g) : DM (fun ω => if P ω then f ω else g ω) := by
  intro d
  have : (fun ω => if P ω then f ω else g ω) ⁻¹' {d} =
      ({ω | P ω} ∩ f ⁻¹' {d}) ∪ ({ω | P ω}ᶜ ∩ g ⁻¹' {d}) := by
    ext ω; by_cases h : P ω <;> simp [h]
  rw [this]; exact (hP.inter (hf d)).union (hP.compl.inter (hg d))

theorem DM.bool {f : Ω → Bool} (h : MeasurableSet {ω | f ω = true}) : DM f := by
  intro d
  cases d
  · have : f ⁻¹' {false} = {ω | f ω = true}ᶜ := by ext ω; simp
    rw [this]; exact h.compl
  · exact h

end DMsec

theorem meas_maxOver {Ω : Type} [MeasurableSpace Ω] {K : ℕ} (A : Finset (Fin K))
    {H : Ω → Fin K → ℝ} (hH : ∀ j, Measurable fun ω => H ω j) :
    Measurable fun ω => maxOver A (H ω) := by
  unfold maxOver
  by_cases h : A.Nonempty
  · simp only [h, dif_pos]
    have := Finset.measurable_sup' h (f := fun j ω => H ω j) (fun j _ => hH j)
    convert this using 1
    ext ω
    simp [Finset.sup'_apply]
  · simp [h]

/-! ### The inner loop of SAO with one branch of (12) fixed. -/

open Classical in
noncomputable def armOut (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (A' : Finset (Fin K)) (tau' : Fin K → ℕ) (q' : Fin K → ℝ) (b : Bool) (i : Fin K) :
    Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool :=
  let tstar : ℕ := min (tau' i) t
  let test13 : Prop := 1 ≤ T i ∧
    |Ht i - Hh i| > Real.sqrt (2 * Real.log β / T i) +
      Real.sqrt (4 * (K * tstar / (t : ℝ) ^ 2 + ((t : ℝ) - tstar) / (q' i * tau' i * t)) *
        Real.log β + 5 * (K * Real.log β / tstar) ^ 2)
  let test14 : Prop := i ∉ A' ∧ 2 ≤ tau' i ∧
    maxOver A' Ht - Ht i > 10 * width K β ((tau' i : ℝ) - 1)
  let test15 : Prop := i ∉ A' ∧ maxOver A' Ht - Ht i ≤ 2 * width K β (tau' i)
  (A', tau', q', b || decide (test13 ∨ test14 ∨ test15))

open Classical in
theorem armStep_eq (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (A : Finset (Fin K)) (tau : Fin K → ℕ) (q : Fin K → ℝ) (b : Bool) (i : Fin K) :
    armStep K β t p Ht Hh T (A, tau, q, b) i =
      if (i ∈ A ∧ maxOver A Ht - Ht i > 6 * width K β t) then
        armOut K β t p Ht Hh T (A.erase i) (Function.update tau i t) (Function.update q i (p i)) b i
      else armOut K β t p Ht Hh T A tau q b i := by
  dsimp only [armStep, armOut]
  split_ifs <;> rfl

theorem armOut_meas {Ω : Type} [MeasurableSpace Ω] (K : ℕ) (β : ℝ) (t : ℕ)
    (p Ht Hh q' : Ω → Fin K → ℝ) (hp : ∀ j, Measurable fun ω => p ω j)
    (hHt : ∀ j, Measurable fun ω => Ht ω j) (hHh : ∀ j, Measurable fun ω => Hh ω j)
    (hq : ∀ j, Measurable fun ω => q' ω j) (T : Fin K → ℕ)
    (A' : Finset (Fin K)) (tau' : Fin K → ℕ) (b : Bool) (i : Fin K) :
    MeasurableSet {ω | (armOut K β t (p ω) (Ht ω) (Hh ω) T A' tau' (q' ω) b i).2.2.2 = true} := by
  have hM := meas_maxOver A' hHt
  simp only [armOut, Bool.or_eq_true, decide_eq_true_eq]
  simp only [Set.ofPred_or, Set.ofPred_and]
  repeat' first
    | exact MeasurableSet.const _
    | apply MeasurableSet.union
    | apply MeasurableSet.inter
    | apply measurableSet_lt
    | apply measurableSet_le
    | exact (hM.sub (hHt i))
    | exact ((hHt i).sub (hHh i)).abs
    | fun_prop

/-! ### Measurability of the inner loop. -/

section Inner

variable {Ω : Type} [MeasurableSpace Ω]

def IGood {K : ℕ} (s : Ω → Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool) : Prop :=
  DM (fun ω => ((s ω).1, (s ω).2.1, (s ω).2.2.2)) ∧ ∀ j, Measurable fun ω => (s ω).2.2.1 j

theorem armOut_IGood (K : ℕ) (β : ℝ) (t : ℕ)
    (p Ht Hh q' : Ω → Fin K → ℝ) (hp : ∀ j, Measurable fun ω => p ω j)
    (hHt : ∀ j, Measurable fun ω => Ht ω j) (hHh : ∀ j, Measurable fun ω => Hh ω j)
    (hq : ∀ j, Measurable fun ω => q' ω j) (T : Fin K → ℕ)
    (A' : Finset (Fin K)) (tau' : Fin K → ℕ) (b : Bool) (i : Fin K) :
    IGood (fun ω => armOut K β t (p ω) (Ht ω) (Hh ω) T A' tau' (q' ω) b i) := by
  refine ⟨?_, fun j => hq j⟩
  have hB := DM.bool (armOut_meas K β t p Ht Hh q' hp hHt hHh hq T A' tau' b i)
  exact (DM.const A').pair ((DM.const tau').pair hB)

theorem armStep_IGood (K : ℕ) (β : ℝ) (t : ℕ)
    (p Ht Hh : Ω → Fin K → ℝ) (hp : ∀ j, Measurable fun ω => p ω j)
    (hHt : ∀ j, Measurable fun ω => Ht ω j) (hHh : ∀ j, Measurable fun ω => Hh ω j)
    (T : Fin K → ℕ) (s : Ω → Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool)
    (hs : IGood s) (i : Fin K) :
    IGood (fun ω => armStep K β t (p ω) (Ht ω) (Hh ω) T (s ω) i) := by
  obtain ⟨hc, hq⟩ := hs
  set c := fun ω => ((s ω).1, (s ω).2.1, (s ω).2.2.2) with hcdef
  let P : Finset (Fin K) → Ω → Prop := fun A ω => i ∈ A ∧ maxOver A (Ht ω) - Ht ω i > 6 * width K β t
  have hPm : ∀ A, MeasurableSet {ω | P A ω} := by
    intro A
    have hM := meas_maxOver A hHt
    exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (hM.sub (hHt i)))
  have hrw : ∀ ω, armStep K β t (p ω) (Ht ω) (Hh ω) T (s ω) i =
      (fun d : Finset (Fin K) × (Fin K → ℕ) × Bool => fun ω =>
        if P d.1 ω then
          armOut K β t (p ω) (Ht ω) (Hh ω) T (d.1.erase i) (Function.update d.2.1 i t)
            (Function.update (s ω).2.2.1 i (p ω i)) d.2.2 i
        else armOut K β t (p ω) (Ht ω) (Hh ω) T d.1 d.2.1 (s ω).2.2.1 d.2.2 i) (c ω) ω := by
    intro ω
    exact armStep_eq K β t (p ω) (Ht ω) (Hh ω) T (s ω).1 (s ω).2.1 (s ω).2.2.1 (s ω).2.2.2 i
  have hqu : ∀ j, Measurable fun ω => Function.update (s ω).2.2.1 i (p ω i) j := by
    intro j
    by_cases hji : j = i
    · subst hji; simpa using hp j
    · simpa [Function.update_of_ne hji] using hq j
  constructor
  · refine DM.piece hc (fun d ω => ((if P d.1 ω then
          armOut K β t (p ω) (Ht ω) (Hh ω) T (d.1.erase i) (Function.update d.2.1 i t)
            (Function.update (s ω).2.2.1 i (p ω i)) d.2.2 i
        else armOut K β t (p ω) (Ht ω) (Hh ω) T d.1 d.2.1 (s ω).2.2.1 d.2.2 i).1,
        (if P d.1 ω then
          armOut K β t (p ω) (Ht ω) (Hh ω) T (d.1.erase i) (Function.update d.2.1 i t)
            (Function.update (s ω).2.2.1 i (p ω i)) d.2.2 i
        else armOut K β t (p ω) (Ht ω) (Hh ω) T d.1 d.2.1 (s ω).2.2.1 d.2.2 i).2.1,
        (if P d.1 ω then
          armOut K β t (p ω) (Ht ω) (Hh ω) T (d.1.erase i) (Function.update d.2.1 i t)
            (Function.update (s ω).2.2.1 i (p ω i)) d.2.2 i
        else armOut K β t (p ω) (Ht ω) (Hh ω) T d.1 d.2.1 (s ω).2.2.1 d.2.2 i).2.2.2)) ?_ ?_
    · intro d
      have h1 := (armOut_IGood K β t p Ht Hh (fun ω => Function.update (s ω).2.2.1 i (p ω i))
        hp hHt hHh hqu T (d.1.erase i) (Function.update d.2.1 i t) d.2.2 i).1
      have h2 := (armOut_IGood K β t p Ht Hh (fun ω => (s ω).2.2.1)
        hp hHt hHh hq T d.1 d.2.1 d.2.2 i).1
      have := @DM.ite Ω _ _ (P d.1) (fun ω => Classical.propDecidable _) (hPm d.1) _ _ h1 h2
      convert this using 2 with ω
      split_ifs <;> rfl
    · intro ω; dsimp only; rw [hrw ω]
  · intro j
    refine meas_piece hc (fun d ω => (if P d.1 ω then
          armOut K β t (p ω) (Ht ω) (Hh ω) T (d.1.erase i) (Function.update d.2.1 i t)
            (Function.update (s ω).2.2.1 i (p ω i)) d.2.2 i
        else armOut K β t (p ω) (Ht ω) (Hh ω) T d.1 d.2.1 (s ω).2.2.1 d.2.2 i).2.2.1 j) ?_ ?_
    · intro d
      have : Measurable fun ω => if P d.1 ω then Function.update (s ω).2.2.1 i (p ω i) j else (s ω).2.2.1 j := by
        classical exact Measurable.ite (hPm d.1) (hqu j) (hq j)
      convert this using 2 with ω
      split_ifs <;> rfl
    · intro ω; dsimp only; rw [hrw ω]

theorem fold_IGood (K : ℕ) (β : ℝ) (t : ℕ)
    (p Ht Hh : Ω → Fin K → ℝ) (hp : ∀ j, Measurable fun ω => p ω j)
    (hHt : ∀ j, Measurable fun ω => Ht ω j) (hHh : ∀ j, Measurable fun ω => Hh ω j)
    (T : Fin K → ℕ) (l : List (Fin K)) :
    ∀ (s : Ω → Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool), IGood s →
      IGood (fun ω => l.foldl (armStep K β t (p ω) (Ht ω) (Hh ω) T) (s ω)) := by
  induction l with
  | nil => intro s hs; exact hs
  | cons i l ih =>
    intro s hs
    exact ih _ (armStep_IGood K β t p Ht Hh hp hHt hHh T s hs i)

end Inner

/-! ### Measurability of the SAO state along a run. -/

section Outer

variable {Ω : Type} [MeasurableSpace Ω]

def disc {K : ℕ} (s : SAOState K) : ℕ × Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℕ) × Option ℕ :=
  (s.t, s.active, s.tau, s.T, s.tau0)

def mk {K : ℕ} (d : ℕ × Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℕ) × Option ℕ) (s : SAOState K) :
    SAOState K :=
  { s with t := d.1, active := d.2.1, tau := d.2.2.1, T := d.2.2.2.1, tau0 := d.2.2.2.2 }

def SGood {K : ℕ} (S : Ω → SAOState K) : Prop :=
  DM (fun ω => disc (S ω)) ∧ (∀ i, Measurable fun ω => (S ω).p i) ∧
    (∀ i, Measurable fun ω => (S ω).q i) ∧ (∀ i, Measurable fun ω => (S ω).Gtil i) ∧
    (∀ i, Measurable fun ω => (S ω).Ghat i)

theorem piece_SGood (K : ℕ) (β : ℝ) (S : Ω → SAOState K) (hS : SGood S) (a : Fin K)
    (g : Ω → ℝ) (hg : Measurable g)
    (d : ℕ × Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℕ) × Option ℕ) :
    SGood (fun ω => saoStep K β (mk d (S ω)) (a, g ω)) := by
  obtain ⟨hc, hp, hq, hG1, hG2⟩ := hS
  obtain ⟨t, A, tau, T, z⟩ := d
  cases z with
  | some τ =>
    exact ⟨DM.const (t, A, tau, T, some τ), hp, hq, hG1, hG2⟩
  | none =>
    let Gt : Ω → Fin K → ℝ := fun ω i => (S ω).Gtil i + (if a = i then g ω / (S ω).p i else 0)
    let Gh : Ω → Fin K → ℝ := fun ω i => (S ω).Ghat i + (if a = i then g ω else 0)
    let T' : Fin K → ℕ := fun i => T i + (if a = i then 1 else 0)
    let Ht : Ω → Fin K → ℝ := fun ω i => Gt ω i / ((t + 1 : ℕ) : ℝ)
    let Hh : Ω → Fin K → ℝ := fun ω i => Gh ω i / (T' i : ℝ)
    have hGt : ∀ i, Measurable fun ω => Gt ω i := by
      intro i
      by_cases h : a = i
      · simp only [Gt, h, if_true]; exact (hG1 i).add (hg.div (hp i))
      · simp only [Gt, h, if_false, add_zero]; exact hG1 i
    have hGh : ∀ i, Measurable fun ω => Gh ω i := by
      intro i
      by_cases h : a = i
      · simp only [Gh, h, if_true]; exact (hG2 i).add hg
      · simp only [Gh, h, if_false, add_zero]; exact hG2 i
    have hHt : ∀ i, Measurable fun ω => Ht ω i := fun i => (hGt i).div_const _
    have hHh : ∀ i, Measurable fun ω => Hh ω i := fun i => (hGh i).div_const _
    let r := fun ω => (List.finRange K).foldl
      (armStep K β (t + 1) ((S ω).p) (Ht ω) (Hh ω) T') (A, tau, (S ω).q, false)
    have hr : IGood r := fold_IGood K β (t + 1) (fun ω => (S ω).p) Ht Hh hp hHt hHh T' _ _
      ⟨DM.const (A, tau, false), hq⟩
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨?_, ?_, ?_, hGt, hGh⟩
    · exact hr1.map (fun e => (t + 1, e.1, e.2.1, T', if e.2.2 then some (t + 1) else none))
    · intro i
      refine meas_piece hr1 (fun e ω => if i ∈ e.1 then
          (1 - ∑ j ∈ Finset.univ \ e.1, (r ω).2.2.1 j * e.2.1 j / (((t + 1 : ℕ) : ℝ) + 1)) / e.1.card
        else (r ω).2.2.1 i * e.2.1 i / (((t + 1 : ℕ) : ℝ) + 1)) ?_ (fun ω => rfl)
      intro e
      by_cases hi : i ∈ e.1
      · simp only [hi, if_true]
        refine (measurable_const.sub (Finset.measurable_sum _ (fun j _ => ?_))).div_const _
        exact ((hr2 j).mul_const _).div_const _
      · simp only [hi, if_false]
        exact ((hr2 i).mul_const _).div_const _
    · exact hr2

theorem step_SGood (K : ℕ) (β : ℝ) (S : Ω → SAOState K) (hS : SGood S) (a : Fin K)
    (g : Ω → ℝ) (hg : Measurable g) : SGood (fun ω => saoStep K β (S ω) (a, g ω)) := by
  have key := piece_SGood K β S hS a g hg
  refine ⟨DM.piece hS.1 (fun d ω => disc (saoStep K β (mk d (S ω)) (a, g ω)))
      (fun d => (key d).1) (fun ω => rfl), fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact meas_piece hS.1 (fun d ω => (saoStep K β (mk d (S ω)) (a, g ω)).p i)
      (fun d => (key d).2.1 i) (fun ω => rfl)
  · exact meas_piece hS.1 (fun d ω => (saoStep K β (mk d (S ω)) (a, g ω)).q i)
      (fun d => (key d).2.2.1 i) (fun ω => rfl)
  · exact meas_piece hS.1 (fun d ω => (saoStep K β (mk d (S ω)) (a, g ω)).Gtil i)
      (fun d => (key d).2.2.2.1 i) (fun ω => rfl)
  · exact meas_piece hS.1 (fun d ω => (saoStep K β (mk d (S ω)) (a, g ω)).Ghat i)
      (fun d => (key d).2.2.2.2 i) (fun ω => rfl)

def ev {K : ℕ} (ω : Ω) (x : Fin K × (Ω → ℝ)) : Fin K × ℝ := (x.1, x.2 ω)

theorem fold_SGood (K : ℕ) (β : ℝ) (L : List (Fin K × (Ω → ℝ))) :
    (∀ x ∈ L, Measurable x.2) → ∀ S : Ω → SAOState K, SGood S →
      SGood (fun ω => (L.map (ev ω)).foldl (saoStep K β) (S ω)) := by
  induction L with
  | nil => intro _ S hS; exact hS
  | cons x L ih =>
    intro hL S hS
    exact ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)) _
      (step_SGood K β S hS x.1 x.2 (hL x List.mem_cons_self))

theorem init_SGood (K n : ℕ) : SGood (fun _ : Ω => SAOState.init K n) :=
  ⟨DM.const _, fun _ => measurable_const, fun _ => measurable_const, fun _ => measurable_const,
    fun _ => measurable_const⟩

def EGood {K : ℕ} (s : Ω → (Fin K → ℝ) × (Fin K → ℝ)) : Prop :=
  (∀ i, Measurable fun ω => (s ω).1 i) ∧ ∀ i, Measurable fun ω => (s ω).2 i

theorem exp3_fold (K : ℕ) (prm : Exp3PParams) (L : List (Fin K × (Ω → ℝ))) :
    (∀ x ∈ L, Measurable x.2) → ∀ s : Ω → (Fin K → ℝ) × (Fin K → ℝ), EGood s →
      EGood (fun ω => (L.map (ev ω)).foldl (exp3PStep K prm) (s ω)) := by
  induction L with
  | nil => intro _ s hs; exact hs
  | cons x L ih =>
    intro hL s hs
    refine ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)) _ ?_
    obtain ⟨h1, h2⟩ := hs
    have hx := hL x List.mem_cons_self
    have hG : ∀ i, Measurable fun ω =>
        (s ω).2 i + ((if x.1 = i then x.2 ω else 0) + prm.betaP) / (s ω).1 i := by
      intro i
      by_cases h : x.1 = i
      · simp only [h, if_true]; exact (h2 i).add ((hx.add measurable_const).div (h1 i))
      · simp only [h, if_false]; exact (h2 i).add ((measurable_const.add measurable_const).div (h1 i))
    refine ⟨fun i => ?_, hG⟩
    show Measurable fun ω => (1 - prm.gamma) * Real.exp (prm.eta * ((s ω).2 i +
        ((if x.1 = i then x.2 ω else 0) + prm.betaP) / (s ω).1 i)) /
        ∑ k, Real.exp (prm.eta * ((s ω).2 k + ((if x.1 = k then x.2 ω else 0) + prm.betaP) / (s ω).1 k))
        + prm.gamma / K
    refine ((measurable_const.mul ((hG i).const_mul _).exp).div
      (Finset.measurable_sum _ (fun k _ => ((hG k).const_mul _).exp))).add measurable_const

theorem meas_sao (K n : ℕ) (β : ℝ) (L : List (Fin K × (Ω → ℝ))) (hL : ∀ x ∈ L, Measurable x.2)
    (i : Fin K) : Measurable fun ω => sao K n β (L.map (ev ω)) i := by
  have hS := fold_SGood K β L hL _ (init_SGood K n)
  have hz : DM (fun ω => (saoState K n β (L.map (ev ω))).tau0) :=
    hS.1.map (fun d => d.2.2.2.2)
  refine meas_piece hz (fun z ω => match z with
    | none => (saoState K n β (L.map (ev ω))).p i
    | some τ => exp3P K (exp3PTuned K (n - τ) (K / β)) ((L.drop τ).map (ev ω)) i) ?_ ?_
  · intro z
    cases z with
    | none => exact hS.2.1 i
    | some τ =>
      exact (exp3_fold K _ (L.drop τ) (fun x hx => hL x (List.mem_of_mem_drop hx)) _
        ⟨fun _ => measurable_const, fun _ => measurable_const⟩).1 i
  · intro ω
    simp only [sao]
    rcases h : (saoState K n β (L.map (ev ω))).tau0 with _ | τ
    · rfl
    · simp only [List.map_drop]

theorem history_table (K n : ℕ) (ω : Fin n → Fin K → ℝ) (I : Fin n → Fin K) :
    history (tableAdv ω) I =
      (List.ofFn (fun r => (I r, fun ω' : Fin n → Fin K → ℝ => ω' r (I r)))).map (ev ω) := by
  have key : ∀ r : Fin n, reward (tableAdv ω) I r (I r) = ω r (I r) := by
    intro r
    unfold reward tableAdv
    have hlen : ((List.ofFn I).take r).length = r := by simp [r.isLt.le]
    split_ifs with h
    · congr 2
    · rw [hlen] at h
      exact absurd r.isLt h
  unfold history
  rw [List.map_ofFn]
  congr 1
  funext r
  simp only [Function.comp, ev, key]

theorem meas_pathProb (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) :
    Measurable fun ω : Fin n → Fin K → ℝ => pathProb (sao K n β) (tableAdv ω) I := by
  unfold pathProb probAt
  refine Finset.measurable_prod _ (fun r _ => ?_)
  simp only [history_table, ← List.map_take]
  refine meas_sao K n β _ ?_ (I r)
  intro x hx
  have hx' := List.mem_of_mem_take hx
  rw [List.mem_ofFn] at hx'
  obtain ⟨r', rfl⟩ := hx'
  exact (measurable_pi_apply _).comp (measurable_pi_apply r')

end Outer

/-! ### `0 ≤ p ≤ 1` for every sampling vector of SAO. -/

def Inv2 {K : ℕ} (s : SAOState K) : Prop :=
  ∀ i, i ∉ s.active → s.p i = s.q i * s.tau i / ((s.t : ℝ) + 1)

theorem inv2_step (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : Inv2 s) :
    Inv2 (saoStep K β s o) := by
  cases hs : s.tau0 with
  | some τ => rw [P5292263e.step_frozen K β s o τ hs]; exact h
  | none =>
    obtain ⟨r, _, hA, hT, hQ, ht, _, hP⟩ := P5292263e.step_spec K β s o hs
    intro i hi
    rw [hA] at hi
    rw [hP, hQ, hT, ht]
    simp only [hi, if_false]

theorem inv2_fold (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), Inv2 s → Inv2 (l.foldl (saoStep K β) s) := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o l ih => intro s h; exact ih _ (inv2_step K β s o h)

theorem inv2_init (K n : ℕ) : Inv2 (SAOState.init K n) := by
  intro i hi
  simp [SAOState.init] at hi

theorem state_p_bounds {K : ℕ} (s : SAOState K) (h : P5292263e.Inv s) (h2 : Inv2 s) (i : Fin K) :
    0 ≤ s.p i ∧ s.p i ≤ 1 := by
  by_cases hi : i ∈ s.active
  · obtain ⟨h0, h1⟩ := P5292263e.inv_p_bounds s h i hi
    refine ⟨h0, h1.trans ?_⟩
    have hc : (1 : ℝ) ≤ s.active.card := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
    rw [div_le_one (by linarith)]
    exact hc
  · rw [h2 i hi]
    obtain ⟨hj, _, hW0, hW1, _⟩ := h
    have hq := (hj i hi).2
    have ht : (0 : ℝ) < (s.t : ℝ) + 1 := by positivity
    have hterm : s.q i * s.tau i ≤ P5292263e.W s := by
      unfold P5292263e.W
      exact Finset.single_le_sum (f := fun j => s.q j * (s.tau j : ℝ))
        (fun j hj' => mul_nonneg (hj j (Finset.mem_sdiff.mp hj').2).2 (Nat.cast_nonneg _))
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
    constructor
    · exact div_nonneg (mul_nonneg hq (Nat.cast_nonneg _)) ht.le
    · rw [div_le_one ht]; linarith

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

theorem sao_bounds (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (h : History K) (i : Fin K) :
    0 ≤ sao K n β h i ∧ sao K n β h i ≤ 1 := by
  unfold sao
  cases hz : (saoState K n β h).tau0 with
  | none =>
    exact state_p_bounds _ (P5292263e.inv_fold K β h _ (P5292263e.inv_init K n))
      (inv2_fold K β h _ (inv2_init K n)) i
  | some τ => exact exp3P_bounds K hK _ _ _ i

theorem pathProb_bounds (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) :
    0 ≤ pathProb (sao K n β) adv I ∧ pathProb (sao K n β) adv I ≤ 1 :=
  ⟨Finset.prod_nonneg (fun r _ => (sao_bounds K n hK β _ (I r)).1),
    Finset.prod_le_one (fun r _ => (sao_bounds K n hK β _ (I r)).1)
      (fun r _ => (sao_bounds K n hK β _ (I r)).2)⟩

/-! ### Monotonicity of `probStoch` under an almost-sure implication. -/

theorem ae_table (K n : ℕ) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) :
    ∀ᵐ ω ∂(rewardTableMeasure n ν), ∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]; intro r; rw [ae_all_iff]; intro i
  have h1 : ∀ᵐ y ∂(ν i), y ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν i
  have h2 : ∀ᵐ x ∂(Measure.pi ν), x i ∈ Set.Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_eval ν i).ae h1
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => Measure.pi ν) r).ae h2


end Pd1470854

namespace Pb0242b1c

open BestBothWorlds.SAO

/-! ### The active set of SAO is never empty, so every sampling vector sums to one. -/

theorem maxOver_mem' {K : ℕ} (A : Finset (Fin K)) (f : Fin K → ℝ) (hA : A.Nonempty) :
    ∃ j ∈ A, maxOver A f = f j := by
  unfold maxOver
  rw [dif_pos hA]
  obtain ⟨j, hj, e⟩ := Finset.exists_mem_eq_sup' hA f
  exact ⟨j, hj, e⟩

theorem armStep_ne (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ)
    (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool) (i : Fin K)
    (h : s.1.Nonempty) : (armStep K β t p Ht Hh T s i).1.Nonempty := by
  rcases s with ⟨A, tau, q, b⟩
  simp only at h
  dsimp only [armStep]
  split_ifs with hd
  · obtain ⟨j, hj, e⟩ := maxOver_mem' A Ht h
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, hj⟩⟩
    rintro rfl
    have hw : 0 ≤ width K β t := Real.sqrt_nonneg _
    have h2 := hd.2
    rw [e] at h2
    linarith
  · exact h

theorem fold_ne (K : ℕ) (β : ℝ) (t : ℕ) (p Ht Hh : Fin K → ℝ) (T : Fin K → ℕ) :
    ∀ (l : List (Fin K)) (s : Finset (Fin K) × (Fin K → ℕ) × (Fin K → ℝ) × Bool),
      s.1.Nonempty → (l.foldl (armStep K β t p Ht Hh T) s).1.Nonempty := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons i l ih => intro s h; exact ih _ (armStep_ne K β t p Ht Hh T s i h)

theorem step_ne (K : ℕ) (β : ℝ) (s : SAOState K) (o : Fin K × ℝ) (h : s.active.Nonempty) :
    (saoStep K β s o).active.Nonempty := by
  obtain ⟨t, A, tau, q, p, G1, G2, T, tau0⟩ := s
  cases tau0 with
  | some τ => exact h
  | none => exact fold_ne K β _ _ _ _ _ (List.finRange K) _ h

theorem fold_ne_sao (K : ℕ) (β : ℝ) :
    ∀ (l : History K) (s : SAOState K), s.active.Nonempty →
      (l.foldl (saoStep K β) s).active.Nonempty := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o l ih => intro s h; exact ih _ (step_ne K β s o h)

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

theorem sao_sum (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (h : History K) : ∑ j, sao K n β h j = 1 := by
  unfold sao
  cases hz : (saoState K n β h).tau0 with
  | some τ => exact exp3P_sum K hK _ _
  | none =>
    show ∑ j, (saoState K n β h).p j = 1
    have hI : P5292263e.Inv (saoState K n β h) :=
      P5292263e.inv_fold K β h _ (P5292263e.inv_init K n)
    have hI2 : Pd1470854.Inv2 (saoState K n β h) :=
      Pd1470854.inv2_fold K β h _ (Pd1470854.inv2_init K n)
    have hne : (saoState K n β h).active.Nonempty := by
      have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
      exact fold_ne_sao K β h _ Finset.univ_nonempty
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
      Finset.sum_congr rfl (fun j hj => hI2 j (Finset.mem_sdiff.mp hj).2)
    rw [e1, e2]
    ring

/-! ### Splitting off the last round. -/

theorem reward_table {K m : ℕ} (ω : Fin m → Fin K → ℝ) (I : Fin m → Fin K) (r : Fin m)
    (k : Fin K) : reward (tableAdv ω) I r k = ω r k := by
  unfold reward tableAdv
  have hlen : ((List.ofFn I).take r).length = r := by simp [r.isLt.le]
  split_ifs with h
  · have e : (⟨((List.ofFn I).take r).length, h⟩ : Fin m) = r := Fin.ext hlen
    rw [e]
  · rw [hlen] at h
    exact absurd r.isLt h

theorem hist_eq {K m : ℕ} (ω : Fin m → Fin K → ℝ) (I : Fin m → Fin K) :
    history (tableAdv ω) I = List.ofFn (fun r => (I r, ω r (I r))) := by
  unfold history
  simp only [reward_table]

theorem pathProb_snoc {K m : ℕ} (π : Policy K) (ω : Fin (m + 1) → Fin K → ℝ)
    (I : Fin m → Fin K) (j : Fin K) :
    pathProb π (tableAdv ω) (Fin.snoc I j : Fin (m + 1) → Fin K) =
      pathProb π (tableAdv (Fin.init ω)) I * π (history (tableAdv (Fin.init ω)) I) j := by
  have hL : history (tableAdv ω) (Fin.snoc I j : Fin (m + 1) → Fin K) =
      history (tableAdv (Fin.init ω)) I ++ [(j, ω (Fin.last m) j)] := by
    rw [hist_eq, hist_eq, List.ofFn_succ', List.concat_eq_append]
    simp [Fin.init]
  have hlen : (history (tableAdv (Fin.init ω)) I).length = m := by simp [history]
  unfold pathProb probAt
  rw [Fin.prod_univ_castSucc, hL]
  congr 1
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, Nat.add_sub_cancel]
    rw [List.take_append_of_le_length (by rw [hlen]; exact r.isLt.le)]
  · simp only [Fin.val_last, Fin.snoc_last, Nat.add_sub_cancel]
    rw [List.take_append_of_le_length (le_of_eq hlen.symm),
      List.take_of_length_le (le_of_eq hlen)]

theorem sum_snoc {K m : ℕ} (f : (Fin (m + 1) → Fin K) → ℝ) :
    ∑ I, f I = ∑ I : Fin m → Fin K, ∑ j : Fin K, f (Fin.snoc I j) := by
  rw [← (Fin.snocEquiv (fun _ => Fin K)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem prod_snoc {K m : ℕ} (c : ℕ → (Fin K → ℝ) → Fin K → ℝ) (ω : Fin (m + 1) → Fin K → ℝ)
    (I : Fin m → Fin K) (j : Fin K) :
    ∏ r : Fin (m + 1), c r (ω r) ((Fin.snoc I j : Fin (m + 1) → Fin K) r) =
      (∏ r : Fin m, c r (Fin.init ω r) (I r)) * c m (ω (Fin.last m)) j := by
  rw [Fin.prod_univ_castSucc]
  simp [Fin.init]

theorem sum_pathProb {K : ℕ} (π : Policy K) (hπ : ∀ h, ∑ j, π h j = 1) :
    ∀ (m : ℕ) (ω : Fin m → Fin K → ℝ), ∑ I : Fin m → Fin K, pathProb π (tableAdv ω) I = 1 := by
  intro m
  induction m with
  | zero => intro ω; simp [pathProb]
  | succ m ih =>
    intro ω
    rw [sum_snoc]
    simp only [pathProb_snoc, ← Finset.mul_sum, hπ, mul_one]
    exact ih _

end Pb0242b1c

namespace Pa12151c4

open BestBothWorlds.SAO

/-! ### Glue for the union bound (21), (23), (24). -/

theorem tau0_le (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) :
    tau0 K n β adv I ≤ n := by
  have hinv : P5292263e.Inv (runState K n β adv I n) :=
    P5292263e.inv_fold K β _ _ (P5292263e.inv_init K n)
  have h1 := P5292263e.t_fold K β ((history adv I).take n) (SAOState.init K n)
  have h2 : (SAOState.init K n).t = 0 := rfl
  have h3 : ((history adv I).take n).length ≤ n := by simp
  have h4 : (runState K n β adv I n).t =
      (List.foldl (saoStep K β) (SAOState.init K n) ((history adv I).take n)).t := rfl
  unfold tau0
  cases hz : (runState K n β adv I n).tau0 with
  | none => simp
  | some τ =>
    simp only
    have := hinv.2.1 τ hz
    omega

open Classical in
theorem union3 {K n : ℕ} (π : Policy K) (adv : Adversary K)
    (hp : ∀ I : Fin n → Fin K, 0 ≤ pathProb π adv I)
    {ι₁ ι₂ ι₃ : Type} (S₁ : Finset ι₁) (S₂ : Finset ι₂) (S₃ : Finset ι₃)
    (E : (Fin n → Fin K) → Prop) (F₁ : ι₁ → (Fin n → Fin K) → Prop)
    (F₂ : ι₂ → (Fin n → Fin K) → Prop) (F₃ : ι₃ → (Fin n → Fin K) → Prop)
    (hcov : ∀ I, (∀ j ∈ S₁, F₁ j I) → (∀ j ∈ S₂, F₂ j I) → (∀ j ∈ S₃, F₃ j I) → E I) :
    (∑ I : Fin n → Fin K, pathProb π adv I) - probEvent n π adv E ≤
      ∑ j ∈ S₁, ((∑ I : Fin n → Fin K, pathProb π adv I) - probEvent n π adv (F₁ j)) +
      ∑ j ∈ S₂, ((∑ I : Fin n → Fin K, pathProb π adv I) - probEvent n π adv (F₂ j)) +
      ∑ j ∈ S₃, ((∑ I : Fin n → Fin K, pathProb π adv I) - probEvent n π adv (F₃ j)) := by
  have key : ∀ (G : (Fin n → Fin K) → Prop), (∑ I : Fin n → Fin K, pathProb π adv I) - probEvent n π adv G =
      ∑ I : Fin n → Fin K, (pathProb π adv I - if G I then pathProb π adv I else 0) := by
    intro G
    unfold probEvent
    rw [Finset.sum_sub_distrib]
  simp only [key]
  rw [Finset.sum_comm (s := S₁), Finset.sum_comm (s := S₂), Finset.sum_comm (s := S₃),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun (I : Fin n → Fin K) _ => ?_)
  have h0 : ∀ G : (Fin n → Fin K) → Prop,
      0 ≤ pathProb π adv I - (if G I then pathProb π adv I else 0) := by
    intro G
    split_ifs <;> linarith [hp I]
  have hs1 := Finset.sum_nonneg (fun j (_ : j ∈ S₁) => h0 (F₁ j))
  have hs2 := Finset.sum_nonneg (fun j (_ : j ∈ S₂) => h0 (F₂ j))
  have hs3 := Finset.sum_nonneg (fun j (_ : j ∈ S₃) => h0 (F₃ j))
  by_cases hE : E I
  · rw [if_pos hE, sub_self]
    linarith
  · rw [if_neg hE, sub_zero]
    by_cases h1 : ∀ j ∈ S₁, F₁ j I
    · by_cases h2 : ∀ j ∈ S₂, F₂ j I
      · by_cases h3 : ∀ j ∈ S₃, F₃ j I
        · exact absurd (hcov I h1 h2 h3) hE
        · push_neg at h3
          obtain ⟨j, hj, hF⟩ := h3
          have := Finset.single_le_sum
            (f := fun j => pathProb π adv I - if F₃ j I then pathProb π adv I else 0)
            (fun j _ => h0 (F₃ j)) hj
          simp only [if_neg hF, sub_zero] at this
          linarith
      · push_neg at h2
        obtain ⟨j, hj, hF⟩ := h2
        have := Finset.single_le_sum
          (f := fun j => pathProb π adv I - if F₂ j I then pathProb π adv I else 0)
          (fun j _ => h0 (F₂ j)) hj
        simp only [if_neg hF, sub_zero] at this
        linarith
    · push_neg at h1
      obtain ⟨j, hj, hF⟩ := h1
      have := Finset.single_le_sum
        (f := fun j => pathProb π adv I - if F₁ j I then pathProb π adv I else 0)
        (fun j _ => h0 (F₁ j)) hj
      simp only [if_neg hF, sub_zero] at this
      linarith

/-! ### Monotonicity of the radii in the logarithmic term. -/

theorem estRadius_mono (K τ t : ℕ) (q L L' : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L) (hLL : L ≤ L') :
    estRadius K τ q t L ≤ estRadius K τ q t L' := by
  unfold estRadius
  apply Real.sqrt_le_sqrt
  have hc : 0 ≤ (K : ℝ) * ((min τ t : ℕ) : ℝ) / (t : ℝ) ^ 2 +
      max ((t : ℝ) - τ) 0 / (q * τ * t) := by
    have : 0 ≤ q * τ * t := by positivity
    have : 0 ≤ max ((t : ℝ) - τ) 0 := le_max_right _ _
    positivity
  have h1 := mul_le_mul_of_nonneg_left hLL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc)
  have h2 : (K : ℝ) * L / ((min τ t : ℕ) : ℝ) ≤ (K : ℝ) * L' / ((min τ t : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLL (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have h3 : 0 ≤ (K : ℝ) * L / ((min τ t : ℕ) : ℝ) := by positivity
  have h4 := pow_le_pow_left₀ h3 h2 2
  nlinarith

theorem pullBound_mono (q : ℝ) (τ t : ℕ) (L L' : ℝ) (hq : 0 ≤ q) (ht : 1 ≤ t) (hL : 0 ≤ L)
    (hLL : L ≤ L') : pullBound q τ t L ≤ pullBound q τ t L' := by
  unfold pullBound
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht)
  have hc : 0 ≤ 4 * q * τ * (1 + Real.log t) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hLL hc
  have h2 := pow_le_pow_left₀ hL hLL 2
  have h3 : Real.sqrt (4 * q * τ * (1 + Real.log t) * L + 5 * L ^ 2) ≤
      Real.sqrt (4 * q * τ * (1 + Real.log t) * L' + 5 * L' ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem log_cmp (a b δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.log (a / δ) ∧ Real.log (a / δ) ≤ Real.log (b / δ) := by
  have h1 : 1 ≤ a / δ := by rw [le_div_iff₀ hδ]; linarith
  refine ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) ?_⟩
  exact div_le_div_of_nonneg_right hab hδ.le

theorem qEff_nonneg (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K)
    (i : Fin K) : 0 ≤ qEff K n β adv I i := by
  unfold qEff probAt
  exact (Pd1470854.sao_bounds K n hK β _ i).1

/-! ### Measurability of the parent integrand. -/

section Meas

theorem hL_meas (K n : ℕ) (I : Fin n → Fin K) (m : ℕ) :
    ∀ x ∈ ((List.ofFn (fun r => (I r, fun ω' : Fin n → Fin K → ℝ => ω' r (I r)))).take m),
      Measurable x.2 := by
  intro x hx
  have hx' := List.mem_of_mem_take hx
  rw [List.mem_ofFn] at hx'
  obtain ⟨r', rfl⟩ := hx'
  exact (measurable_pi_apply _).comp (measurable_pi_apply r')

theorem dm_run (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) :
    Pd1470854.DM (fun ω : Fin n → Fin K → ℝ =>
      Pd1470854.disc (runState K n β (tableAdv ω) I n)) := by
  have hS := Pd1470854.fold_SGood K β _ (hL_meas K n I n) _
    (Pd1470854.init_SGood (Ω := Fin n → Fin K → ℝ) K n)
  have he : ∀ ω : Fin n → Fin K → ℝ, runState K n β (tableAdv ω) I n =
      (((List.ofFn (fun r => (I r, fun ω' : Fin n → Fin K → ℝ => ω' r (I r)))).take n).map
        (Pd1470854.ev ω)).foldl (saoStep K β) (SAOState.init K n) := by
    intro ω
    unfold runState saoState
    rw [Pd1470854.history_table, ← List.map_take]
  simp only [he]
  exact hS.1

theorem dm_tau0 (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) :
    Pd1470854.DM (fun ω : Fin n → Fin K → ℝ => tau0 K n β (tableAdv ω) I) := by
  have h := (dm_run K n β I).map (fun d => d.2.2.2.2.getD n)
  have e : (fun ω : Fin n → Fin K → ℝ => tau0 K n β (tableAdv ω) I) =
      fun ω => ((Pd1470854.disc (runState K n β (tableAdv ω) I n)).2.2.2.2).getD n := by
    funext ω
    unfold tau0 Pd1470854.disc
    cases (runState K n β (tableAdv ω) I n).tau0 <;> rfl
  rw [e]
  exact h

theorem dm_tauEff (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) (i : Fin K) :
    Pd1470854.DM (fun ω : Fin n → Fin K → ℝ => tauEff K n β (tableAdv ω) I i) :=
  (((dm_run K n β I).map (fun d => d.2.2.1 i)).pair (dm_tau0 K n β I)).map
    (fun p => min p.1 p.2)

theorem meas_probAt (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) (d : ℕ) (j : Fin K) :
    Measurable fun ω : Fin n → Fin K → ℝ => probAt (sao K n β) (tableAdv ω) I d j := by
  unfold probAt
  simp only [Pd1470854.history_table, ← List.map_take]
  exact Pd1470854.meas_sao K n β _ (hL_meas K n I _) j

theorem meas_qEff (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) (i : Fin K) :
    Measurable fun ω : Fin n → Fin K → ℝ => qEff K n β (tableAdv ω) I i :=
  Pd1470854.meas_piece (dm_tauEff K n β I i)
    (fun d ω => probAt (sao K n β) (tableAdv ω) I d i) (fun d => meas_probAt K n β I d i)
    (fun _ => rfl)

theorem meas_estAvg (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) (i : Fin K) (t : ℕ) :
    Measurable fun ω : Fin n → Fin K → ℝ => estAvg (sao K n β) (tableAdv ω) I i t := by
  unfold estAvg estReward
  simp only [Pb0242b1c.reward_table]
  exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply i).comp
    (measurable_pi_apply r)).div (meas_probAt K n β I _ i))).div_const _

theorem meas_algAvg (K n : ℕ) (I : Fin n → Fin K) (i : Fin K) (t : ℕ) :
    Measurable fun ω : Fin n → Fin K → ℝ => algAvg (tableAdv ω) I i t := by
  unfold algAvg algReward
  simp only [Pb0242b1c.reward_table]
  exact (Finset.measurable_sum _
    (fun r _ => (measurable_pi_apply i).comp (measurable_pi_apply r))).div_const _

theorem meas_estRadius_q (K d t : ℕ) (L : ℝ) : Measurable fun q : ℝ => estRadius K d q t L := by
  unfold estRadius
  fun_prop

theorem meas_pullBound_q (d t : ℕ) (L : ℝ) : Measurable fun q : ℝ => pullBound q d t L := by
  unfold pullBound
  fun_prop

/-- The good event of the parent, with `L` in place of `log β`. -/
def Ev (K n : ℕ) (β L : ℝ) (ν : Fin K → Measure ℝ) (ω : Fin n → Fin K → ℝ)
    (I : Fin n → Fin K) : Prop :=
  ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
    |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
        estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L ∧
    (1 ≤ pullCount I i t →
      |algAvg (tableAdv ω) I i t - mean ν i| ≤ Real.sqrt (2 * L / pullCount I i t)) ∧
    (pullCount I i t : ℝ) ≤
        pullBound (qEff K n β (tableAdv ω) I i) (tauEff K n β (tableAdv ω) I i) t L

theorem meas_Ev (K n : ℕ) (β L : ℝ) (ν : Fin K → Measure ℝ) (I : Fin n → Fin K) :
    MeasurableSet {ω | Ev K n β L ν ω I} := by
  refine measurableSet_setOf.mpr ?_
  unfold Ev
  refine Measurable.forall (fun i => Measurable.forall (fun t => Measurable.imp ?_ ?_))
  · exact measurableSet_setOf.mp ((dm_tau0 K n β I).pre {d | t ∈ Finset.Icc 1 d})
  · have hrad : Measurable fun ω : Fin n → Fin K → ℝ =>
        estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L :=
      Pd1470854.meas_piece (dm_tauEff K n β I i)
        (fun d ω => estRadius K d (qEff K n β (tableAdv ω) I i) t L)
        (fun d => (meas_estRadius_q K d t L).comp (meas_qEff K n β I i)) (fun _ => rfl)
    have hpb : Measurable fun ω : Fin n → Fin K → ℝ =>
        pullBound (qEff K n β (tableAdv ω) I i) (tauEff K n β (tableAdv ω) I i) t L :=
      Pd1470854.meas_piece (dm_tauEff K n β I i)
        (fun d ω => pullBound (qEff K n β (tableAdv ω) I i) d t L)
        (fun d => (meas_pullBound_q d t L).comp (meas_qEff K n β I i)) (fun _ => rfl)
    refine Measurable.and ?_ (Measurable.and (Measurable.imp measurable_const ?_) ?_)
    · exact measurableSet_setOf.mp (measurableSet_le
        (continuous_abs.measurable.comp ((meas_estAvg K n β I i t).sub_const _)) hrad)
    · exact measurableSet_setOf.mp (measurableSet_le
        (continuous_abs.measurable.comp ((meas_algAvg K n I i t).sub_const _)) measurable_const)
    · exact measurableSet_setOf.mp (measurableSet_le measurable_const hpb)

end Meas

theorem integrable_of_pos {α : Type} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (h : 0 < ∫ x, g x ∂μ) : Integrable g μ := by
  by_contra hg
  rw [integral_undef hg] at h
  exact lt_irrefl _ h

end Pa12151c4


/-! ## Lemma 4.5 (stochastic): Freedman-type supermartingale on the joint (table, path) law. -/

namespace P6cbf72b9

open BestBothWorlds.SAO P9236924e

/-! ### The two-point bound, centred at the mean. -/

theorem two_pointS (p y g μ : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hy : |y| ≤ p) :
    p * Real.exp (y * (g / p - μ) - y ^ 2 / p) + (1 - p) * Real.exp (y * (0 - μ) - y ^ 2 / p) ≤
      Real.exp (-(y ^ 2 / p)) * (1 + y * (g - μ) + y ^ 2 * (g / p - 2 * g * μ + μ ^ 2)) := by
  set a := y ^ 2 / p with ha
  set u := g / p with hu
  have hpu : p * u = g := by rw [hu, mul_div_cancel₀ g hp0.ne']
  have hu0 : 0 ≤ u := div_nonneg hg0 hp0.le
  have hu1 : u ≤ 1 / p := div_le_div_of_nonneg_right hg1 hp0.le
  have h1p : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have hx1 : |y * (u - μ)| ≤ 1 := by
    rw [abs_mul]
    have hb : |u - μ| ≤ 1 / p := by
      rw [abs_le]; constructor <;> linarith
    calc |y| * |u - μ| ≤ p * (1 / p) := mul_le_mul hy hb (abs_nonneg _) hp0.le
      _ = 1 := by field_simp
  have hx0 : |y * (0 - μ)| ≤ 1 := by
    rw [abs_mul, zero_sub, abs_neg, abs_of_nonneg hμ0]
    calc |y| * μ ≤ p * 1 := mul_le_mul hy hμ1 hμ0 hp0.le
      _ ≤ 1 := by linarith
  have e1 : Real.exp (y * (u - μ) - a) ≤ Real.exp (-a) * (1 + y * (u - μ) + (y * (u - μ)) ^ 2) := by
    rw [show y * (u - μ) - a = -a + y * (u - μ) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad _ hx1) (Real.exp_pos _).le
  have e0 : Real.exp (y * (0 - μ) - a) ≤
      Real.exp (-a) * (1 + y * (0 - μ) + (y * (0 - μ)) ^ 2) := by
    rw [show y * (0 - μ) - a = -a + y * (0 - μ) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad _ hx0) (Real.exp_pos _).le
  have hp1' : 0 ≤ 1 - p := by linarith
  have hE := Real.exp_pos (-a)
  have hcomb : p * (1 + y * (u - μ) + (y * (u - μ)) ^ 2) +
      (1 - p) * (1 + y * (0 - μ) + (y * (0 - μ)) ^ 2) ≤
      1 + y * (g - μ) + y ^ 2 * (u - 2 * g * μ + μ ^ 2) := by
    have e : p * (1 + y * (u - μ) + (y * (u - μ)) ^ 2) +
        (1 - p) * (1 + y * (0 - μ) + (y * (0 - μ)) ^ 2) =
        1 + y * (g - μ) + y ^ 2 * (g * u - 2 * g * μ + μ ^ 2) := by
      linear_combination (y + y ^ 2 * u - 2 * y ^ 2 * μ) * hpu
    rw [e]
    have hgu : g * u ≤ u := mul_le_of_le_one_left hu0 hg1
    have := mul_le_mul_of_nonneg_left hgu (sq_nonneg y)
    nlinarith
  calc p * Real.exp (y * (u - μ) - a) + (1 - p) * Real.exp (y * (0 - μ) - a)
      ≤ p * (Real.exp (-a) * (1 + y * (u - μ) + (y * (u - μ)) ^ 2)) +
        (1 - p) * (Real.exp (-a) * (1 + y * (0 - μ) + (y * (0 - μ)) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hp0.le) (mul_le_mul_of_nonneg_left e0 hp1')
    _ = Real.exp (-a) * (p * (1 + y * (u - μ) + (y * (u - μ)) ^ 2) +
          (1 - p) * (1 + y * (0 - μ) + (y * (0 - μ)) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcomb hE.le

theorem factor2S {K : ℕ} (p : Fin K → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (i : Fin K)
    (g μ ℓ t : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ht : 0 < t)
    (hpi : 0 < p i) (hℓ : |ℓ| ≤ p i * t) :
    ∑ j, p j * Real.exp (ℓ * ((if j = i then g / p i else 0) - μ) / t - ℓ ^ 2 / (p i * t ^ 2)) ≤
      Real.exp (-((ℓ / t) ^ 2 / p i)) *
        (1 + ℓ / t * (g - μ) + (ℓ / t) ^ 2 * (g / p i - 2 * g * μ + μ ^ 2)) := by
  have hpi1 : p i ≤ 1 := by
    rw [← hp1]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  set y := ℓ / t with hy
  have hyb : |y| ≤ p i := by
    rw [hy, abs_div, abs_of_pos ht, div_le_iff₀ ht]; exact hℓ
  have ea : ℓ ^ 2 / (p i * t ^ 2) = y ^ 2 / p i := by
    rw [hy, div_pow, div_div, mul_comm (t ^ 2) (p i)]
  have ex' : ∀ j, ℓ * ((if j = i then g / p i else 0) - μ) / t =
      y * ((if j = i then g / p i else 0) - μ) := by
    intro j; rw [hy]; ring
  simp only [ex', ea]
  rw [Fintype.sum_eq_add_sum_compl i]
  have hrest : ∑ j ∈ ({i}ᶜ : Finset (Fin K)),
      p j * Real.exp (y * ((if j = i then g / p i else 0) - μ) - y ^ 2 / p i) =
      (1 - p i) * Real.exp (y * (0 - μ) - y ^ 2 / p i) := by
    have hs : ∑ j ∈ ({i}ᶜ : Finset (Fin K)), p j = 1 - p i := by
      rw [← hp1, Fintype.sum_eq_add_sum_compl i p]; ring
    rw [← hs, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := by simpa using hj
    simp only [hji, if_false]
  rw [hrest, if_pos rfl]
  exact two_pointS (p i) y g μ hpi hpi1 hg0 hg1 hμ0 hμ1 hyb

/-! ### The truncated per-round exponent. -/

noncomputable def exS (K n : ℕ) (β : ℝ) (μ : ℝ) (i : Fin K) (ℓ : ℝ) (t r : ℕ) (h : History K)
    (x : Fin K → ℝ) (j : Fin K) : ℝ :=
  if r < t ∧ 0 < sao K n β h i ∧ |ℓ| ≤ sao K n β h i * t then
    ℓ * ((if j = i then x i / sao K n β h i else 0) - μ) / t -
      ℓ ^ 2 / (sao K n β h i * (t : ℝ) ^ 2)
  else 0

theorem exS_meas (K n : ℕ) (β : ℝ) (μ : ℝ) (i : Fin K) (ℓ : ℝ) (t r : ℕ) (h : History K)
    (j : Fin K) : Measurable (fun x => exS K n β μ i ℓ t r h x j) := by
  unfold exS
  by_cases hc : r < t ∧ 0 < sao K n β h i ∧ |ℓ| ≤ sao K n β h i * t
  · simp only [if_pos hc]
    by_cases hj : j = i
    · simp only [hj, if_true]; fun_prop
    · simp only [hj, if_false]; fun_prop
  · simp only [if_neg hc]; exact measurable_const

theorem mean_bounds {K : ℕ} (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) : 0 ≤ mean ν i ∧ mean ν i ≤ 1 := by
  have hb : ∀ᵐ y ∂(ν i), y ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν i
  have hid : Integrable (fun y : ℝ => y) (ν i) := Integrable.of_mem_Icc 0 1 aemeasurable_id hb
  refine ⟨integral_nonneg_of_ae (hb.mono (fun y hy => hy.1)), ?_⟩
  have := integral_mono_ae hid (integrable_const (1 : ℝ)) (hb.mono (fun y hy => hy.2))
  simpa [mean] using this

theorem factorS (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (ν : Fin K → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) (ℓ : ℝ)
    (t r : ℕ) (h : History K) :
    ∫⁻ x, ENNReal.ofReal (∑ j, sao K n β h j * Real.exp (exS K n β (mean ν i) i ℓ t r h x j))
      ∂(Measure.pi ν) ≤ 1 := by
  have hPi : IsProbabilityMeasure (Measure.pi ν) := inferInstance
  unfold exS
  by_cases hc : r < t ∧ 0 < sao K n β h i ∧ |ℓ| ≤ sao K n β h i * t
  · simp only [if_pos hc]
    obtain ⟨hrt, hpi, hℓ⟩ := hc
    have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    obtain ⟨hμ0, hμ1⟩ := mean_bounds ν hν i
    set μ := mean ν i with hμ
    set p := sao K n β h with hp
    set y := ℓ / t with hy
    set a := y ^ 2 / p i with ha
    have hpi1 : p i ≤ 1 := (Pd1470854.sao_bounds K n hK β h i).2
    set B : ℝ → ℝ := fun g => Real.exp (-a) * (1 + y * (g - μ) + y ^ 2 * (g / p i - 2 * g * μ + μ ^ 2))
      with hB
    have hb : ∀ᵐ g ∂(ν i), g ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν i
    have hbx : ∀ᵐ x ∂(Measure.pi ν), x i ∈ Set.Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_eval ν i).ae hb
    have hpt : ∀ g : ℝ, g ∈ Set.Icc (0 : ℝ) 1 →
        0 ≤ ∑ j, p j * Real.exp (ℓ * ((if j = i then g / p i else 0) - μ) / t - ℓ ^ 2 / (p i * t ^ 2)) ∧
        ∑ j, p j * Real.exp (ℓ * ((if j = i then g / p i else 0) - μ) / t - ℓ ^ 2 / (p i * t ^ 2)) ≤
          B g := by
      intro g hg
      refine ⟨Finset.sum_nonneg (fun j _ => mul_nonneg (Pd1470854.sao_bounds K n hK β h j).1
        (Real.exp_pos _).le), ?_⟩
      exact factor2S p (fun j => (Pd1470854.sao_bounds K n hK β h j).1)
        (Pb0242b1c.sao_sum K n hK β h) i g μ ℓ t hg.1 hg.2 hμ0 hμ1 ht hpi hℓ
    have hBm : Measurable (fun g : ℝ => ENNReal.ofReal (B g)) := by
      simp only [hB]; fun_prop
    have hid : Integrable (fun g : ℝ => g) (ν i) := Integrable.of_mem_Icc 0 1 aemeasurable_id hb
    set c0 := Real.exp (-a) * (1 - y * μ + y ^ 2 * μ ^ 2) with hc0
    set c1 := Real.exp (-a) * (y + y ^ 2 / p i - 2 * y ^ 2 * μ) with hc1
    have hBe : ∀ g, B g = c0 + c1 * g := by
      intro g; simp only [hB, hc0, hc1]; ring
    have hBi : Integrable B (ν i) := by
      have : B = fun g => c0 + c1 * g := funext hBe
      rw [this]
      exact (integrable_const c0).add (hid.const_mul c1)
    have hBint : ∫ g, B g ∂(ν i) = c0 + c1 * μ := by
      have : B = fun g => c0 + c1 * g := funext hBe
      rw [this, integral_add (integrable_const c0) (hid.const_mul c1), integral_const,
        integral_const_mul]
      simp [mean, μ]
    have hval : c0 + c1 * μ ≤ 1 := by
      have e : c0 + c1 * μ = Real.exp (-a) * (1 + y ^ 2 * (μ / p i - μ ^ 2)) := by
        simp only [hc0, hc1]; ring
      rw [e]
      have h2 : y ^ 2 * (μ / p i - μ ^ 2) ≤ a := by
        rw [ha]
        have h3 : μ / p i ≤ 1 / p i := div_le_div_of_nonneg_right hμ1 hpi.le
        have h4 : y ^ 2 * (μ / p i - μ ^ 2) ≤ y ^ 2 * (1 / p i) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg μ]) (sq_nonneg y)
        calc y ^ 2 * (μ / p i - μ ^ 2) ≤ y ^ 2 * (1 / p i) := h4
          _ = y ^ 2 / p i := by ring
      have hea : Real.exp (-a) * (1 + a) ≤ 1 := by
        have h1 := Real.add_one_le_exp a
        have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
        calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
              mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
          _ = 1 := h2
      calc Real.exp (-a) * (1 + y ^ 2 * (μ / p i - μ ^ 2)) ≤ Real.exp (-a) * (1 + a) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ ≤ 1 := hea
    calc ∫⁻ x, ENNReal.ofReal (∑ j, p j * Real.exp (ℓ * ((if j = i then x i / p i else 0) - μ) / t -
            ℓ ^ 2 / (p i * t ^ 2))) ∂(Measure.pi ν)
        ≤ ∫⁻ x, ENNReal.ofReal (B (x i)) ∂(Measure.pi ν) := by
          refine lintegral_mono_ae (hbx.mono (fun x hx => ?_))
          exact ENNReal.ofReal_le_ofReal (hpt (x i) hx).2
      _ = ∫⁻ g, ENNReal.ofReal (B g) ∂(ν i) := (measurePreserving_eval ν i).lintegral_comp hBm
      _ = ENNReal.ofReal (∫ g, B g ∂(ν i)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hBi
            (hb.mono (fun g hg => le_trans (hpt g hg).1 (hpt g hg).2))]
      _ ≤ 1 := by
          rw [hBint, ENNReal.ofReal_le_one]; exact hval
  · simp only [if_neg hc, Real.exp_zero, mul_one]
    rw [Pb0242b1c.sao_sum K n hK β h]
    simp

/-! ### The supermartingale bound with history-dependent factors. -/

theorem prod_snoc2 {K m : ℕ} (c : ℕ → History K → (Fin K → ℝ) → Fin K → ℝ)
    (ω : Fin (m + 1) → Fin K → ℝ) (I : Fin m → Fin K) (j : Fin K) :
    ∏ r : Fin (m + 1), c r ((history (tableAdv ω) (Fin.snoc I j : Fin (m + 1) → Fin K)).take r)
        (ω r) ((Fin.snoc I j : Fin (m + 1) → Fin K) r) =
      (∏ r : Fin m, c r ((history (tableAdv (Fin.init ω)) I).take r) (Fin.init ω r) (I r)) *
        c m (history (tableAdv (Fin.init ω)) I) (ω (Fin.last m)) j := by
  have hL : history (tableAdv ω) (Fin.snoc I j : Fin (m + 1) → Fin K) =
      history (tableAdv (Fin.init ω)) I ++ [(j, ω (Fin.last m) j)] := by
    rw [Pb0242b1c.hist_eq, Pb0242b1c.hist_eq, List.ofFn_succ', List.concat_eq_append]
    simp [Fin.init]
  have hlen : (history (tableAdv (Fin.init ω)) I).length = m := by simp [history]
  rw [Fin.prod_univ_castSucc, hL]
  congr 1
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    rw [List.take_append_of_le_length (by rw [hlen]; exact r.isLt.le)]
    rfl
  · simp only [Fin.val_last, Fin.snoc_last]
    rw [List.take_append_of_le_length (le_of_eq hlen.symm),
      List.take_of_length_le (le_of_eq hlen)]

theorem key_bound2 {K : ℕ} (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (π : Policy K) (hπ0 : ∀ h j, 0 ≤ π h j)
    (c : ℕ → History K → (Fin K → ℝ) → Fin K → ℝ) (hc0 : ∀ r h x j, 0 ≤ c r h x j)
    (hcm : ∀ r h j, Measurable (fun x => c r h x j))
    (hc1 : ∀ r h, ∫⁻ x, ENNReal.ofReal (∑ j, π h j * c r h x j) ∂(Measure.pi ν) ≤ 1) :
    ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal (∑ I, pathProb π (tableAdv ω) I *
      ∏ r : Fin m, c r ((history (tableAdv ω) I).take r) (ω r) (I r))
        ∂(rewardTableMeasure m ν) ≤ 1 := by
  have hP0 : ∀ {m : ℕ} (ω : Fin m → Fin K → ℝ) (I : Fin m → Fin K),
      0 ≤ pathProb π (tableAdv ω) I :=
    fun ω I => Finset.prod_nonneg (fun r _ => hπ0 _ _)
  have hC0 : ∀ {m : ℕ} (ω : Fin m → Fin K → ℝ) (I : Fin m → Fin K),
      0 ≤ ∏ r : Fin m, c r ((history (tableAdv ω) I).take r) (ω r) (I r) :=
    fun ω I => Finset.prod_nonneg (fun r _ => hc0 _ _ _ _)
  intro m
  induction m with
  | zero =>
    have : IsProbabilityMeasure (rewardTableMeasure 0 ν) := by
      unfold rewardTableMeasure; infer_instance
    calc _ ≤ ∫⁻ _ω, (1 : ENNReal) ∂(rewardTableMeasure 0 ν) := by
          refine lintegral_mono (fun ω => ?_)
          simp [pathProb]
      _ = 1 := by simp
  | succ m ih =>
    let B : (Fin m → Fin K → ℝ) → (Fin m → Fin K) → ℝ := fun ω' I =>
      pathProb π (tableAdv ω') I * ∏ r : Fin m, c r ((history (tableAdv ω') I).take r) (ω' r) (I r)
    have hB0 : ∀ ω' I, 0 ≤ B ω' I := fun ω' I => mul_nonneg (hP0 _ _) (hC0 _ _)
    let F : (Fin m → Fin K → ℝ) → (Fin m → Fin K) → (Fin K → ℝ) → ℝ := fun ω' I x =>
      ∑ j, π (history (tableAdv ω') I) j * c m (history (tableAdv ω') I) x j
    have hF0 : ∀ ω' I x, 0 ≤ F ω' I x := fun ω' I x =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (hπ0 _ _) (hc0 _ _ _ _))
    let G : (Fin K → ℝ) → (Fin m → Fin K → ℝ) → ENNReal := fun x ω' =>
      ∑ I, ENNReal.ofReal (B ω' I) * ENNReal.ofReal (F ω' I x)
    have hF : ∀ ω : Fin (m + 1) → Fin K → ℝ, ENNReal.ofReal (∑ I, pathProb π (tableAdv ω) I *
        ∏ r : Fin (m + 1), c r ((history (tableAdv ω) I).take r) (ω r) (I r)) =
        G (ω (Fin.last m)) (Fin.init ω) := by
      intro ω
      have e : ∑ I, pathProb π (tableAdv ω) I *
          ∏ r : Fin (m + 1), c r ((history (tableAdv ω) I).take r) (ω r) (I r) =
          ∑ I, B (Fin.init ω) I * F (Fin.init ω) I (ω (Fin.last m)) := by
        rw [Pb0242b1c.sum_snoc]
        refine Finset.sum_congr rfl (fun I _ => ?_)
        simp only [Pb0242b1c.pathProb_snoc, prod_snoc2, B, F, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [e, ENNReal.ofReal_sum_of_nonneg (fun I _ => mul_nonneg (hB0 _ _) (hF0 _ _ _))]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [ENNReal.ofReal_mul (hB0 _ _)]
    have hinner : ∀ ω' : Fin m → Fin K → ℝ, ∫⁻ x, G x ω' ∂(Measure.pi ν) ≤
        ENNReal.ofReal (∑ I, B ω' I) := by
      intro ω'
      have hm : ∀ I, Measurable (fun x : Fin K → ℝ => ENNReal.ofReal (F ω' I x)) := by
        intro I
        exact ENNReal.measurable_ofReal.comp
          (Finset.measurable_sum _ (fun j _ => (hcm m _ j).const_mul _))
      calc ∫⁻ x, G x ω' ∂(Measure.pi ν)
          = ∑ I, ENNReal.ofReal (B ω' I) * ∫⁻ x, ENNReal.ofReal (F ω' I x) ∂(Measure.pi ν) := by
            simp only [G]
            rw [lintegral_finsetSum _ (fun I _ => (hm I).const_mul _)]
            refine Finset.sum_congr rfl (fun I _ => ?_)
            rw [lintegral_const_mul _ (hm I)]
        _ ≤ ∑ I, ENNReal.ofReal (B ω' I) * 1 := by
            gcongr with I _
            exact hc1 m _
        _ = ENNReal.ofReal (∑ I, B ω' I) := by
            simp only [mul_one]
            rw [ENNReal.ofReal_sum_of_nonneg (fun I _ => hB0 _ _)]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => Measure.pi ν) (Fin.last m)
    have he : ∀ ω : Fin (m + 1) → Fin K → ℝ,
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin K → ℝ) (Fin.last m) ω =
          (ω (Fin.last m), Fin.init ω) := by
      intro ω
      refine Prod.ext rfl ?_
      funext r
      simp [MeasurableEquiv.piFinSuccAbove, Fin.init]
    calc ∫⁻ ω, ENNReal.ofReal (∑ I, pathProb π (tableAdv ω) I *
          ∏ r : Fin (m + 1), c r ((history (tableAdv ω) I).take r) (ω r) (I r))
            ∂(rewardTableMeasure (m + 1) ν)
        = ∫⁻ ω, (fun p : (Fin K → ℝ) × (Fin m → Fin K → ℝ) => G p.1 p.2)
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin K → ℝ) (Fin.last m) ω)
            ∂(Measure.pi fun _ : Fin (m + 1) => Measure.pi ν) := by
          unfold rewardTableMeasure
          refine lintegral_congr (fun ω => ?_)
          rw [hF, he]
      _ = ∫⁻ p, G p.1 p.2 ∂((Measure.pi ν).prod (Measure.pi fun _ : Fin m => Measure.pi ν)) :=
          hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
            (fun p : (Fin K → ℝ) × (Fin m → Fin K → ℝ) => G p.1 p.2)
      _ = ∫⁻ q, G q.2 q.1 ∂((Measure.pi fun _ : Fin m => Measure.pi ν).prod (Measure.pi ν)) :=
          (lintegral_prod_swap (fun p : (Fin K → ℝ) × (Fin m → Fin K → ℝ) => G p.1 p.2)).symm
      _ ≤ ∫⁻ ω', ∫⁻ x, G x ω' ∂(Measure.pi ν) ∂(Measure.pi fun _ : Fin m => Measure.pi ν) :=
          lintegral_prod_le _
      _ ≤ ∫⁻ ω', ENNReal.ofReal (∑ I, B ω' I) ∂(Measure.pi fun _ : Fin m => Measure.pi ν) :=
          lintegral_mono (fun ω' => hinner ω')
      _ ≤ 1 := ih

/-! ### The exponent along a run, and its value on the good event. -/

noncomputable def YsumS (K n : ℕ) (β : ℝ) (ω : Fin n → Fin K → ℝ) (μ : ℝ) (i : Fin K) (ℓ : ℝ)
    (t : ℕ) (I : Fin n → Fin K) : ℝ :=
  ∑ r : Fin n, exS K n β μ i ℓ t r ((history (tableAdv ω) I).take r) (ω r) (I r)

theorem meas_saoT (K n : ℕ) (β : ℝ) (I : Fin n → Fin K) (r : ℕ) (j : Fin K) :
    Measurable fun ω : Fin n → Fin K → ℝ => sao K n β ((history (tableAdv ω) I).take r) j := by
  simp only [Pd1470854.history_table, ← List.map_take]
  exact Pd1470854.meas_sao K n β _ (Pa12151c4.hL_meas K n I _) j

theorem meas_YsumS (K n : ℕ) (β : ℝ) (μ : ℝ) (i : Fin K) (ℓ : ℝ) (t : ℕ) (I : Fin n → Fin K) :
    Measurable fun ω : Fin n → Fin K → ℝ => YsumS K n β ω μ i ℓ t I := by
  unfold YsumS
  refine Finset.measurable_sum _ (fun r _ => ?_)
  have hP := meas_saoT K n β I r i
  have hS : MeasurableSet {ω : Fin n → Fin K → ℝ | (r : ℕ) < t ∧
      0 < sao K n β ((history (tableAdv ω) I).take r) i ∧
      |ℓ| ≤ sao K n β ((history (tableAdv ω) I).take r) i * t} :=
    (MeasurableSet.const _).inter ((measurableSet_lt measurable_const hP).inter
      (measurableSet_le measurable_const (hP.mul_const _)))
  unfold exS
  refine Measurable.ite hS ?_ measurable_const
  by_cases hj : I r = i
  · simp only [hj, if_true]
    have h1 : Measurable fun ω : Fin n → Fin K → ℝ => ω r i :=
      (measurable_pi_apply i).comp (measurable_pi_apply r)
    exact ((((h1.div hP).sub_const _).const_mul ℓ).div_const _).sub
      ((hP.mul_const _).const_div _)
  · simp only [hj, if_false]
    exact measurable_const.sub ((hP.mul_const _).const_div _)

theorem Y_eqS (K n : ℕ) (β : ℝ) (ω : Fin n → Fin K → ℝ) (μ : ℝ) (i : Fin K) (ℓ : ℝ) (t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (I : Fin n → Fin K)
    (hgood : ∀ r, r < t → 0 < sao K n β ((history (tableAdv ω) I).take r) i ∧
      |ℓ| ≤ sao K n β ((history (tableAdv ω) I).take r) i * t) :
    YsumS K n β ω μ i ℓ t I = ℓ * (estAvg (sao K n β) (tableAdv ω) I i t - μ) -
      ℓ ^ 2 * ∑ r ∈ Finset.range t,
        1 / (sao K n β ((history (tableAdv ω) I).take r) i * (t : ℝ) ^ 2) := by
  have e : ∀ r : Fin n, exS K n β μ i ℓ t r ((history (tableAdv ω) I).take r) (ω r) (I r) =
      ℓ / t * ((if (r : ℕ) < t ∧ I r = i then
          reward (tableAdv ω) I r i / probAt (sao K n β) (tableAdv ω) I (r + 1) i else 0) -
        (if (r : ℕ) < t then μ else 0)) -
      ℓ ^ 2 * (if (r : ℕ) < t then
          1 / (sao K n β ((history (tableAdv ω) I).take r) i * (t : ℝ) ^ 2) else 0) := by
    intro r
    have hp : probAt (sao K n β) (tableAdv ω) I (r + 1) i =
        sao K n β ((history (tableAdv ω) I).take r) i := by
      unfold probAt; rw [Nat.add_sub_cancel]
    have hg : ω r i = reward (tableAdv ω) I r i := (Pb0242b1c.reward_table ω I r i).symm
    unfold exS
    by_cases hr : (r : ℕ) < t
    · rw [if_pos ⟨hr, hgood r hr⟩, hg, hp]
      by_cases hi : I r = i
      · simp only [hi, hr, and_self, if_true]; ring
      · simp only [hi, hr, and_false, if_false, if_true]; ring
    · simp only [hr, false_and, if_false]; ring
  have hV := P925e7ff2.fin_sum_range htn
    (fun r => 1 / (sao K n β ((history (tableAdv ω) I).take r) i * (t : ℝ) ^ 2))
  have hM := P925e7ff2.fin_sum_range htn (fun _ => μ)
  have ht0 : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  unfold YsumS estAvg estReward
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter, hM, hV]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp


set_option maxHeartbeats 4000000 in
theorem coverS (K n : ℕ) (hK : 2 ≤ K) (β : ℝ) (ω : Fin n → Fin K → ℝ) (μ : ℝ) (i : Fin K) (t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (L : ℝ) (hL2 : 1 / 2 ≤ L) (I : Fin n → Fin K)
    (htt : t ≤ tau0 K n β (tableAdv ω) I)
    (hR : estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L <
      |estAvg (sao K n β) (tableAdv ω) I i t - μ|) :
    ∃ m : Bool × Fin t × Fin t, L ≤ YsumS K n β ω μ i
      ((if m.1 then 1 else -1) * mu (m.2.2 : ℕ) * ((((m.2.1 : ℕ) : ℝ) + 1) / K)) t I := by
  have hK1 : 1 ≤ K := by omega
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hL : 0 < L := by linarith
  obtain ⟨hτ1, hqK, hP1, hP2⟩ := pstruct K n hK β (tableAdv ω) I i t ht htn htt
  have hW := wsum_le K hK1 t (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i)
    (fun r => sao K n β ((history (tableAdv ω) I).take r) i) ht hτ1 hqK hP1 hP2
  have hVhb := vh_le K hK1 (tauEff K n β (tableAdv ω) I i) t (qEff K n β (tableAdv ω) I i) hτ1 ht hqK
  set τ := tauEff K n β (tableAdv ω) I i with hτ
  set q := qEff K n β (tableAdv ω) I i with hq
  set D := estAvg (sao K n β) (tableAdv ω) I i t - μ with hD
  set τ' := min τ t with hτ'
  have hτ'1 : 1 ≤ τ' := by omega
  have hτ't : τ' ≤ t := min_le_right _ _
  have hτ'τ : τ' ≤ τ := min_le_left _ _
  set Vh := (K : ℝ) * (τ' : ℝ) / (t : ℝ) ^ 2 + max ((t : ℝ) - τ) 0 / (q * τ * t) with hVh
  set W := ∑ r ∈ Finset.range t, 1 / (sao K n β ((history (tableAdv ω) I).take r) i * (t : ℝ) ^ 2) with hWdef
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hqK
  have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hτ'r : (1 : ℝ) ≤ τ' := by exact_mod_cast hτ'1
  have hVh0 : 0 ≤ Vh := by
    apply add_nonneg
    · positivity
    · exact div_nonneg (le_max_right _ _) (by positivity)
  set c : ℝ := (τ' : ℝ) / K with hc
  have hc0 : 0 < c := by positivity
  have hRe : estRadius K τ q t L = Real.sqrt (4 * Vh * L + 5 * (L / c) ^ 2) := by
    have e : (K : ℝ) * L / (τ' : ℝ) = L / c := by
      rw [hc]; field_simp
    show Real.sqrt (4 * Vh * L + 5 * ((K : ℝ) * L / (τ' : ℝ)) ^ 2) = _
    rw [e]
  -- the grid index
  have hL5 : (0 : ℝ) < L * (5 / 4) := by positivity
  set z := Vh * c ^ 2 / (L * (5 / 4)) with hz
  have hz0 : 0 ≤ z := div_nonneg (mul_nonneg hVh0 (sq_nonneg _)) hL5.le
  have ez : z * (L * (5 / 4)) = Vh * c ^ 2 := div_mul_cancel₀ _ hL5.ne'
  set k := ⌊z⌋₊ with hk
  have hk1 : (k : ℝ) * (5 / 4) * L ≤ Vh * c ^ 2 := by
    calc (k : ℝ) * (5 / 4) * L = (k : ℝ) * (L * (5 / 4)) := by ring
      _ ≤ z * (L * (5 / 4)) := mul_le_mul_of_nonneg_right (Nat.floor_le hz0) hL5.le
      _ = Vh * c ^ 2 := ez
  have hk2 : Vh * c ^ 2 ≤ ((k : ℝ) * (5 / 4) + 5 / 4) * L := by
    calc Vh * c ^ 2 = z * (L * (5 / 4)) := ez.symm
      _ ≤ ((k : ℝ) + 1) * (L * (5 / 4)) :=
        mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one z).le hL5.le
      _ = ((k : ℝ) * (5 / 4) + 5 / 4) * L := by ring
  have hkt : k < t := by
    rw [hk, Nat.floor_lt hz0, hz, div_lt_iff₀ hL5]
    have e : Vh * c ^ 2 = Vh * (τ' : ℝ) ^ 2 / (K : ℝ) ^ 2 := by rw [hc]; ring
    have h1 : Vh * c ^ 2 ≤ t / K := by
      rw [e, div_le_div_iff₀ (by positivity) hK0]
      calc Vh * (τ' : ℝ) ^ 2 * K ≤ (K * t) * K := mul_le_mul_of_nonneg_right hVhb hK0.le
        _ = t * (K : ℝ) ^ 2 := by ring
    have hLK : 1 ≤ L * K := by
      have := mul_le_mul hL2 hKr (by norm_num) hL.le
      linarith
    have h2 : (t : ℝ) / K < t * (L * (5 / 4)) := by
      rw [div_lt_iff₀ hK0]
      have e2 : (t : ℝ) * (L * (5 / 4)) * K = (5 / 4) * (t * (L * K)) := by ring
      rw [e2]
      linarith [mul_le_mul_of_nonneg_left hLK htpos.le]
    linarith
  obtain ⟨s, hs⟩ := key_ineq D W Vh L c k hc0 hL hW hk1 hk2 (by rw [← hRe]; exact hR)
  refine ⟨(s, ⟨τ' - 1, by omega⟩, ⟨k, hkt⟩), ?_⟩
  show L ≤ YsumS K n β ω μ i
    ((if s then 1 else -1) * mu k * ((((τ' - 1 : ℕ) : ℝ) + 1) / K)) t I
  have ecast : (((τ' - 1 : ℕ) : ℝ) + 1) / K = c := by
    rw [hc, Nat.cast_sub hτ'1]; push_cast; ring
  rw [ecast]
  have hm := mu_bounds k
  have hl : |(if s then (1 : ℝ) else -1) * mu k * c| ≤ c := by
    have hs1 : |(if s then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
    rw [abs_mul, abs_mul, hs1, abs_of_nonneg hm.1, abs_of_pos hc0]
    have := mul_le_mul_of_nonneg_right hm.2 hc0.le
    linarith
  rw [Y_eqS K n β ω μ i _ t ht htn I ?_]
  · exact hs
  · intro r hr
    have hcK : c ≤ (t : ℝ) / K := by
      rw [hc]
      have : (τ' : ℝ) ≤ t := by exact_mod_cast hτ't
      exact div_le_div_of_nonneg_right this hK0.le
    by_cases hrτ : r + 1 ≤ τ
    · have h1 := hP1 r hr hrτ
      have hp0 : 0 < sao K n β ((history (tableAdv ω) I).take r) i := lt_of_lt_of_le (by positivity) h1
      refine ⟨hp0, hl.trans (hcK.trans ?_)⟩
      calc (t : ℝ) / K = 1 / K * t := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 htpos.le
    · push_neg at hrτ
      have h2 := hP2 r hr (by omega)
      have hr1 : ((r : ℕ) : ℝ) + 1 ≤ t := by exact_mod_cast (show r + 1 ≤ t by omega)
      rw [h2]
      have hpos : 0 < q * τ / ((r : ℝ) + 1) := div_pos (mul_pos hq0 (by linarith)) (by positivity)
      refine ⟨hpos, hl.trans ?_⟩
      have hqt : q * τ ≤ q * τ / ((r : ℝ) + 1) * t := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hr1 (by positivity)
      have hcq : c ≤ q * τ := by
        rw [hc, div_le_iff₀ hK0]
        have hqK' : 1 ≤ q * K := by rw [div_le_iff₀ hK0] at hqK; linarith
        have : (τ' : ℝ) ≤ τ := by exact_mod_cast hτ'τ
        calc (τ' : ℝ) ≤ τ := this
          _ = τ * 1 := by ring
          _ ≤ τ * (q * K) := mul_le_mul_of_nonneg_left hqK' (by linarith)
          _ = q * τ * K := by ring
      linarith


theorem card_idx (t : ℕ) : (Fintype.card (Bool × Fin t × Fin t) : ℝ) = 2 * (t : ℝ) ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  push_cast; ring

set_option maxHeartbeats 4000000 in
theorem main (K n : ℕ) (hK : 2 ≤ K) (β : ℝ) (ν : Fin K → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) (t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probStoch n (sao K n β) ν (fun ω I =>
      t ≤ tau0 K n β (tableAdv ω) I →
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t
            (Real.log (2 * (t : ℝ) ^ 2 / δ))) := by
  have hK1 : 1 ≤ K := by omega
  have hPr : IsProbabilityMeasure (rewardTableMeasure n ν) := by
    unfold rewardTableMeasure; infer_instance
  set L := Real.log (2 * (t : ℝ) ^ 2 / δ) with hLdef
  set E : (Fin n → Fin K → ℝ) → (Fin n → Fin K) → Prop := fun ω I =>
      t ≤ tau0 K n β (tableAdv ω) I →
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L with hE
  have hP01 := fun (ω : Fin n → Fin K → ℝ) I =>
    Pd1470854.pathProb_bounds K n hK1 β (tableAdv ω) I
  have hsum : ∀ ω : Fin n → Fin K → ℝ, ∑ I, pathProb (sao K n β) (tableAdv ω) I = 1 :=
    Pb0242b1c.sum_pathProb _ (Pb0242b1c.sao_sum K n hK1 β) n
  have hEm : ∀ I, MeasurableSet {ω | E ω I} := by
    intro I
    have hrad : Measurable fun ω : Fin n → Fin K → ℝ =>
        estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L :=
      Pd1470854.meas_piece (Pa12151c4.dm_tauEff K n β I i)
        (fun d ω => estRadius K d (qEff K n β (tableAdv ω) I i) t L)
        (fun d => (Pa12151c4.meas_estRadius_q K d t L).comp (Pa12151c4.meas_qEff K n β I i))
        (fun _ => rfl)
    refine measurableSet_setOf.mpr (Measurable.imp ?_ ?_)
    · exact measurableSet_setOf.mp ((Pa12151c4.dm_tau0 K n β I).pre {d | t ≤ d})
    · exact measurableSet_setOf.mp (measurableSet_le
        (continuous_abs.measurable.comp ((Pa12151c4.meas_estAvg K n β I i t).sub_const _)) hrad)
  set f : (Fin n → Fin K → ℝ) → ℝ := fun ω => probEvent n (sao K n β) (tableAdv ω) (E ω) with hf
  have hfm : Measurable f := by
    simp only [hf]
    unfold probEvent
    exact Finset.measurable_sum _ (fun I _ =>
      Measurable.ite (hEm I) (Pd1470854.meas_pathProb K n β I) measurable_const)
  have hf01 : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1 := by
    intro ω
    simp only [hf]
    unfold probEvent
    have hb : ∀ I : Fin n → Fin K,
        0 ≤ (@ite ℝ (E ω I) (Classical.propDecidable _) (pathProb (sao K n β) (tableAdv ω) I) 0) ∧
        (@ite ℝ (E ω I) (Classical.propDecidable _) (pathProb (sao K n β) (tableAdv ω) I) 0) ≤
          pathProb (sao K n β) (tableAdv ω) I := by
      intro I
      split_ifs
      · exact ⟨(hP01 ω I).1, le_rfl⟩
      · exact ⟨le_rfl, (hP01 ω I).1⟩
    refine ⟨Finset.sum_nonneg (fun I _ => (hb I).1), ?_⟩
    rw [← hsum ω]
    exact Finset.sum_le_sum (fun I _ => (hb I).2)
  have hfi : Integrable f (rewardTableMeasure n ν) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hf01 ω).1]
    exact (hf01 ω).2
  by_cases hδ1 : 1 ≤ δ
  · have : 0 ≤ ∫ ω, f ω ∂(rewardTableMeasure n ν) := integral_nonneg (fun ω => (hf01 ω).1)
    unfold probStoch
    change 1 - δ ≤ ∫ ω, f ω ∂(rewardTableMeasure n ν)
    linarith
  push_neg at hδ1
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hx2 : 2 ≤ 2 * (t : ℝ) ^ 2 / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  have hL2 : 1 / 2 ≤ L := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2 * (t : ℝ) ^ 2 / δ) (by linarith)
    have : (2 * (t : ℝ) ^ 2 / δ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx2
    linarith
  have hexpL : Real.exp (-L) = δ / (2 * (t : ℝ) ^ 2) := by
    rw [hLdef, Real.exp_neg, Real.exp_log (by positivity), inv_div]
  set μi := mean ν i with hμi
  set e := Real.exp (-L) with he
  let lam : Bool × Fin t × Fin t → ℝ := fun m =>
    (if m.1 then 1 else -1) * P9236924e.mu (m.2.2 : ℕ) * ((((m.2.1 : ℕ) : ℝ) + 1) / K)
  let H : Bool × Fin t × Fin t → (Fin n → Fin K → ℝ) → ℝ := fun k ω =>
    ∑ I, pathProb (sao K n β) (tableAdv ω) I * Real.exp (YsumS K n β ω μi i (lam k) t I)
  have hH0 : ∀ k ω, 0 ≤ H k ω := fun k ω =>
    Finset.sum_nonneg (fun I _ => mul_nonneg (hP01 ω I).1 (Real.exp_pos _).le)
  have hHm : ∀ k, Measurable (H k) := by
    intro k
    exact Finset.measurable_sum _ (fun I _ => (Pd1470854.meas_pathProb K n β I).mul
      (meas_YsumS K n β μi i (lam k) t I).exp)
  have hkey : ∀ k, ∫⁻ ω, ENNReal.ofReal (H k ω) ∂(rewardTableMeasure n ν) ≤ 1 := by
    intro k
    have h := key_bound2 ν (sao K n β) (fun h j => (Pd1470854.sao_bounds K n hK1 β h j).1)
      (fun r h x j => Real.exp (exS K n β μi i (lam k) t r h x j))
      (fun _ _ _ _ => (Real.exp_pos _).le)
      (fun r h j => (exS_meas K n β μi i (lam k) t r h j).exp)
      (fun r h => factorS K n hK1 β ν hν i (lam k) t r h) n
    simpa only [H, YsumS, Real.exp_sum] using h
  have hpt : ∀ ω, 1 - f ω ≤ ∑ k, e * H k ω := by
    intro ω
    have h1 : 1 - f ω = ∑ I, (pathProb (sao K n β) (tableAdv ω) I -
        (@ite ℝ (E ω I) (Classical.propDecidable _) (pathProb (sao K n β) (tableAdv ω) I) 0)) := by
      rw [← hsum ω, Finset.sum_sub_distrib]
      rfl
    have h2 : ∑ k, e * H k ω = ∑ I, pathProb (sao K n β) (tableAdv ω) I *
        ∑ k, e * Real.exp (YsumS K n β ω μi i (lam k) t I) := by
      simp only [H, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun I _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [h1, h2]
    refine Finset.sum_le_sum (fun I _ => ?_)
    by_cases hEI : E ω I
    · rw [if_pos hEI, sub_self]
      exact mul_nonneg (hP01 ω I).1
        (Finset.sum_nonneg (fun k _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    · rw [if_neg hEI, sub_zero]
      apply le_mul_of_one_le_right (hP01 ω I).1
      have hE' : t ≤ tau0 K n β (tableAdv ω) I ∧
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t L <
            |estAvg (sao K n β) (tableAdv ω) I i t - μi| := by
        by_contra hc
        apply hEI
        intro h1
        by_contra h2
        exact hc ⟨h1, not_le.1 h2⟩
      obtain ⟨htt, hR⟩ := hE'
      obtain ⟨m, hm⟩ := coverS K n hK β ω μi i t ht htn L hL2 I htt hR
      have hone : 1 ≤ e * Real.exp (YsumS K n β ω μi i (lam m) t I) := by
        rw [he, ← Real.exp_add]
        apply Real.one_le_exp
        have : L ≤ YsumS K n β ω μi i (lam m) t I := hm
        linarith
      exact le_trans hone (Finset.single_le_sum
        (f := fun k : Bool × Fin t × Fin t => e * Real.exp (YsumS K n β ω μi i (lam k) t I))
        (fun k _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Finset.mem_univ m))
  have hgm : Measurable (fun ω => 1 - f ω) := measurable_const.sub hfm
  have hepos : 0 ≤ e := (Real.exp_pos _).le
  have hHm' : ∀ k, Measurable (fun ω => ENNReal.ofReal (H k ω)) :=
    fun k => ENNReal.measurable_ofReal.comp (hHm k)
  have hcardE : (Fintype.card (Bool × Fin t × Fin t) : ℝ) * e = δ := by
    rw [card_idx, hexpL]
    have : (0 : ℝ) < 2 * (t : ℝ) ^ 2 := by positivity
    field_simp
  have hlint : ∫⁻ ω, ENNReal.ofReal (1 - f ω) ∂(rewardTableMeasure n ν) ≤ ENNReal.ofReal δ := by
    calc ∫⁻ ω, ENNReal.ofReal (1 - f ω) ∂(rewardTableMeasure n ν)
        ≤ ∫⁻ ω, ∑ k, ENNReal.ofReal e * ENNReal.ofReal (H k ω) ∂(rewardTableMeasure n ν) := by
          refine lintegral_mono (fun ω => ?_)
          have hm : ∀ k, ENNReal.ofReal e * ENNReal.ofReal (H k ω) = ENNReal.ofReal (e * H k ω) :=
            fun k => (ENNReal.ofReal_mul hepos).symm
          rw [Finset.sum_congr rfl (fun k _ => hm k), ← ENNReal.ofReal_sum_of_nonneg
            (fun k _ => mul_nonneg hepos (hH0 k ω))]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ∑ k, ENNReal.ofReal e * ∫⁻ ω, ENNReal.ofReal (H k ω) ∂(rewardTableMeasure n ν) := by
          rw [lintegral_finsetSum]
          · refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [lintegral_const_mul _ (hHm' k)]
          · intro k _
            exact (hHm' k).const_mul _
      _ ≤ ∑ _k : Bool × Fin t × Fin t, ENNReal.ofReal e * 1 := by
          gcongr with k _
          exact hkey k
      _ = ENNReal.ofReal ((Fintype.card (Bool × Fin t × Fin t) : ℝ) * e) := by
          rw [Finset.sum_congr rfl (fun k _ => mul_one (ENNReal.ofReal e)), Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal δ := by rw [hcardE]
  have hg : ∫ ω, (1 - f ω) ∂(rewardTableMeasure n ν) ≤ δ := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (hf01 ω).2))
      hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hlint
  have h1 : ∫ ω, (1 - f ω) ∂(rewardTableMeasure n ν) = 1 - ∫ ω, f ω ∂(rewardTableMeasure n ν) := by
    rw [integral_sub (integrable_const _) hfi]
    simp
  unfold probStoch
  change 1 - δ ≤ ∫ ω, f ω ∂(rewardTableMeasure n ν)
  linarith

end P6cbf72b9

open BestBothWorlds.SAO MeasureTheory in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ)
    (hβ : 1 < β) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ probStoch n (sao K n β) ν (fun ω I =>
      t ≤ tau0 K n β (tableAdv ω) I →
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t
            (Real.log (2 * (t : ℝ) ^ 2 / δ))) := by
  exact P6cbf72b9.main K n hK β ν hν i t ht htn δ hδ
