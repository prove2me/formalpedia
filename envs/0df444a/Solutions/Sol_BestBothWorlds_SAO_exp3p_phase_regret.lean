-- Prove2me | solution 1 for BestBothWorlds.SAO.exp3p_phase_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T07:44:48.249982+00:00
-- url     : https://prove2.me/submissions/8e9bbe9a-9889-4091-8c99-e4632bc221cc

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


end P925e7ff2

namespace P55803a07

open BestBothWorlds.SAO P8092e862 P925e7ff2

/-! ### Elementary exponential bounds. -/

theorem map_fst_take {K n : ℕ} (adv : Adversary K) (I : Fin n → Fin K) (r : ℕ) :
    ((history adv I).take r).map Prod.fst = (List.ofFn I).take r := by
  unfold history
  rw [List.map_take, List.map_ofFn]
  rfl

theorem exp_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have := (abs_le.mp h).2
  linarith

theorem exp_quad' (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  by_cases h : -1 ≤ x
  · exact exp_quad x (abs_le.mpr ⟨h, hx⟩)
  · push_neg at h
    have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith

/-- The Exp3.P bias factor of Bubeck–Cesa-Bianchi, Lemma 3.1. -/
theorem two_point' (p b g : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    p * Real.exp (b * (g - (g + b) / p)) + (1 - p) * Real.exp (b * (g - b / p)) ≤ 1 := by
  have hgp : p * (g / p) = g := mul_div_cancel₀ g hp0.ne'
  have hgle : g ≤ g / p := by rw [le_div_iff₀ hp0]; nlinarith
  have hpx1 : p * (b * (g - g / p)) = -(b * g * (1 - p)) := by linear_combination (-b) * hgp
  have hx1 : b * (g - g / p) ≤ 1 := by
    have : b * (g - g / p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb0 (by linarith)
    linarith
  have hx0 : b * g ≤ 1 := by nlinarith
  have e1 : Real.exp (b * (g - (g + b) / p)) ≤
      Real.exp (-(b ^ 2 / p)) * (1 + b * (g - g / p) + (b * (g - g / p)) ^ 2) := by
    rw [show b * (g - (g + b) / p) = -(b ^ 2 / p) + b * (g - g / p) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad' _ hx1) (Real.exp_pos _).le
  have e0 : Real.exp (b * (g - b / p)) ≤
      Real.exp (-(b ^ 2 / p)) * (1 + b * g + (b * g) ^ 2) := by
    rw [show b * (g - b / p) = -(b ^ 2 / p) + b * g by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (exp_quad' _ hx0) (Real.exp_pos _).le
  have hQ : p * (b * (g - g / p)) ^ 2 + (1 - p) * (b * g) ^ 2 ≤ b ^ 2 / p := by
    rw [le_div_iff₀ hp0]
    have e : (p * (b * (g - g / p)) ^ 2 + (1 - p) * (b * g) ^ 2) * p =
        b ^ 2 * (g ^ 2 * (1 - p)) := by
      linear_combination (p * (b * (g - g / p)) - b * g * (1 - p)) * hpx1
    rw [e]
    have h1 : g ^ 2 ≤ 1 := by nlinarith
    have h2 : g ^ 2 * (1 - p) ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg g) hp0.le]
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg b)
    linarith
  have hlin : p * (b * (g - g / p)) + (1 - p) * (b * g) = 0 := by
    linear_combination hpx1
  have hea : Real.exp (-(b ^ 2 / p)) * (1 + b ^ 2 / p) ≤ 1 := by
    have h1 := Real.add_one_le_exp (b ^ 2 / p)
    have h2 : Real.exp (-(b ^ 2 / p)) * Real.exp (b ^ 2 / p) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(b ^ 2 / p)) * (1 + b ^ 2 / p)
        ≤ Real.exp (-(b ^ 2 / p)) * Real.exp (b ^ 2 / p) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := h2
  have hp1' : 0 ≤ 1 - p := by linarith
  have hE := Real.exp_pos (-(b ^ 2 / p))
  calc p * Real.exp (b * (g - (g + b) / p)) + (1 - p) * Real.exp (b * (g - b / p))
      ≤ p * (Real.exp (-(b ^ 2 / p)) * (1 + b * (g - g / p) + (b * (g - g / p)) ^ 2)) +
        (1 - p) * (Real.exp (-(b ^ 2 / p)) * (1 + b * g + (b * g) ^ 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hp0.le) (mul_le_mul_of_nonneg_left e0 hp1')
    _ = Real.exp (-(b ^ 2 / p)) * (1 + (p * (b * (g - g / p)) + (1 - p) * (b * g)) +
          (p * (b * (g - g / p)) ^ 2 + (1 - p) * (b * g) ^ 2)) := by ring
    _ ≤ Real.exp (-(b ^ 2 / p)) * (1 + b ^ 2 / p) := by
        rw [hlin]
        exact mul_le_mul_of_nonneg_left (by linarith) hE.le
    _ ≤ 1 := hea

theorem factorP {K : ℕ} (p : Fin K → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (i : Fin K)
    (b g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hpi : 0 < p i) :
    ∑ j, p j * Real.exp (b * (g - ((if j = i then g else 0) + b) / p i)) ≤ 1 := by
  have hpi1 : p i ≤ 1 := by
    rw [← hp1]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  rw [Fintype.sum_eq_add_sum_compl i]
  have hrest : ∑ j ∈ ({i}ᶜ : Finset (Fin K)),
      p j * Real.exp (b * (g - ((if j = i then g else 0) + b) / p i)) =
      (1 - p i) * Real.exp (b * (g - b / p i)) := by
    have hs : ∑ j ∈ ({i}ᶜ : Finset (Fin K)), p j = 1 - p i := by
      rw [← hp1, Fintype.sum_eq_add_sum_compl i p]; ring
    rw [← hs, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := by simpa using hj
    simp only [hji, if_false, zero_add]
  rw [hrest, if_pos rfl]
  exact two_point' (p i) b g hpi hpi1 hg0 hg1 hb0 hb1

/-! ### The supermartingale of Lemma 3.1, along SAO. -/

noncomputable def bh (K n : ℕ) (β : ℝ) (h : History K) : ℝ :=
  match (saoState K n β h).tau0 with
  | none => 0
  | some τ => (exp3PTuned K (n - τ) (K / β)).betaP

theorem bh_bounds (K n : ℕ) (β : ℝ) (h : History K) : 0 ≤ bh K n β h ∧ bh K n β h ≤ 1 := by
  unfold bh
  cases (saoState K n β h).tau0 with
  | none => exact ⟨le_rfl, zero_le_one⟩
  | some τ => exact ⟨le_min zero_le_one (Real.sqrt_nonneg _), min_le_left _ _⟩

noncomputable def exF (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (h : History K)
    (j : Fin K) : ℝ :=
  if 0 < sao K n β h i ∧ 0 ≤ adv (h.map Prod.fst) i ∧ adv (h.map Prod.fst) i ≤ 1 then
    bh K n β h * (adv (h.map Prod.fst) i -
      ((if j = i then adv (h.map Prod.fst) i else 0) + bh K n β h) / sao K n β h i)
  else 0

theorem exF_ok (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (i : Fin K) (h : History K) :
    ∑ j, sao K n β h j * Real.exp (exF K n β adv i h j) ≤ 1 := by
  unfold exF
  by_cases hc : 0 < sao K n β h i ∧ 0 ≤ adv (h.map Prod.fst) i ∧ adv (h.map Prod.fst) i ≤ 1
  · simp only [if_pos hc]
    exact factorP (sao K n β h) (sao_nonneg K n hK β h) (sao_sum K n hK β h) i _ _ hc.2.1 hc.2.2
      (bh_bounds K n β h).1 (bh_bounds K n β h).2 hc.1
  · simp only [if_neg hc, Real.exp_zero, mul_one]
    rw [sao_sum K n hK β h]

noncomputable def Ysum (K n : ℕ) (β : ℝ) (adv : Adversary K) (i : Fin K) (I : Fin n → Fin K) : ℝ :=
  ∑ r : Fin n, exF K n β adv i ((history adv I).take r) (I r)

theorem Ysum_mart (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (i : Fin K) :
    ∑ I : Fin n → Fin K, pathProb (sao K n β) adv I * Real.exp (Ysum K n β adv i I) ≤ 1 := by
  have h := supermart (sao K n β) (sao_nonneg K n hK β) adv
    (fun _ h j => Real.exp (exF K n β adv i h j)) (fun _ _ _ => (Real.exp_pos _).le)
    (fun _ h => exF_ok K n hK β adv i h) n
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun I _ => ?_)
  unfold Ysum
  rw [Real.exp_sum]

theorem prob_main (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (adv : Adversary K) (L : ℝ)
    (E : (Fin n → Fin K) → Prop)
    (hE : ∀ I, (∀ i, Ysum K n β adv i I < L) → E I) :
    1 - K * Real.exp (-L) ≤ probEvent n (sao K n β) adv E := by
  have hpp : ∀ I : Fin n → Fin K, 0 ≤ pathProb (sao K n β) adv I := fun I =>
    Finset.prod_nonneg (fun r _ => sao_nonneg K n hK β _ _)
  have htot := sum_pathProb' (sao K n β) (sao_sum K n hK β) adv n
  refine prob_ge (sao K n β) adv E htot hpp
    (fun k I => if hk : k < K then L ≤ Ysum K n β adv ⟨k, hk⟩ I else False) K (Real.exp (-L))
    ?_ ?_
  · intro I hI
    by_contra hcon
    apply hI
    apply hE
    intro i
    by_contra hi
    refine hcon ⟨i.val, i.isLt, ?_⟩
    rw [dif_pos i.isLt]
    exact not_lt.mp hi
  · intro k hk
    have e : (fun I => if hk' : k < K then L ≤ Ysum K n β adv ⟨k, hk'⟩ I else False) =
        (fun I => L ≤ Ysum K n β adv ⟨k, hk⟩ I) := by
      funext I; rw [dif_pos hk]
    rw [e]
    exact markov (sao K n β) adv hpp _ L (Ysum_mart K n hK β adv ⟨k, hk⟩)

/-! ### `τ₀` along a path. -/

theorem tau_struct (K n : ℕ) (hK0 : 0 < K) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) :
    tau0 K n β adv I ≤ n ∧
    ∀ r, r < n →
      (r < tau0 K n β adv I → (saoState K n β ((history adv I).take r)).tau0 = none) ∧
      (tau0 K n β adv I ≤ r →
        (saoState K n β ((history adv I).take r)).tau0 = some (tau0 K n β adv I)) := by
  classical
  set S : ℕ → SAOState K := fun u => saoState K n β ((history adv I).take u) with hSdef
  have hlater : ∀ a b, a ≤ b → ∃ l : History K, S b = l.foldl (saoStep K β) (S a) :=
    fun a b hab => later K n β (history adv I) a b hab
  have hstep : ∀ u (h : u < n),
      S (u + 1) = saoStep K β (S u) (I ⟨u, h⟩, reward adv I ⟨u, h⟩ (I ⟨u, h⟩)) := by
    intro u h
    show saoState K n β _ = _
    unfold saoState
    rw [take_succ_hist adv I u h, List.foldl_append]
    rfl
  have hinv : ∀ u, Inv (S u) := fun u => inv_fold K β _ _ (inv_init K n)
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
  have hSt : ∀ u, (S u).t ≤ u := by
    intro u
    have h1 := t_fold K β ((history adv I).take u) (SAOState.init K n)
    have h2 : ((history adv I).take u).length ≤ u := by simp [List.length_take]
    have h3 : (SAOState.init K n).t = 0 := rfl
    show (saoState K n β _).t ≤ u
    unfold saoState
    omega
  have htnone : ∀ u, u ≤ n → (S u).tau0 = none → (S u).t = u := by
    intro u
    induction u with
    | zero => intro _ _; rfl
    | succ u ih =>
      intro hu hz
      have hun : u < n := by omega
      have hz' : (S u).tau0 = none := hback (u + 1) u (by omega) hz
      have h1 := ih (by omega) hz'
      have e := hstep u hun
      obtain ⟨r, _, _, _, _, ht, _⟩ := step_spec K β (S u)
        (I ⟨u, hun⟩, reward adv I ⟨u, hun⟩ (I ⟨u, hun⟩)) hz'
      rw [e, ht, h1]
  have hfut : ∀ r d, r + d ≤ n → (S r).tau0 = none →
      ((S (r + d)).tau0 = none ∨ ∃ τ, r < τ ∧ (S (r + d)).tau0 = some τ) := by
    intro r d
    induction d with
    | zero => intro _ h; left; exact h
    | succ d ih =>
      intro hd hr
      have hlt : r + d < n := by omega
      have e : S (r + (d + 1)) = saoStep K β (S (r + d))
          (I ⟨r + d, hlt⟩, reward adv I ⟨r + d, hlt⟩ (I ⟨r + d, hlt⟩)) := hstep (r + d) hlt
      rcases ih (by omega) hr with h0 | ⟨τ, hτ, hs⟩
      · obtain ⟨_, _, _, _, _, _, hτ0, _⟩ := step_spec K β (S (r + d))
          (I ⟨r + d, hlt⟩, reward adv I ⟨r + d, hlt⟩ (I ⟨r + d, hlt⟩)) h0
        rw [e]
        rcases hτ0 with h1 | h1
        · left; exact h1
        · right
          refine ⟨(S (r + d)).t + 1, ?_, h1⟩
          have := htnone (r + d) (by omega) h0
          omega
      · right
        refine ⟨τ, hτ, ?_⟩
        rw [e, step_frozen K β _ _ τ hs]
        exact hs
  set T0 := tau0 K n β adv I with hT0
  have hT0n : T0 ≤ n := by
    rw [htau0def]
    cases hz : (S n).tau0 with
    | none => exact le_rfl
    | some τ => exact ((hinv n).2.1 τ hz).trans (hSt n)
  refine ⟨hT0n, fun r hrn => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · cases hz : (S r).tau0 with
    | none => rfl
    | some τ =>
      exfalso
      have hτu : τ ≤ r := ((hinv r).2.1 τ hz).trans (hSt r)
      obtain ⟨l, hl⟩ := hlater r n (by omega)
      have hSn : S n = S r := by rw [hl]; exact frozen_fold K β τ l _ hz
      have : T0 = τ := by rw [htau0def, hSn, hz]
      omega
  · cases hz : (S r).tau0 with
    | none =>
      exfalso
      have h := hfut r (n - r) (by omega) hz
      have hrn' : r + (n - r) = n := by omega
      rw [hrn'] at h
      rcases h with h | ⟨τ, hτ, hs⟩
      · have : T0 = n := by rw [htau0def, h]
        omega
      · have : T0 = τ := by rw [htau0def, hs]
        omega
    | some τ =>
      obtain ⟨l, hl⟩ := hlater r n (by omega)
      have hSn : S n = S r := by rw [hl]; exact frozen_fold K β τ l _ hz
      have : T0 = τ := by rw [htau0def, hSn, hz]
      rw [this]

/-! ### Deterministic analysis of Exp3.P (Bubeck–Cesa-Bianchi, Theorem 3.2). -/

noncomputable def Pv (K : ℕ) (prm : Exp3PParams) (G : Fin K → ℝ) : Fin K → ℝ :=
  fun i => (1 - prm.gamma) * Real.exp (prm.eta * G i) / ∑ k, Real.exp (prm.eta * G k) +
    prm.gamma / K

noncomputable def Phi (K : ℕ) (prm : Exp3PParams) (G : Fin K → ℝ) : ℝ :=
  Real.log (∑ k, Real.exp (prm.eta * G k))

theorem Pv_ge (K : ℕ) (hK : 1 ≤ K) (prm : Exp3PParams) (hγ1 : prm.gamma ≤ 1) (G : Fin K → ℝ)
    (i : Fin K) : prm.gamma / K ≤ Pv K prm G i := by
  have hW : 0 < ∑ k, Real.exp (prm.eta * G k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have : 0 ≤ (1 - prm.gamma) * Real.exp (prm.eta * G i) / ∑ k, Real.exp (prm.eta * G k) :=
    div_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hW.le
  unfold Pv
  linarith

theorem step_pot (K : ℕ) (hK : 1 ≤ K) (prm : Exp3PParams) (hγ0 : 0 < prm.gamma)
    (hγ1 : prm.gamma < 1) (hη : 0 < prm.eta) (hb : 0 ≤ prm.betaP)
    (hηb : prm.eta * (1 + prm.betaP) * K ≤ prm.gamma)
    (G : Fin K → ℝ) (a : Fin K) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Phi K prm (fun i => G i + ((if a = i then x else 0) + prm.betaP) / Pv K prm G i) ≤
      Phi K prm G + prm.eta / (1 - prm.gamma) * (x + K * prm.betaP) +
        prm.eta ^ 2 * (1 + prm.betaP) / (1 - prm.gamma) *
          ∑ i, ((if a = i then x else 0) + prm.betaP) / Pv K prm G i := by
  classical
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set η := prm.eta with hηd
  set γ := prm.gamma with hγd
  set b := prm.betaP with hbd
  have h1γ : 0 < 1 - γ := by linarith
  set W := ∑ k, Real.exp (η * G k) with hW
  have hWpos : 0 < W := Finset.sum_pos (fun k _ => Real.exp_pos _) hne
  set p := Pv K prm G with hp
  have hpe : ∀ i, p i = (1 - γ) * Real.exp (η * G i) / W + γ / K := fun i => rfl
  have hγK : 0 < γ / K := div_pos hγ0 hK0
  have hpK : ∀ i, γ / K ≤ p i := fun i => Pv_ge K hK prm hγ1.le G i
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hγK (hpK i)
  have he : ∀ i, (1 - γ) * Real.exp (η * G i) ≤ W * p i := fun i => by
    have e : W * p i = (1 - γ) * Real.exp (η * G i) + W * (γ / K) := by
      rw [hpe, mul_add]; congr 1; field_simp
    have : 0 ≤ W * (γ / K) := mul_nonneg hWpos.le hγK.le
    linarith
  have hc0 : ∀ i, 0 ≤ (if a = i then x else 0) := fun i => by split_ifs <;> linarith
  have hc1 : ∀ i, (if a = i then x else 0) ≤ 1 := fun i => by split_ifs <;> linarith
  set gt : Fin K → ℝ := fun i => ((if a = i then x else 0) + b) / p i with hgt
  have hgt0 : ∀ i, 0 ≤ gt i := fun i => div_nonneg (by linarith [hc0 i]) (hp0 i).le
  have hpgt : ∀ i, p i * gt i = (if a = i then x else 0) + b := fun i => by
    simp only [hgt]; field_simp [(hp0 i).ne']
  have hηgt : ∀ i, η * gt i ≤ 1 := fun i => by
    have h1 : η * ((if a = i then x else 0) + b) ≤ η * (1 + b) :=
      mul_le_mul_of_nonneg_left (by linarith [hc1 i]) hη.le
    have h2 : η * (1 + b) ≤ γ / K := by rw [le_div_iff₀ hK0]; linarith
    have h3 : η * gt i * p i = η * ((if a = i then x else 0) + b) := by
      rw [mul_assoc, mul_comm (gt i), hpgt]
    by_contra hcon
    push_neg at hcon
    have : p i < η * gt i * p i := lt_mul_of_one_lt_left (hp0 i) hcon
    linarith [hpK i]
  have hsum1 : ∑ k, p k * gt k = x + K * b := by
    rw [Finset.sum_congr rfl (fun k _ => hpgt k), Finset.sum_add_distrib]
    simp
  have hterm : ∀ k, Real.exp (η * (G k + gt k)) ≤
      Real.exp (η * G k) + W / (1 - γ) * (η * (p k * gt k) + η ^ 2 * (1 + b) * gt k) := by
    intro k
    have hq := exp_quad' (η * gt k) (hηgt k)
    have hE := Real.exp_pos (η * G k)
    have h1 : 0 ≤ η * gt k + (η * gt k) ^ 2 := by have := hgt0 k; positivity
    have h2 : Real.exp (η * G k) ≤ W * p k / (1 - γ) := by
      rw [le_div_iff₀ h1γ]; linarith [he k]
    have h3 : p k * gt k ^ 2 ≤ (1 + b) * gt k := by
      have : p k * gt k ^ 2 = (p k * gt k) * gt k := by ring
      rw [this, hpgt]; exact mul_le_mul_of_nonneg_right (by linarith [hc1 k]) (hgt0 k)
    calc Real.exp (η * (G k + gt k)) = Real.exp (η * G k) * Real.exp (η * gt k) := by
          rw [mul_add, Real.exp_add]
      _ ≤ Real.exp (η * G k) * (1 + η * gt k + (η * gt k) ^ 2) :=
          mul_le_mul_of_nonneg_left hq hE.le
      _ = Real.exp (η * G k) + Real.exp (η * G k) * (η * gt k + (η * gt k) ^ 2) := by ring
      _ ≤ Real.exp (η * G k) + W * p k / (1 - γ) * (η * gt k + (η * gt k) ^ 2) := by
          have := mul_le_mul_of_nonneg_right h2 h1
          linarith
      _ = Real.exp (η * G k) + W / (1 - γ) * (η * (p k * gt k) + η ^ 2 * (p k * gt k ^ 2)) := by
          ring
      _ ≤ Real.exp (η * G k) + W / (1 - γ) * (η * (p k * gt k) + η ^ 2 * (1 + b) * gt k) := by
          have hW1 : 0 ≤ W / (1 - γ) := div_nonneg hWpos.le h1γ.le
          have : η ^ 2 * (p k * gt k ^ 2) ≤ η ^ 2 * ((1 + b) * gt k) :=
            mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
          have := mul_le_mul_of_nonneg_left
            (show η * (p k * gt k) + η ^ 2 * (p k * gt k ^ 2) ≤
              η * (p k * gt k) + η ^ 2 * (1 + b) * gt k by linarith) hW1
          linarith
  set R := η / (1 - γ) * (x + K * b) + η ^ 2 * (1 + b) / (1 - γ) * ∑ i, gt i with hR
  have hnew : ∑ k, Real.exp (η * (G k + gt k)) ≤ W * (1 + R) := by
    calc ∑ k, Real.exp (η * (G k + gt k))
        ≤ ∑ k, (Real.exp (η * G k) +
            W / (1 - γ) * (η * (p k * gt k) + η ^ 2 * (1 + b) * gt k)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = W + W / (1 - γ) * (η * ∑ k, p k * gt k + η ^ 2 * (1 + b) * ∑ k, gt k) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ = W * (1 + R) := by
          rw [hsum1, hR]
          field_simp
  have hR0 : 0 ≤ R := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hgt0 i)
    have hx : 0 ≤ x + K * b := by positivity
    rw [hR]
    have h1 : 0 ≤ η / (1 - γ) * (x + K * b) := mul_nonneg (div_nonneg hη.le h1γ.le) hx
    have h2 : 0 ≤ η ^ 2 * (1 + b) / (1 - γ) * ∑ i, gt i :=
      mul_nonneg (div_nonneg (by positivity) h1γ.le) this
    linarith
  have hpos : 0 < ∑ k, Real.exp (η * (G k + gt k)) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) hne
  have key : Real.log (∑ k, Real.exp (η * (G k + gt k))) ≤ Real.log W + R := by
    calc Real.log (∑ k, Real.exp (η * (G k + gt k))) ≤ Real.log (W * (1 + R)) :=
          Real.log_le_log hpos hnew
      _ = Real.log W + Real.log (1 + R) := Real.log_mul hWpos.ne' (by linarith)
      _ ≤ Real.log W + R := by
          have := Real.log_le_sub_one_of_pos (show 0 < 1 + R by linarith)
          linarith
  have e1 : Phi K prm (fun i => G i + ((if a = i then x else 0) + prm.betaP) / Pv K prm G i) =
      Real.log (∑ k, Real.exp (η * (G k + gt k))) := rfl
  have e2 : Phi K prm G = Real.log W := rfl
  rw [e1, e2]
  have e3 : (∑ i, ((if a = i then x else 0) + prm.betaP) / Pv K prm G i) = ∑ i, gt i := rfl
  rw [e3]
  linarith

theorem seq_pot (K : ℕ) (hK : 1 ≤ K) (prm : Exp3PParams) (hγ0 : 0 < prm.gamma)
    (hγ1 : prm.gamma < 1) (hη : 0 < prm.eta) (hb : 0 ≤ prm.betaP)
    (hηb : prm.eta * (1 + prm.betaP) * K ≤ prm.gamma)
    (St : ℕ → (Fin K → ℝ) × (Fin K → ℝ)) (a : ℕ → Fin K) (x : ℕ → ℝ) (m : ℕ)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (h0 : St 0 = (fun _ => 1 / (K : ℝ), fun _ => 0))
    (hs : ∀ k, k < m → St (k + 1) = exp3PStep K prm (St k) (a k, x k)) :
    ∀ u, u ≤ m → (St u).1 = Pv K prm (St u).2 ∧
      (∀ j, (St u).2 j = ∑ k ∈ Finset.range u,
        ((if a k = j then x k else 0) + prm.betaP) / (St k).1 j) ∧
      Phi K prm (St u).2 ≤ Real.log K + prm.eta / (1 - prm.gamma) *
        (∑ k ∈ Finset.range u, x k + u * K * prm.betaP) +
        prm.eta ^ 2 * (1 + prm.betaP) / (1 - prm.gamma) * ∑ j, (St u).2 j := by
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  intro u
  induction u with
  | zero =>
    intro _
    rw [h0]
    refine ⟨?_, ?_, ?_⟩
    · funext i
      simp only [Pv, mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring
    · intro j; simp
    · simp [Phi]
  | succ u ih =>
    intro hu
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    have e := hs u (by omega)
    have hst2 : ∀ j, (St (u + 1)).2 j =
        (St u).2 j + ((if a u = j then x u else 0) + prm.betaP) / (St u).1 j := by
      intro j; rw [e]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; rfl
    · intro j
      rw [hst2, Finset.sum_range_succ, ih2 j]
    · have hG : (St (u + 1)).2 = fun i => (St u).2 i +
          ((if a u = i then x u else 0) + prm.betaP) / Pv K prm (St u).2 i := by
        funext i; rw [hst2, ih1]
      have hp := step_pot K hK prm hγ0 hγ1 hη hb hηb (St u).2 (a u) (x u) (hx u).1 (hx u).2
      rw [← hG] at hp
      have hsum : ∑ j, (St (u + 1)).2 j = ∑ j, (St u).2 j +
          ∑ i, ((if a u = i then x u else 0) + prm.betaP) / Pv K prm (St u).2 i := by
        rw [hG, Finset.sum_add_distrib]
      rw [hsum, Finset.sum_range_succ]
      push_cast
      have h1γ : 0 < 1 - prm.gamma := by linarith
      set A := prm.eta / (1 - prm.gamma)
      set B := prm.eta ^ 2 * (1 + prm.betaP) / (1 - prm.gamma)
      nlinarith [ih3, hp]

/-! ### The arithmetic of (3.10). -/

set_option maxHeartbeats 1000000 in
theorem det_arith (Kr mr u b η γ lnK L M G Gh Gt : ℝ) (hK : 2 ≤ Kr) (hm : 0 < mr) (hu : 0 < u)
    (hub : u ≤ b) (hb : b ≤ 971 / 10000) (hKu : Kr * u ≤ 1 / 5) (hη : η = 19 / 20 * u)
    (hγ : γ = 21 / 20 * Kr * u) (hlnK : lnK = mr * Kr * u ^ 2) (hL : L = mr * Kr * b ^ 2)
    (h1 : η * M ≤ lnK + η / (1 - γ) * (Gh + mr * Kr * b) + η ^ 2 * (1 + b) / (1 - γ) * (Kr * M))
    (h2 : b * (G - Gt) < L) (h3 : Gt ≤ M) (h4 : G ≤ mr) (h5 : 0 ≤ G) :
    G - Gh ≤ 103 / 20 * (mr * Kr * b) := by
  subst hη hγ hlnK hL
  have hb0 : 0 < b := lt_of_lt_of_le hu hub
  have hKu0 : 0 ≤ Kr * u := by positivity
  have hd : 0 < 1 - 21 / 20 * Kr * u := by linarith
  have hdne : 1 - 21 / 20 * Kr * u ≠ 0 := hd.ne'
  have h1' : (1 - 21 / 20 * Kr * u) * (19 / 20 * u * M) ≤
      (1 - 21 / 20 * Kr * u) * (mr * Kr * u ^ 2) + 19 / 20 * u * (Gh + mr * Kr * b) +
        (19 / 20 * u) ^ 2 * (1 + b) * (Kr * M) := by
    have := mul_le_mul_of_nonneg_left h1 hd.le
    have e1 : (1 - 21 / 20 * Kr * u) * (19 / 20 * u / (1 - 21 / 20 * Kr * u) *
        (Gh + mr * Kr * b)) = 19 / 20 * u * (Gh + mr * Kr * b) := by
      calc (1 - 21 / 20 * Kr * u) * (19 / 20 * u / (1 - 21 / 20 * Kr * u) * (Gh + mr * Kr * b))
          = ((1 - 21 / 20 * Kr * u) / (1 - 21 / 20 * Kr * u)) * (19 / 20 * u * (Gh + mr * Kr * b)) := by
            ring
        _ = 19 / 20 * u * (Gh + mr * Kr * b) := by rw [div_self hdne, one_mul]
    have e2 : (1 - 21 / 20 * Kr * u) * ((19 / 20 * u) ^ 2 * (1 + b) / (1 - 21 / 20 * Kr * u) *
        (Kr * M)) = (19 / 20 * u) ^ 2 * (1 + b) * (Kr * M) := by
      calc (1 - 21 / 20 * Kr * u) * ((19 / 20 * u) ^ 2 * (1 + b) / (1 - 21 / 20 * Kr * u) * (Kr * M))
          = ((1 - 21 / 20 * Kr * u) / (1 - 21 / 20 * Kr * u)) * ((19 / 20 * u) ^ 2 * (1 + b) * (Kr * M)) := by
            ring
        _ = (19 / 20 * u) ^ 2 * (1 + b) * (Kr * M) := by rw [div_self hdne, one_mul]
    rw [mul_add, mul_add, e1, e2] at this
    exact this
  have h1'' : (1 - 21 / 20 * Kr * u) * M ≤
      20 / 19 * ((1 - 21 / 20 * Kr * u) * (mr * Kr * u)) + (Gh + mr * Kr * b) +
        19 / 20 * u * (1 + b) * Kr * M := by
    have hmul : u * (19 / 20 * ((1 - 21 / 20 * Kr * u) * M)) ≤
        u * ((1 - 21 / 20 * Kr * u) * (mr * Kr * u) + 19 / 20 * (Gh + mr * Kr * b) +
          (19 / 20) ^ 2 * u * (1 + b) * Kr * M) := by
      have e1 : u * (19 / 20 * ((1 - 21 / 20 * Kr * u) * M)) =
          (1 - 21 / 20 * Kr * u) * (19 / 20 * u * M) := by ring
      have e2 : u * ((1 - 21 / 20 * Kr * u) * (mr * Kr * u) + 19 / 20 * (Gh + mr * Kr * b) +
          (19 / 20) ^ 2 * u * (1 + b) * Kr * M) =
          (1 - 21 / 20 * Kr * u) * (mr * Kr * u ^ 2) + 19 / 20 * u * (Gh + mr * Kr * b) +
            (19 / 20 * u) ^ 2 * (1 + b) * (Kr * M) := by ring
      rw [e1, e2]
      exact h1'
    have := le_of_mul_le_mul_left hmul hu
    linarith
  set c := 1 - 21 / 20 * Kr * u - 19 / 20 * u * (1 + b) * Kr with hc
  have hKub : Kr * u * b ≤ Kr * u * (971 / 10000) := mul_le_mul_of_nonneg_left hb hKu0
  have hc0 : 0 ≤ c := by
    have e : c = 1 - 2 * (Kr * u) - 19 / 20 * (Kr * u * b) := by rw [hc]; ring
    rw [e]
    linarith
  have hc1 : c ≤ 1 := by
    have e : c = 1 - 2 * (Kr * u) - 19 / 20 * (Kr * u * b) := by rw [hc]; ring
    have : 0 ≤ Kr * u * b := by positivity
    rw [e]
    linarith
  have hcM : c * M ≤ 20 / 19 * ((1 - 21 / 20 * Kr * u) * (mr * Kr * u)) + (Gh + mr * Kr * b) := by
    have e : c * M = (1 - 21 / 20 * Kr * u) * M - 19 / 20 * u * (1 + b) * Kr * M := by
      rw [hc]; ring
    rw [e]
    linarith
  have hG2 : G - Gt < mr * Kr * b := by
    by_contra hcon
    have hcon' : mr * Kr * b ≤ G - Gt := not_lt.mp hcon
    have := mul_le_mul_of_nonneg_left hcon' hb0.le
    have e : b * (mr * Kr * b) = mr * Kr * b ^ 2 := by ring
    linarith
  have hD : c * (G - mr * Kr * b) ≤ c * M := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hA : (1 - c) * G ≤ (1 - c) * mr := mul_le_mul_of_nonneg_left h4 (by linarith)
  have hP : 0 ≤ mr * Kr * b := by positivity
  have hB : c * (mr * Kr * b) ≤ mr * Kr * b := by
    have := mul_le_mul_of_nonneg_right hc1 hP
    linarith
  have hC : (1 - 21 / 20 * Kr * u) * (mr * Kr * u) ≤ mr * Kr * u := by
    have : 0 ≤ Kr * u * (mr * Kr * u) := by positivity
    have e : (1 - 21 / 20 * Kr * u) * (mr * Kr * u) = mr * Kr * u - 21 / 20 * (Kr * u * (mr * Kr * u)) := by
      ring
    rw [e]
    linarith
  have hA' : (1 - c) * mr = mr * Kr * (u * (2 + 19 / 20 * b)) := by rw [hc]; ring
  have hE : u * (2 + 19 / 20 * b) + 20 / 19 * u ≤ 63 / 20 * b := by
    have h1 := mul_le_mul_of_nonneg_right hub (show 0 ≤ 2 + 19 / 20 * b + 20 / 19 by positivity)
    have h2 : b * b ≤ 971 / 10000 * b := mul_le_mul_of_nonneg_right hb hb0.le
    have e1 : u * (2 + 19 / 20 * b) + 20 / 19 * u ≤ b * (2 + 19 / 20 * b + 20 / 19) := by
      have e : u * (2 + 19 / 20 * b) + 20 / 19 * u = u * (2 + 19 / 20 * b + 20 / 19) - 0 := by ring
      rw [e]
      have : u * (2 + 19 / 20 * b + 20 / 19) ≤ b * (2 + 19 / 20 * b + 20 / 19) := h1
      linarith
    have e2 : b * (2 + 19 / 20 * b + 20 / 19) = 2 * b + 19 / 20 * (b * b) + 20 / 19 * b := by ring
    linarith
  have hF := mul_le_mul_of_nonneg_left hE (show 0 ≤ mr * Kr by positivity)
  have eF : mr * Kr * (u * (2 + 19 / 20 * b) + 20 / 19 * u) =
      mr * Kr * (u * (2 + 19 / 20 * b)) + 20 / 19 * (mr * Kr * u) := by ring
  have eF2 : mr * Kr * (63 / 20 * b) = 63 / 20 * (mr * Kr * b) := by ring
  have hfin : G - Gh ≤ (1 - c) * G + c * (mr * Kr * b) +
      20 / 19 * ((1 - 21 / 20 * Kr * u) * (mr * Kr * u)) + mr * Kr * b := by
    have e1 : c * (G - mr * Kr * b) = c * G - c * (mr * Kr * b) := by ring
    have e2 : (1 - c) * G = G - c * G := by ring
    linarith
  linarith


end P55803a07

namespace P55803a07

open BestBothWorlds.SAO P8092e862 P925e7ff2

theorem reidx (n τ : ℕ) (hτ : τ ≤ n) (F : ℕ → ℝ) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)), F r =
      ∑ k ∈ Finset.range (n - τ), F (τ + k) := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun r => if τ ≤ r then F r else 0) n,
    ← Finset.sum_filter]
  have : (Finset.range n).filter (fun r => τ ≤ r) = Finset.Ico τ n := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]

set_option maxHeartbeats 4000000 in
theorem core (K n : ℕ) (hK : 2 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (adv : Adversary K)
    (hadv : adv.IsBounded) (I : Fin n → Fin K)
    (hY : ∀ i, Ysum K n ((K : ℝ) / δ) adv i I < Real.log ((K : ℝ) / δ)) :
    regretFrom adv I (tau0 K n ((K : ℝ) / δ) adv I) ≤
      5.15 * Real.sqrt (((n : ℝ) - tau0 K n ((K : ℝ) / δ) adv I) * K * Real.log ((K : ℝ) / δ)) := by
  classical
  have hK1 : 1 ≤ K := by omega
  have hK0 : 0 < K := by omega
  haveI : Nonempty (Fin K) := ⟨⟨0, hK0⟩⟩
  set β : ℝ := (K : ℝ) / δ with hβ
  obtain ⟨hT0n, hstr⟩ := tau_struct K n hK0 β adv I
  set T0 := tau0 K n β adv I with hT0
  set m := n - T0 with hm
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  set L := Real.log ((K : ℝ) / δ) with hLdef
  have hlnK0 : 0 < Real.log K := Real.log_pos (by linarith)
  have hKL : Real.log K ≤ L := Real.log_le_log hKpos (by rw [le_div_iff₀ hδ0]; nlinarith)
  have hL0 : 0 < L := lt_of_lt_of_le hlnK0 hKL
  have hcast : ((n : ℝ) - T0) = (m : ℝ) := by rw [hm, Nat.cast_sub hT0n]
  rw [hcast]
  set rw' : ℕ → Fin K → ℝ := fun r j => if h : r < n then reward adv I ⟨r, h⟩ j else 0 with hrw
  set ob : ℕ → ℝ := fun r => if h : r < n then reward adv I ⟨r, h⟩ (I ⟨r, h⟩) else 0 with hob
  have hrw01 : ∀ r j, 0 ≤ rw' r j ∧ rw' r j ≤ 1 := by
    intro r j
    simp only [hrw]
    split_ifs
    · exact hadv _ _
    · exact ⟨le_rfl, zero_le_one⟩
  have hob01 : ∀ r, 0 ≤ ob r ∧ ob r ≤ 1 := by
    intro r
    simp only [hob]
    split_ifs
    · exact hadv _ _
    · exact ⟨le_rfl, zero_le_one⟩
  have hsumG : ∀ i, ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)), reward adv I r i =
      ∑ k ∈ Finset.range m, rw' (T0 + k) i := by
    intro i
    refine (Finset.sum_congr rfl (fun r _ => ?_)).trans (reidx n T0 hT0n (fun r => rw' r i))
    show reward adv I r i = rw' r i
    simp only [hrw, dif_pos r.isLt]
  have hsumGh : ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)), reward adv I r (I r) =
      ∑ k ∈ Finset.range m, ob (T0 + k) := by
    refine (Finset.sum_congr rfl (fun r _ => ?_)).trans (reidx n T0 hT0n ob)
    show reward adv I r (I r) = ob r
    simp only [hob, dif_pos r.isLt]
  have hGle : ∀ i, ∑ k ∈ Finset.range m, rw' (T0 + k) i ≤ m := by
    intro i
    calc ∑ k ∈ Finset.range m, rw' (T0 + k) i ≤ ∑ k ∈ Finset.range m, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => (hrw01 _ _).2)
      _ = m := by simp
  have hG0 : ∀ i, 0 ≤ ∑ k ∈ Finset.range m, rw' (T0 + k) i :=
    fun i => Finset.sum_nonneg (fun k _ => (hrw01 _ _).1)
  have hGh0 : 0 ≤ ∑ k ∈ Finset.range m, ob (T0 + k) :=
    Finset.sum_nonneg (fun k _ => (hob01 _).1)
  unfold regretFrom
  rw [hsumGh]
  have h515 : (5.15 : ℝ) = 103 / 20 := by norm_num
  rw [h515]
  by_cases htriv : (m : ℝ) ≤ 26.5225 * K * L
  · -- the bound exceeds the number of rounds
    have h265 : (26.5225 : ℝ) = 106.09 / 4 := by norm_num
    have hmle : (m : ℝ) ≤ 103 / 20 * Real.sqrt ((m : ℝ) * K * L) := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hsq : (m : ℝ) * 20 / 103 ≤ Real.sqrt ((m : ℝ) * K * L) := by
        rw [show (m : ℝ) * 20 / 103 = Real.sqrt (((m : ℝ) * 20 / 103) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        have : ((m : ℝ) * 20 / 103) ^ 2 = (m : ℝ) * ((m : ℝ) * (400 / 10609)) := by ring
        rw [this]
        have h2 : (m : ℝ) * (400 / 10609) ≤ K * L := by
          have : (26.5225 : ℝ) = 10609 / 400 := by norm_num
          rw [this] at htriv
          linarith
        have := mul_le_mul_of_nonneg_left h2 hm0
        linarith
      linarith
    have hsup : (⨆ i, ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)),
        reward adv I r i) ≤ m := by
      apply ciSup_le
      intro i
      rw [hsumG i]
      exact hGle i
    linarith
  push_neg at htriv
  have h265 : (26.5225 : ℝ) = 10609 / 400 := by norm_num
  rw [h265] at htriv
  have hmr : (0 : ℝ) < m := by
    have : 0 < 10609 / 400 * (K : ℝ) * L := by positivity
    linarith
  have hm1 : 1 ≤ m := by
    have : (0 : ℕ) < m := by exact_mod_cast hmr
    omega
  -- the Exp3.P parameters
  set prm := exp3PTuned K m ((K : ℝ) / β) with hprm
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  have hδne : δ ≠ 0 := hδ0.ne'
  have hmne : (m : ℝ) ≠ 0 := hmr.ne'
  have hKβ : (K : ℝ) / β = δ := by rw [hβ]; field_simp
  set u := Real.sqrt (Real.log K / (m * K)) with hu
  set b := Real.sqrt (L / (m * K)) with hbdef
  have hmK : (0 : ℝ) < m * K := by positivity
  have hu2 : u ^ 2 = Real.log K / (m * K) := Real.sq_sqrt (div_nonneg hlnK0.le hmK.le)
  have hb2 : b ^ 2 = L / (m * K) := Real.sq_sqrt (div_nonneg hL0.le hmK.le)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (div_pos hlnK0 hmK)
  have hub : u ≤ b := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hKL hmK.le)
  have hb0 : 0 < b := lt_of_lt_of_le hu0 hub
  have hlnK : Real.log K = m * K * u ^ 2 := by rw [hu2]; field_simp
  have hLb : L = m * K * b ^ 2 := by rw [hb2]; field_simp
  have hKu2 : (m : ℝ) * (K * u) ^ 2 = K * Real.log K := by rw [hlnK]; ring
  have hKu : K * u ≤ 1 / 5 := by
    have h1 : (m : ℝ) * (K * u) ^ 2 * (10609 / 400) < m := by
      rw [hKu2]
      have : K * Real.log K ≤ K * L := mul_le_mul_of_nonneg_left hKL hKpos.le
      linarith
    have h2 : (K * u) ^ 2 * (10609 / 400) < 1 := by
      by_contra hcon
      have hcon' : 1 ≤ (K * u) ^ 2 * (10609 / 400) := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' hmr.le
      linarith
    have h3 : 0 ≤ K * u := by positivity
    nlinarith
  have hbb : b ≤ 971 / 10000 := by
    have h1 : (m : ℝ) * (K * K * b ^ 2 * (10609 / 400)) < m := by
      have e : (m : ℝ) * (K * K * b ^ 2 * (10609 / 400)) = 10609 / 400 * K * (m * K * b ^ 2) := by
        ring
      rw [e, ← hLb]
      linarith
    have h2 : K * K * b ^ 2 * (10609 / 400) < 1 := by
      by_contra hcon
      have hcon' : 1 ≤ K * K * b ^ 2 * (10609 / 400) := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' hmr.le
      linarith
    have h4 : (4 : ℝ) ≤ K * K := by nlinarith
    have h5 : 4 * b ^ 2 ≤ K * K * b ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg b)
    by_contra hc
    have hc' : 971 / 10000 < b := not_le.mp hc
    have := mul_lt_mul'' hc' hc' (by norm_num) (by norm_num)
    have e : b ^ 2 = b * b := by ring
    linarith
  have h095 : (0.95 : ℝ) = 19 / 20 := by norm_num
  have h105 : (1.05 : ℝ) = 21 / 20 := by norm_num
  have hη : prm.eta = 19 / 20 * u := by
    show 0.95 * Real.sqrt (Real.log K / (m * K)) = 19 / 20 * u
    rw [h095]
  have hsK : Real.sqrt (K * Real.log K / m) = K * u := by
    have e : (K : ℝ) * Real.log K / m = (K * u) ^ 2 := by
      rw [← hKu2]; field_simp
    rw [e]
    exact Real.sqrt_sq (by positivity)
  have hγ : prm.gamma = 21 / 20 * K * u := by
    show min 1 (1.05 * Real.sqrt (K * Real.log K / m)) = 21 / 20 * K * u
    rw [hsK, h105, min_eq_right (by linarith)]
    ring
  have hbP : prm.betaP = b := by
    show min 1 (Real.sqrt (Real.log ((K : ℝ) / ((K : ℝ) / β)) / (m * K))) = b
    rw [hKβ]
    apply min_eq_right
    linarith
  have hγ0 : 0 < prm.gamma := by rw [hγ]; positivity
  have hγ1 : prm.gamma < 1 := by rw [hγ]; linarith
  have hη0 : 0 < prm.eta := by rw [hη]; positivity
  have hbP0 : 0 ≤ prm.betaP := by rw [hbP]; exact hb0.le
  have hηb : prm.eta * (1 + prm.betaP) * K ≤ prm.gamma := by
    rw [hη, hγ, hbP]
    have : K * u * b ≤ K * u * (971 / 10000) := mul_le_mul_of_nonneg_left hbb (by positivity)
    nlinarith
  -- the Exp3.P run after the switch
  set St : ℕ → (Fin K → ℝ) × (Fin K → ℝ) :=
    fun v => exp3PState K prm (((history adv I).take (T0 + v)).drop T0) with hSt
  set a : ℕ → Fin K := fun k => if h : T0 + k < n then I ⟨T0 + k, h⟩ else ⟨0, hK0⟩ with ha
  set x : ℕ → ℝ := fun k => ob (T0 + k) with hx
  have h0 : St 0 = (fun _ => 1 / (K : ℝ), fun _ => 0) := by
    show exp3PState K prm (((history adv I).take (T0 + 0)).drop T0) = _
    rw [Nat.add_zero, List.drop_eq_nil_of_le (by simp [List.length_take])]
    rfl
  have hs : ∀ k, k < m → St (k + 1) = exp3PStep K prm (St k) (a k, x k) := by
    intro k hk
    have hlt : T0 + k < n := by omega
    show exp3PState K prm (((history adv I).take (T0 + (k + 1))).drop T0) =
      exp3PStep K prm (exp3PState K prm (((history adv I).take (T0 + k)).drop T0)) (a k, x k)
    have hlen : T0 ≤ ((history adv I).take (T0 + k)).length := by
      simp only [List.length_take, history, List.length_ofFn]; omega
    rw [show T0 + (k + 1) = T0 + k + 1 by omega, take_succ_hist adv I (T0 + k) hlt,
      List.drop_append_of_le_length hlen]
    unfold exp3PState
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 2
    · simp only [ha, dif_pos hlt]
    · simp only [hx, hob, dif_pos hlt]
  have hxx : ∀ k, 0 ≤ x k ∧ x k ≤ 1 := fun k => hob01 (T0 + k)
  have SP := seq_pot K hK1 prm hγ0 hγ1 hη0 hbP0 hηb St a x m hxx h0 hs
  obtain ⟨hP1, hP2, hP3⟩ := SP m le_rfl
  have hpos : ∀ k, k ≤ m → ∀ j, 0 < (St k).1 j := by
    intro k hk j
    rw [(SP k hk).1]
    exact lt_of_lt_of_le (div_pos hγ0 hKpos) (Pv_ge K hK1 prm hγ1.le _ j)
  have hsao : ∀ k, k < m → sao K n β ((history adv I).take (T0 + k)) = (St k).1 := by
    intro k hk
    have hr := (hstr (T0 + k) (by omega)).2 (by omega)
    unfold sao
    rw [hr]
    rfl
  have hbh : ∀ k, k < m → bh K n β ((history adv I).take (T0 + k)) = prm.betaP := by
    intro k hk
    have hr := (hstr (T0 + k) (by omega)).2 (by omega)
    unfold bh
    rw [hr]
  have hbh0 : ∀ r, r < T0 → r < n → bh K n β ((history adv I).take r) = 0 := by
    intro r hr hrn
    unfold bh
    rw [(hstr r hrn).1 hr]
  -- the supermartingale exponent equals b (G_j - G̃_j)
  have hYeq : ∀ j, Ysum K n β adv j I =
      prm.betaP * (∑ k ∈ Finset.range m, rw' (T0 + k) j - (St m).2 j) := by
    intro j
    unfold Ysum
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin n => T0 ≤ (r : ℕ))]
    have hz : ∑ r ∈ Finset.univ.filter (fun r : Fin n => ¬ T0 ≤ (r : ℕ)),
        exF K n β adv j ((history adv I).take r) (I r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr' : (r : ℕ) < T0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        omega
      unfold exF
      rw [hbh0 r hr' r.isLt]
      simp
    rw [hz, add_zero]
    have hF : ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)),
        exF K n β adv j ((history adv I).take r) (I r) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)),
          (fun r : ℕ => if h : r < n then exF K n β adv j ((history adv I).take r) (I ⟨r, h⟩)
            else 0) r := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [dif_pos r.isLt]
    rw [hF]
    refine (reidx n T0 hT0n (fun r : ℕ => if h : r < n then
      exF K n β adv j ((history adv I).take r) (I ⟨r, h⟩) else 0)).trans ?_
    rw [hP2 j, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < m := Finset.mem_range.mp hk
    have hlt : T0 + k < n := by omega
    simp only [dif_pos hlt]
    have hadvj : adv (((history adv I).take (T0 + k)).map Prod.fst) j = rw' (T0 + k) j := by
      rw [map_fst_take]
      simp only [hrw, dif_pos hlt]
      rfl
    have hak : a k = I ⟨T0 + k, hlt⟩ := by simp only [ha, dif_pos hlt]
    have hxk : x k = rw' (T0 + k) (I ⟨T0 + k, hlt⟩) := by
      simp only [hx, hob, hrw, dif_pos hlt]
    unfold exF
    rw [hsao k hk', hbh k hk', hadvj,
      if_pos (show 0 < (St k).1 j ∧ 0 ≤ rw' (T0 + k) j ∧ rw' (T0 + k) j ≤ 1 from
        ⟨hpos k hk'.le j, (hrw01 _ j).1, (hrw01 _ j).2⟩), hak]
    by_cases hj : I ⟨T0 + k, hlt⟩ = j
    · rw [if_pos hj, if_pos hj, hxk, hj]
    · rw [if_neg hj, if_neg hj]
  -- the deterministic bound
  obtain ⟨jm, _, hjm⟩ := Finset.exists_max_image Finset.univ (fun j => (St m).2 j)
    Finset.univ_nonempty
  have hPhi : prm.eta * (St m).2 jm ≤ Phi K prm (St m).2 := by
    unfold Phi
    rw [← Real.log_exp (prm.eta * (St m).2 jm)]
    exact Real.log_le_log (Real.exp_pos _)
      (Finset.single_le_sum (f := fun k => Real.exp (prm.eta * (St m).2 k))
        (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ jm))
  have hS : ∑ j, (St m).2 j ≤ K * (St m).2 jm := by
    calc ∑ j, (St m).2 j ≤ ∑ _j : Fin K, (St m).2 jm :=
          Finset.sum_le_sum (fun j _ => hjm j (Finset.mem_univ j))
      _ = K * (St m).2 jm := by simp
  have hcoef : 0 ≤ prm.eta ^ 2 * (1 + prm.betaP) / (1 - prm.gamma) :=
    div_nonneg (by positivity) (by linarith)
  have h1 : prm.eta * (St m).2 jm ≤ Real.log K + prm.eta / (1 - prm.gamma) *
      (∑ k ∈ Finset.range m, x k + m * K * prm.betaP) +
      prm.eta ^ 2 * (1 + prm.betaP) / (1 - prm.gamma) * (K * (St m).2 jm) := by
    have := mul_le_mul_of_nonneg_left hS hcoef
    linarith
  rw [hbP] at h1 hYeq
  have hdet : ∀ i, ∑ k ∈ Finset.range m, rw' (T0 + k) i - ∑ k ∈ Finset.range m, ob (T0 + k) ≤
      103 / 20 * (m * K * b) := by
    intro i
    have hYi := hY i
    rw [hYeq i] at hYi
    have h1' : prm.eta * (St m).2 jm ≤ Real.log K + prm.eta / (1 - prm.gamma) *
        (∑ k ∈ Finset.range m, ob (T0 + k) + m * K * b) +
        prm.eta ^ 2 * (1 + b) / (1 - prm.gamma) * (K * (St m).2 jm) := h1
    exact det_arith K m u b prm.eta prm.gamma (Real.log K) L ((St m).2 jm)
      (∑ k ∈ Finset.range m, rw' (T0 + k) i) (∑ k ∈ Finset.range m, ob (T0 + k)) ((St m).2 i)
      hKr hmr hu0 hub hbb hKu hη hγ hlnK hLb h1' hYi (hjm i (Finset.mem_univ i)) (hGle i) (hG0 i)
  have hsq : Real.sqrt ((m : ℝ) * K * L) = m * K * b := by
    rw [show (m : ℝ) * K * L = (m * K * b) ^ 2 by rw [hLb]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have hsup : (⨆ i, ∑ r ∈ Finset.univ.filter (fun r : Fin n => T0 ≤ (r : ℕ)),
      reward adv I r i) ≤ ∑ k ∈ Finset.range m, ob (T0 + k) + 103 / 20 * (m * K * b) := by
    apply ciSup_le
    intro i
    rw [hsumG i]
    linarith [hdet i]
  linarith

end P55803a07

open BestBothWorlds.SAO in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded) :
    1 - δ ≤ probEvent n (sao K n (K / δ)) adv (fun I =>
      regretFrom adv I (tau0 K n (K / δ) adv I) ≤
        5.15 * Real.sqrt (((n : ℝ) - tau0 K n (K / δ) adv I) * K * Real.log (K / δ))) := by
  have h := P55803a07.prob_main K n (by omega) ((K : ℝ) / δ) adv (Real.log ((K : ℝ) / δ)) _
    (fun I hY => P55803a07.core K n hK δ hδ0 hδ1 adv hadv I hY)
  have hK0 : (0 : ℝ) < K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have e : (K : ℝ) * Real.exp (-Real.log ((K : ℝ) / δ)) = δ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hK0 hδ0)]
    field_simp [hK0.ne', hδ0.ne']
  rw [e] at h
  exact h
