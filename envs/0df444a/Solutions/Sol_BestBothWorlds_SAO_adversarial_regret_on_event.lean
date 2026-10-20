-- Prove2me | solution 1 for BestBothWorlds.SAO.adversarial_regret_on_event
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T05:31:40.929682+00:00
-- url     : https://prove2.me/submissions/6375fa3d-04de-4e8e-bfd7-81cb32847a18

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

/-! ### Harmonic sum (from 5292263e). -/

theorem harm_aux {α : Type} [DecidableEq α] (T : α → ℕ) :
    ∀ (m : ℕ) (s : Finset α), s.card = m →
      ∑ i ∈ s, (1 : ℝ) / ((s.filter (fun k => T i ≤ T k)).card : ℝ) ≤ (harmonic m : ℝ) := by
  intro m
  induction m with
  | zero => intro s hs; rw [Finset.card_eq_zero] at hs; subst hs; simp
  | succ m ih =>
    intro s hs
    have hne : s.Nonempty := by rw [← Finset.card_pos, hs]; omega
    obtain ⟨a, ha, hmin⟩ := s.exists_min_image T hne
    rw [← Finset.add_sum_erase s _ ha]
    have h1 : s.filter (fun k => T a ≤ T k) = s := Finset.filter_true_of_mem (fun k hk => hmin k hk)
    rw [h1, hs, harmonic_succ]
    have hcard : (s.erase a).card = m := by rw [Finset.card_erase_of_mem ha, hs]; rfl
    have h3 := ih (s.erase a) hcard
    have h2 : ∑ i ∈ s.erase a, (1 : ℝ) / ((s.filter (fun k => T i ≤ T k)).card : ℝ) ≤
        ∑ i ∈ s.erase a, (1 : ℝ) / (((s.erase a).filter (fun k => T i ≤ T k)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply one_div_le_one_div_of_le
      · have hpos : 0 < ((s.erase a).filter (fun k => T i ≤ T k)).card :=
          Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, le_refl _⟩⟩
        exact_mod_cast hpos
      · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset a s))
    have h4 : (1 : ℝ) / (((m + 1 : ℕ)) : ℝ) = (((m + 1 : ℕ) : ℚ)⁻¹ : ℚ) := by
      push_cast; rw [one_div]
    rw [Rat.cast_add, h4]
    linarith

theorem sumq (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (adv : Adversary K) (hadv : adv.IsBounded) (I : Fin n → Fin K) :
    ∑ i : Fin K, qEff K n β adv I i ≤ 1 + Real.log K := by
  set h := history adv I with hh
  have hlen : h.length = n := by simp [hh, history]
  set S : ℕ → SAOState K := fun r => saoState K n β (h.take r) with hS
  have hF : runState K n β adv I n = S n := rfl
  have hinv : ∀ r, Inv (S r) := fun r => inv_fold K β _ _ (inv_init K n)
  have htle : ∀ r, (S r).t ≤ r := by
    intro r
    have h1 := t_fold K β (h.take r) (SAOState.init K n)
    have h2 : (SAOState.init K n).t = 0 := rfl
    have h3 : (h.take r).length ≤ r := by simp
    have h4 : (S r).t = (List.foldl (saoStep K β) (SAOState.init K n) (h.take r)).t := rfl
    omega
  set T : Fin K → ℕ := fun i => tauEff K n β adv I i with hTdef
  have hT0 : ∀ k, T k ≤ tau0 K n β adv I := fun k => min_le_right _ _
  have hTtau : ∀ k, T k ≤ (S n).tau k := fun k => min_le_left _ _
  have hS0 : S 0 = SAOState.init K n := by simp [hS, saoState]
  -- the key claim
  have claim : ∀ k r, (r < T k ∨ r = 0) → k ∈ (S r).active ∧ (S r).tau0 = none := by
    intro k r hr
    rcases hr with hr | hr
    · -- r < T k ≤ τ₀ ≤ n
      have hτn : tau0 K n β adv I ≤ n := by
        unfold tau0
        rw [hF]
        cases hz : (S n).tau0 with
        | none => simp
        | some τ =>
          simp only
          have := (hinv n).2.1 τ hz
          have := htle n
          omega
      have hrn : r ≤ n := by have := hT0 k; omega
      obtain ⟨l', hl'⟩ := later K n β h r n hrn
      have hl'' : S n = l'.foldl (saoStep K β) (S r) := hl'
      constructor
      · by_contra hk
        obtain ⟨_, hk2⟩ := persist_fold K β k l' (S r) hk
        rw [← hl''] at hk2
        have h1 := ((hinv r).1 k hk).1
        have h2 := htle r
        have h3 := hTtau k
        omega
      · cases hz : (S r).tau0 with
        | none => rfl
        | some τ =>
          exfalso
          have hfr := frozen_fold K β τ l' (S r) hz
          rw [← hl''] at hfr
          have h1 := (hinv r).2.1 τ hz
          have h2 := htle r
          have h3 := hT0 k
          unfold tau0 at h3
          rw [hF, hfr, hz] at h3
          simp only at h3
          omega
    · subst hr
      rw [hS0]
      simp [SAOState.init]
  -- each term
  have hterm : ∀ i, qEff K n β adv I i ≤
      (1 : ℝ) / ((Finset.univ.filter (fun k => T i ≤ T k)).card : ℝ) := by
    intro i
    have hr : ∀ k, T i ≤ T k → (T i - 1 < T k ∨ T i - 1 = 0) := by
      intro k hk; omega
    obtain ⟨hiA, hnone⟩ := claim i (T i - 1) (hr i le_rfl)
    have hq : qEff K n β adv I i = (S (T i - 1)).p i := by
      show sao K n β ((history adv I).take (tauEff K n β adv I i - 1)) i = _
      have : (saoState K n β ((history adv I).take (tauEff K n β adv I i - 1))).tau0 = none :=
        hnone
      unfold sao
      rw [this]
    rw [hq]
    have hb := (inv_p_bounds _ (hinv _) i hiA).2
    refine hb.trans ?_
    have hsub : Finset.univ.filter (fun k => T i ≤ T k) ⊆ (S (T i - 1)).active := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact (claim k (T i - 1) (hr k hk)).1
    apply one_div_le_one_div_of_le
    · exact_mod_cast Finset.card_pos.mpr ⟨i, by simp⟩
    · exact_mod_cast Finset.card_le_card hsub
  calc ∑ i : Fin K, qEff K n β adv I i
      ≤ ∑ i : Fin K, (1 : ℝ) / ((Finset.univ.filter (fun k => T i ≤ T k)).card : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ ≤ (harmonic K : ℝ) := by
        have := harm_aux T K Finset.univ (by simp)
        exact this
    _ ≤ 1 + Real.log K := harmonic_le_one_add_log K


/-! ### Arithmetic helpers. -/

theorem le_of_sq' (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

theorem sqrt_le_of (Y b : ℝ) (hb : 0 ≤ b) (h : Y ≤ b ^ 2) : Real.sqrt Y ≤ b := by
  rw [show b = Real.sqrt (b ^ 2) from (Real.sqrt_sq hb).symm]
  exact Real.sqrt_le_sqrt h

theorem mul_sqrt_div (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a) :
    T * Real.sqrt (a / T) = Real.sqrt (a * T) := by
  have e : a * T = T ^ 2 * (a / T) := by field_simp
  rw [e, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT.le]

theorem sum_sqrt_sq_le {K : ℕ} (x : Fin K → ℝ) (hx : ∀ k, 0 ≤ x k) :
    (∑ k, Real.sqrt (x k)) ^ 2 ≤ K * ∑ k, x k := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun k => Real.sqrt (x k))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  have e : ∑ k, Real.sqrt (x k) ^ 2 = ∑ k, x k :=
    Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (hx k))
  rw [e] at h
  exact h

theorem fiber_sum {K n : ℕ} (I : Fin n → Fin K) (t : ℕ) (f : Fin n → ℝ) :
    ∑ k : Fin K, ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < t ∧ I r = k), f r =
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < t), f r := by
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun r : Fin n => (r : ℕ) < t))
    (t := (Finset.univ : Finset (Fin K))) (g := I) (fun _ _ => Finset.mem_univ _) f
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.filter_filter]

theorem card_lt (n m : ℕ) (hm : m ≤ n) :
    (Finset.univ.filter (fun r : Fin n => (r : ℕ) < m)).card = m := by
  have h : (Finset.univ.filter (fun r : Fin n => (r : ℕ) < m)).card = (Finset.range m).card := by
    apply Finset.card_bij (fun (r : Fin n) _ => (r : ℕ))
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simpa using hr
    · intro a _ b _ h
      exact Fin.ext h
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, by simp [hb], rfl⟩
  rw [h, Finset.card_range]

theorem sum_pull {K n : ℕ} (I : Fin n → Fin K) (m : ℕ) (hm : m ≤ n) :
    ∑ k : Fin K, (pullCount I k m : ℝ) = m := by
  have h := fiber_sum I m (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  unfold pullCount
  rw [h, card_lt n m hm]

theorem sum_split (n : ℕ) (f : Fin n → ℝ) (m τ : ℕ) (hmτ : m ≤ τ) (hτ : τ ≤ m + 1)
    (hf0 : ∀ r, 0 ≤ f r) (hf1 : ∀ r, f r ≤ 1) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)), f r ≤
      ∑ r, f r - ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < m), f r ∧
    ∑ r, f r - ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < m), f r ≤
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)), f r + 1 := by
  have e1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin n => (r : ℕ) < m) f
  have e2 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m)) (fun r : Fin n => τ ≤ (r : ℕ)) f
  rw [Finset.filter_filter, Finset.filter_filter] at e2
  have e3 : Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ τ ≤ (r : ℕ)) =
      Finset.univ.filter (fun r : Fin n => τ ≤ (r : ℕ)) := by
    apply Finset.filter_congr
    intro r _
    omega
  rw [e3] at e2
  have h0 : 0 ≤ ∑ r ∈ Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ)), f r :=
    Finset.sum_nonneg (fun r _ => hf0 r)
  have h1 : ∑ r ∈ Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ)), f r ≤ 1 := by
    have hc : (Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply Fin.ext
      omega
    calc ∑ r ∈ Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ)), f r
        ≤ ∑ r ∈ Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ)), (1 : ℝ) :=
          Finset.sum_le_sum (fun r _ => hf1 r)
      _ = (Finset.univ.filter (fun r : Fin n => ¬ (r : ℕ) < m ∧ ¬ τ ≤ (r : ℕ))).card := by simp
      _ ≤ 1 := by exact_mod_cast hc
  constructor <;> linarith

/-- the bound for an arm deactivated at round `v ≥ 2`. -/
theorem zbound (K n v t : ℕ) (L q : ℝ) (hK : 2 ≤ K) (hL3 : 3 ≤ L)
    (hLn : 2 * (1 + Real.log n) ≤ L) (hv : 2 ≤ v) (hvt : v ≤ t) (htn : t ≤ n)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pullBound q v t L * Real.sqrt (4 * K * L / ((v : ℝ) - 1) + 5 * (K * L / ((v : ℝ) - 1)) ^ 2) ≤
      3 * (1 + Real.log n) * q * Real.sqrt (n * K * L + 5 * K ^ 2 * L ^ 2) + 8 * K * L ^ 2 := by
  unfold pullBound
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hv2 : (2 : ℝ) ≤ v := by exact_mod_cast hv
  have hvt' : (v : ℝ) ≤ t := by exact_mod_cast hvt
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hL0 : 0 ≤ L := by linarith
  set d : ℝ := (v : ℝ) - 1 with hd
  have hd1 : 1 ≤ d := by rw [hd]; linarith
  have hd0 : 0 < d := by linarith
  have hKL : 0 ≤ (K : ℝ) * L := by positivity
  have hKL6 : 6 ≤ (K : ℝ) * L := by
    have := mul_le_mul hKr hL3 (by norm_num) (by positivity)
    linarith
  set X : ℝ := K * L / d with hX
  have hX0 : 0 ≤ X := by positivity
  have hXd : X * d = K * L := by rw [hX]; field_simp
  have hXle : X ≤ K * L := by rw [hX]; exact div_le_self hKL hd1
  have hvX : (v : ℝ) * X ≤ 2 * (K * L) := by
    have e : (v : ℝ) * X = X * d + X := by rw [hd]; ring
    rw [e, hXd]; linarith
  have hvX0 : 0 ≤ (v : ℝ) * X := by positivity
  have e4 : 4 * K * L / d = 4 * X := by rw [hX]; ring
  rw [e4]
  set w := Real.sqrt (4 * X + 5 * X ^ 2) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 4 * X + 5 * X ^ 2 := Real.sq_sqrt (by positivity)
  have htpos : (0 : ℝ) < t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlogtn : Real.log t ≤ Real.log n := Real.log_le_log htpos htn'
  set a := 1 + Real.log (t : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have haL : a ≤ L / 2 := by rw [ha]; linarith
  set S := Real.sqrt (n * K * L + 5 * K ^ 2 * L ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = n * K * L + 5 * K ^ 2 * L ^ 2 := Real.sq_sqrt (by positivity)
  -- part (i)
  have hvw : (v : ℝ) * w ≤ 3 * S := by
    apply le_of_sq' _ _ (by positivity)
    have h1 : ((v : ℝ) * w) ^ 2 = 4 * v * ((v : ℝ) * X) + 5 * ((v : ℝ) * X) ^ 2 := by
      rw [mul_pow, hw2]; ring
    have h2 : 4 * (v : ℝ) * ((v : ℝ) * X) ≤ 8 * (K * L) * n := by
      calc 4 * (v : ℝ) * ((v : ℝ) * X) ≤ 4 * v * (2 * (K * L)) :=
            mul_le_mul_of_nonneg_left hvX (by positivity)
        _ = 8 * (K * L) * v := by ring
        _ ≤ 8 * (K * L) * n := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : 5 * ((v : ℝ) * X) ^ 2 ≤ 20 * (K * L) ^ 2 := by
      have := mul_le_mul hvX hvX hvX0 (by positivity)
      linarith [this]
    have h4 : (0 : ℝ) ≤ n * K * L := by positivity
    have h5 : (0 : ℝ) ≤ (K * L) ^ 2 := sq_nonneg _
    rw [h1, show (3 * S) ^ 2 = 9 * S ^ 2 by ring, hS2]
    linarith [h2, h3, h4, h5]
  have hi : q * v * a * w ≤ 3 * (1 + Real.log n) * q * S := by
    have e : q * v * a * w = q * a * (v * w) := by ring
    rw [e]
    have hqa : 0 ≤ q * a := by positivity
    calc q * a * (v * w) ≤ q * a * (3 * S) := mul_le_mul_of_nonneg_left hvw hqa
      _ ≤ q * (1 + Real.log n) * (3 * S) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hq0
          linarith
      _ = 3 * (1 + Real.log n) * q * S := by ring
  -- part (ii)
  have hii : Real.sqrt (4 * q * v * a * L + 5 * L ^ 2) * w ≤ 8 * K * L ^ 2 := by
    apply le_of_sq' _ _ (by positivity)
    have hqa : q * a ≤ L / 2 := by
      calc q * a ≤ 1 * a := mul_le_mul_of_nonneg_right hq1 (by linarith)
        _ ≤ L / 2 := by linarith
    have hY : 4 * q * v * a * L + 5 * L ^ 2 ≤ (2 * v + 5) * L ^ 2 := by
      have h2 : 4 * q * v * a * L = 4 * v * L * (q * a) := by ring
      rw [h2]
      have h3 := mul_le_mul_of_nonneg_left hqa (by positivity : (0 : ℝ) ≤ 4 * v * L)
      have h4 : 4 * (v : ℝ) * L * (L / 2) = 2 * v * L ^ 2 := by ring
      linarith [h3, h4]
    have hY0 : 0 ≤ 4 * q * v * a * L + 5 * L ^ 2 := by positivity
    rw [mul_pow, Real.sq_sqrt hY0, hw2]
    have hP : (2 * (v : ℝ) + 5) * (4 * X + 5 * X ^ 2) ≤ 51 * (K * L) ^ 2 := by
      have e : (2 * (v : ℝ) + 5) * (4 * X + 5 * X ^ 2) =
          8 * ((v : ℝ) * X) + 10 * (((v : ℝ) * X) * X) + 20 * X + 25 * (X * X) := by ring
      rw [e]
      have h1 := mul_le_mul hvX hXle hX0 (by positivity)
      have h2 := mul_le_mul hXle hXle hX0 hKL
      have h3 := mul_le_mul_of_nonneg_right hKL6 hKL
      linarith [h1, h2, h3]
    have hW0 : 0 ≤ 4 * X + 5 * X ^ 2 := by positivity
    have hK4 : (0 : ℝ) ≤ (K : ℝ) ^ 2 * L ^ 4 := by positivity
    calc (4 * q * v * a * L + 5 * L ^ 2) * (4 * X + 5 * X ^ 2)
        ≤ ((2 * v + 5) * L ^ 2) * (4 * X + 5 * X ^ 2) := mul_le_mul_of_nonneg_right hY hW0
      _ = L ^ 2 * ((2 * v + 5) * (4 * X + 5 * X ^ 2)) := by ring
      _ ≤ L ^ 2 * (51 * (K * L) ^ 2) := mul_le_mul_of_nonneg_left hP (by positivity)
      _ ≤ (8 * K * L ^ 2) ^ 2 := by linarith [hK4]
  have e : (q * v * a + Real.sqrt (4 * q * v * a * L + 5 * L ^ 2)) * w =
      q * v * a * w + Real.sqrt (4 * q * v * a * L + 5 * L ^ 2) * w := by ring
  rw [e]
  linarith

/-- the bound for an arm deactivated at round `1`. -/
theorem pbound1 (n t : ℕ) (L q : ℝ) (hL3 : 3 ≤ L) (hLn : 2 * (1 + Real.log n) ≤ L)
    (ht : 1 ≤ t) (htn : t ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    pullBound q 1 t L ≤ 4 * L := by
  unfold pullBound
  simp only [Nat.cast_one, mul_one]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht)
  have hlogtn : Real.log t ≤ Real.log n := Real.log_le_log htpos htn'
  have h1 : q * (1 + Real.log t) ≤ L / 2 := by
    calc q * (1 + Real.log t) ≤ 1 * (1 + Real.log t) :=
          mul_le_mul_of_nonneg_right hq1 (by linarith)
      _ ≤ L / 2 := by linarith
  have h2 : Real.sqrt (4 * q * (1 + Real.log t) * L + 5 * L ^ 2) ≤ 3 * L := by
    apply sqrt_le_of _ _ (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * L)
    nlinarith [h3]
  linarith

/-- `t · width(t) ≤ 2 S`. -/
theorem twidth (K n t : ℕ) (β : ℝ) (hL : 0 ≤ Real.log β) (ht : 1 ≤ t) (htn : t ≤ n) :
    (t : ℝ) * width K β t ≤
      2 * Real.sqrt (n * K * Real.log β + 5 * K ^ 2 * Real.log β ^ 2) := by
  unfold width
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have htn' : (t : ℝ) ≤ n := by exact_mod_cast htn
  apply le_of_sq' _ _ (by positivity)
  have hX0 : 0 ≤ 4 * K * Real.log β / t + 5 * (K * Real.log β / t) ^ 2 := by positivity
  rw [mul_pow, mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt (by positivity)]
  have e : (t : ℝ) ^ 2 * (4 * K * Real.log β / t + 5 * (K * Real.log β / t) ^ 2) =
      4 * K * Real.log β * t + 5 * K ^ 2 * Real.log β ^ 2 := by
    field_simp
  rw [e]
  have : (0 : ℝ) ≤ 4 * K * Real.log β := by positivity
  nlinarith


theorem log_beta_bounds (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 < 10 * (K : ℝ) * (n : ℝ) ^ 3 / δ ∧
    3 ≤ Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ∧
    2 * (1 + Real.log n) ≤ Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) := by
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hK hKn)
  have hn2sq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hn3 : (8 : ℝ) * n ^ 2 ≤ 10 * K * n ^ 3 := by
    have h1 : (10 : ℝ) * K * n ^ 3 = (10 * K * n) * n ^ 2 := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_right _ hn2sq
    nlinarith
  have hdiv : 10 * (K : ℝ) * n ^ 3 ≤ 10 * K * n ^ 3 / δ := by
    rw [le_div_iff₀ hδ0]
    have : 0 ≤ 10 * (K : ℝ) * n ^ 3 := by positivity
    nlinarith
  have he : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hβ : Real.exp 2 * (n : ℝ) ^ 2 ≤ 10 * K * n ^ 3 / δ := by
    have := mul_le_mul_of_nonneg_right he hn2sq
    linarith
  have hpos : 0 < Real.exp 2 * (n : ℝ) ^ 2 := by positivity
  have hL : 2 * (1 + Real.log n) ≤ Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) := by
    have := Real.log_le_log hpos hβ
    rw [Real.log_mul (Real.exp_pos 2).ne' (by positivity), Real.log_exp, Real.log_pow] at this
    push_cast at this
    linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  refine ⟨?_, by linarith, hL⟩
  have : (1 : ℝ) < 10 * K * n ^ 3 := by nlinarith
  linarith

/-! ### The main argument. -/

set_option maxHeartbeats 4000000 in
theorem main (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (hL3 : 3 ≤ Real.log β) (hLn : 2 * (1 + Real.log n) ≤ Real.log β)
    (adv : Adversary K) (hadv : adv.IsBounded) (I : Fin n → Fin K)
    (h22 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β adv I),
      |estAvg (sao K n β) adv I i t - fixedAvg adv I i t| ≤
        estRadius K (tauEff K n β adv I i) (qEff K n β adv I i) t (Real.log β))
    (h24 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β adv I),
      (pullCount I i t : ℝ) ≤
        pullBound (qEff K n β adv I i) (tauEff K n β adv I i) t (Real.log β))
    (h25 : regretFrom adv I (tau0 K n β adv I) ≤
      5.15 * Real.sqrt (((n : ℝ) - tau0 K n β adv I) * K * Real.log β)) :
    regret adv I ≤
      60 * (1 + Real.log K) * (1 + Real.log n) *
          Real.sqrt (n * K * Real.log β + 5 * K ^ 2 * Real.log β ^ 2) +
        200 * K ^ 2 * Real.log β ^ 2 := by
  classical
  have hK0 : 0 < K := by omega
  have hL0 : 0 ≤ Real.log β := by linarith
  haveI : Nonempty (Fin K) := ⟨⟨0, hK0⟩⟩
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans hK hKn)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hrew : ∀ r i, 0 ≤ reward adv I r i ∧ reward adv I r i ≤ 1 :=
    fun r i => ⟨(hadv _ i).1, (hadv _ i).2⟩
  set R0 := Real.sqrt ((n : ℝ) * K * Real.log β + 5 * K ^ 2 * Real.log β ^ 2) with hR0
  have hR0nn : 0 ≤ R0 := Real.sqrt_nonneg _
  have hR0sq : R0 ^ 2 = (n : ℝ) * K * Real.log β + 5 * K ^ 2 * Real.log β ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hΛ0 : 0 ≤ (1 + Real.log K) * (1 + Real.log n) * R0 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hR0nn
  have hKL2 : (36 : ℝ) ≤ (K : ℝ) ^ 2 * Real.log β ^ 2 := by
    have h1 := mul_le_mul hKr hL3 (by norm_num) (by positivity)
    have h2 := mul_le_mul h1 h1 (by norm_num) (by positivity)
    nlinarith [h2]
  set B := 18 * R0 + 36 * ((1 + Real.log K) * (1 + Real.log n) * R0) +
    96 * (K : ℝ) ^ 2 * Real.log β ^ 2 with hB
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  -- the states
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
  have hneS : ∀ u, (S u).active.Nonempty :=
    fun u => ne_fold K β _ (SAOState.init K n) ⟨⟨0, hK0⟩, Finset.mem_univ _⟩
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
  -- the last round without a firing test
  obtain ⟨m, hmn, hlt, hτm, hτn⟩ : ∃ m, m ≤ n ∧ (∀ v ≤ m, (S v).tau0 = none) ∧
      (tau0 K n β adv I = m ∨ tau0 K n β adv I = m + 1) ∧ tau0 K n β adv I ≤ n := by
    by_cases hfin : (S n).tau0 = none
    · have e : tau0 K n β adv I = n := by rw [htau0def, hfin]
      exact ⟨n, le_rfl, fun v hv => hback n v hv hfin, Or.inl e, e.le⟩
    · have hex : ∃ u, (S u).tau0 ≠ none := ⟨n, hfin⟩
      have h1 := Nat.find_spec hex
      have h2 : Nat.find hex ≤ n := Nat.find_min' hex hfin
      have h3 : ∀ v < Nat.find hex, (S v).tau0 = none := fun v hv => by
        have := Nat.find_min hex hv; simpa using this
      have h0 : Nat.find hex ≠ 0 := by
        intro e; rw [e, hS0] at h1; exact h1 rfl
      obtain ⟨m, hm1⟩ : ∃ m, m + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
      rw [← hm1] at h1 h2 h3
      have hmn' : m < n := by omega
      have hlt : ∀ v ≤ m, (S v).tau0 = none := fun v hv => h3 v (by omega)
      obtain ⟨r, -, -, -, -, -, hz, -⟩ := step_spec K β (S m)
        (I ⟨m, hmn'⟩, reward adv I ⟨m, hmn'⟩ (I ⟨m, hmn'⟩)) (hlt m le_rfl)
      rw [← hstep m hmn', (htr m hmn'.le (hlt m le_rfl)).1] at hz
      have hm2 : (S (m + 1)).tau0 = some (m + 1) := by
        rcases hz with hz | hz
        · exact absurd hz h1
        · exact hz
      have hSn : S n = S (m + 1) := by
        obtain ⟨l, hl⟩ := hlater (m + 1) n h2
        rw [hl]; exact frozen_fold K β (m + 1) l _ hm2
      have e : tau0 K n β adv I = m + 1 := by rw [htau0def, hSn, hm2]
      exact ⟨m, hmn'.le, hlt, Or.inr e, by omega⟩
  have hmτ : m ≤ tau0 K n β adv I := by rcases hτm with h | h <;> omega
  have hτm1 : tau0 K n β adv I ≤ m + 1 := by rcases hτm with h | h <;> omega
  have htE : ∀ k, tauEff K n β adv I k = min ((S n).tau k) (tau0 K n β adv I) := fun k => rfl
  -- deactivation rounds
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
  have hactE : ∀ k, k ∈ (S m).active → m ≤ tauEff K n β adv I k := by
    intro k hk
    rw [htE]
    apply le_min _ hmτ
    by_cases hkn : k ∈ (S n).active
    · rw [(hinv n).2.2 k hkn]; exact hmn
    · obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k n le_rfl hkn
      rw [(hpost n hvw).2.1]
      by_contra hc
      exact (hpost m (by omega)).1 hk
  have hinE : ∀ k, k ∉ (S m).active → ∃ v, 1 ≤ v ∧ v ≤ m ∧ (S m).tau k = v ∧
      tauEff K n β adv I k = v ∧ qEff K n β adv I k = (S m).q k ∧
      1 / (K : ℝ) ≤ qEff K n β adv I k ∧ qEff K n β adv I k ≤ 1 := by
    intro k hk
    obtain ⟨v, hv1, hvw, hmin, hpost⟩ := hdr k m hmn hk
    have hFv : (S m).tau k = v := (hpost m hvw).2.1
    have hEv : tauEff K n β adv I k = v := by
      rw [htE, (hpost n (by omega)).2.1]; omega
    have hp : probAt (sao K n β) adv I v = (S (v - 1)).p := by
      unfold probAt; exact sao_eq K n β _ (hlt (v - 1) (by omega))
    have hq : qEff K n β adv I k = (S (v - 1)).p k := by
      show probAt (sao K n β) adv I (tauEff K n β adv I k) k = _
      rw [hEv, hp]
    have hkv : k ∈ (S (v - 1)).active := hmin (v - 1) (by omega)
    refine ⟨v, hv1, hvw, hFv, hEv, by rw [hq, (hpost m hvw).2.2], ?_, ?_⟩
    · rw [hq]; exact active_p_ge K n hK0 _ (hinv _).1 (hinv _).2 k hkv
    · rw [hq]
      have hb := (inv_p_bounds _ (hinv _).1 k hkv).2
      have hc : (1 : ℝ) ≤ ((S (v - 1)).active.card : ℝ) := by
        exact_mod_cast Finset.card_pos.2 ⟨k, hkv⟩
      calc _ ≤ 1 / ((S (v - 1)).active.card : ℝ) := hb
        _ ≤ 1 := by rw [div_le_one (by linarith)]; exact hc
  have hq0 : ∀ k, k ∈ (S m).active → 0 ≤ qEff K n β adv I k := by
    intro k hk
    have he1 : m ≤ tauEff K n β adv I k := hactE k hk
    have he2 : tauEff K n β adv I k ≤ m + 1 := by
      rw [htE]; exact (min_le_right _ _).trans hτm1
    have hp : probAt (sao K n β) adv I (tauEff K n β adv I k) =
        (S (tauEff K n β adv I k - 1)).p := by
      unfold probAt; exact sao_eq K n β _ (hlt _ (by omega))
    have hke : k ∈ (S (tauEff K n β adv I k - 1)).active := by
      by_contra hc
      obtain ⟨l, hl⟩ := hlater (tauEff K n β adv I k - 1) m (by omega)
      have := (persist_fold K β k l _ hc).1
      rw [← hl] at this
      exact this hk
    show 0 ≤ probAt (sao K n β) adv I (tauEff K n β adv I k) k
    rw [hp]
    exact (inv_p_bounds _ (hinv _).1 k hke).1
  have hsumq := sumq K n hK hKn β hβ adv hadv I
  -- the rounds `1, …, m`
  have hfirst : ∀ j, cumReward adv I j m -
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < m), reward adv I r (I r) ≤ B := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · intro j
      subst hm0
      have e1 : cumReward adv I j 0 = 0 := by
        unfold cumReward; apply Finset.sum_eq_zero; intro r hr; simp at hr
      have e2 : ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < 0),
          reward adv I r (I r) = 0 := by
        apply Finset.sum_eq_zero; intro r hr; simp at hr
      rw [e1, e2]; linarith
    obtain ⟨u, rfl⟩ : ∃ u, m = u + 1 := ⟨m - 1, by omega⟩
    have hun : u < n := by omega
    have hso : S (u + 1) = saoStep K β (S u) (I ⟨u, hun⟩, reward adv I ⟨u, hun⟩ (I ⟨u, hun⟩)) :=
      hstep u hun
    set o : Fin K × ℝ := (I ⟨u, hun⟩, reward adv I ⟨u, hun⟩ (I ⟨u, hun⟩)) with ho
    have hnu : (S u).tau0 = none := hlt u (by omega)
    have htu : (S u).t = u := (htr u (by omega) hnu).1
    have htr1 := htr (u + 1) hmn (hlt (u + 1) le_rfl)
    obtain ⟨hA1, hT1, hQ1, hz1, -, -, -, -⟩ := step_fold K β (S u) o hnu
    rw [← hso] at hA1 hT1 hQ1 hz1
    have hflag : (rnd K β (S u) o).2.2.2 = false := by
      cases hb : (rnd K β (S u) o).2.2.2 with
      | false => rfl
      | true =>
        exfalso
        have h := hlt (u + 1) le_rfl
        rw [hz1, hb] at h
        simp at h
    have hne : (S u).active.Nonempty := hneS u
    have hHtf : HtF K β (S u) o = fun i => estAvg (sao K n β) adv I i (u + 1) := by
      funext i
      unfold HtF
      rw [← hso, htu, (htr1.2 i).1]
      rfl
    have hHhf : HhF K β (S u) o = fun i => algAvg adv I i (u + 1) := by
      funext i
      unfold HhF
      rw [← hso, (htr1.2 i).2.1, (htr1.2 i).2.2]
      rfl
    have hTTf : (saoStep K β (S u) o).T = fun i => pullCount I i (u + 1) := by
      funext i
      rw [← hso, (htr1.2 i).2.2]
    obtain ⟨hrne, hM⟩ := rnd_max K β (S u) o hne
    rw [← hA1, hHtf] at hM
    rw [← hA1] at hrne
    set M := maxOver (S u).active (fun i => estAvg (sao K n β) adv I i (u + 1)) with hMdef
    have hGood := rnd_good K β (S u) o
    rw [htu] at hGood
    have hτq : ∀ k (s' : St K), Good (u + 1) (S u).p (S u).active (S u).tau (S u).q s' →
        (k ∈ s'.1 ↔ k ∈ (rnd K β (S u) o).1) →
        s'.2.1 k = (S (u + 1)).tau k ∧ s'.2.2.1 k = (S (u + 1)).q k := by
      intro k s' hg hiff
      rw [hT1, hQ1]
      by_cases hk0 : k ∈ (S u).active
      · by_cases hks : k ∈ s'.1
        · have hkr := hiff.1 hks
          rw [((hg.2 k).2 (Or.inl hks)).1, ((hg.2 k).2 (Or.inl hks)).2,
            ((hGood.2 k).2 (Or.inl hkr)).1, ((hGood.2 k).2 (Or.inl hkr)).2]
          exact ⟨rfl, rfl⟩
        · have hkr : k ∉ (rnd K β (S u) o).1 := fun h => hks (hiff.2 h)
          rw [((hg.2 k).1 hk0 hks).1, ((hg.2 k).1 hk0 hks).2,
            ((hGood.2 k).1 hk0 hkr).1, ((hGood.2 k).1 hk0 hkr).2]
          exact ⟨rfl, rfl⟩
      · rw [((hg.2 k).2 (Or.inr hk0)).1, ((hg.2 k).2 (Or.inr hk0)).2,
          ((hGood.2 k).2 (Or.inr hk0)).1, ((hGood.2 k).2 (Or.inr hk0)).2]
        exact ⟨rfl, rfl⟩
    have hnf : ∀ k, ∃ s' : St K, Good (u + 1) (S u).p (S u).active (S u).tau (S u).q s' ∧
        (k ∈ s'.1 ↔ k ∈ (S (u + 1)).active) ∧
        maxOver s'.1 (fun i => estAvg (sao K n β) adv I i (u + 1)) = M ∧
        ¬ fire K β (u + 1) (fun i => estAvg (sao K n β) adv I i (u + 1))
          (fun i => algAvg adv I i (u + 1)) (fun i => pullCount I i (u + 1)) s' k ∧
        s'.2.1 k = (S (u + 1)).tau k ∧ s'.2.2.1 k = (S (u + 1)).q k := by
      intro k
      obtain ⟨s', hg, -, hiff, -, hmx, hnf⟩ := rnd_nofire K β (S u) o hflag hne k
      rw [htu] at hg hnf
      rw [hHtf] at hmx hnf
      rw [hHhf, hTTf] at hnf
      obtain ⟨e1, e2⟩ := hτq k s' hg hiff
      rw [← hA1] at hiff
      exact ⟨s', hg, hiff, hmx, hnf, e1, e2⟩
    have hW : ∀ k, k ∈ (S (u + 1)).active →
        M - estAvg (sao K n β) adv I k (u + 1) ≤ 6 * width K β ((u + 1 : ℕ) : ℝ) := by
      intro k hk
      obtain ⟨j, hj, e⟩ := maxOver_mem (S (u + 1)).active
        (fun i => estAvg (sao K n β) adv I i (u + 1)) hrne
      have hkr : k ∈ (rnd K β (S u) o).1 := by rw [← hA1]; exact hk
      have hjr : j ∈ (rnd K β (S u) o).1 := by rw [← hA1]; exact hj
      have hk0 : k ∈ (S u).active := hGood.1 hkr
      have h := rnd_keep K β (S u) o k j hk0 hkr hjr
      rw [hHtf, htu] at h
      rw [← hM, e]
      exact h
    have hW0 := width_nonneg K β ((u + 1 : ℕ) : ℝ)
    have hj22 : ∀ j, fixedAvg adv I j (u + 1) ≤ M + width K β ((u + 1 : ℕ) : ℝ) := by
      intro j
      have hb := h22 j (u + 1) (Finset.mem_Icc.2 ⟨by omega, hmτ⟩)
      rw [abs_le] at hb
      by_cases hj : j ∈ (S (u + 1)).active
      · rw [rad_eq K β _ _ (u + 1) (by omega) (hactE j hj)] at hb
        have h1 : estAvg (sao K n β) adv I j (u + 1) ≤ M := by
          rw [← hM]; exact le_maxOver _ (fun i => estAvg (sao K n β) adv I i (u + 1)) j hj
        linarith [hb.1]
      · obtain ⟨v, hv1, hvm, hFv, hEv, hqE, hqK, hq1⟩ := hinE j hj
        have hR := rad_le K hK0 β hL0 v (qEff K n β adv I j) (u + 1) hv1 hvm hqK
        rw [hEv] at hb
        obtain ⟨s', hg, hiff, hmx, hnfj, e1, e2⟩ := hnf j
        simp only [fire, not_or] at hnfj
        obtain ⟨-, -, nC⟩ := hnfj
        have hjs : j ∉ s'.1 := fun h => hj (hiff.1 h)
        rw [e1, hFv, hmx] at nC
        have hC : 2 * width K β v < M - estAvg (sao K n β) adv I j (u + 1) := by
          by_contra hc; exact nC ⟨hjs, not_lt.1 hc⟩
        have hwv := width_nonneg K β v
        linarith [hb.1]
    have hfix1 : ∀ j, fixedAvg adv I j (u + 1) ≤ 1 := by
      intro j
      unfold fixedAvg cumReward
      have hpos : (0 : ℝ) < ((u + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_one hpos]
      calc ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u + 1), reward adv I r j
          ≤ ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u + 1), (1 : ℝ) :=
            Finset.sum_le_sum (fun r _ => (hrew r j).2)
        _ = ((u + 1 : ℕ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_lt n (u + 1) hmn]
    -- the per-arm bound
    have hck : ∀ j k, (pullCount I k (u + 1) : ℝ) * fixedAvg adv I j (u + 1) -
        algReward adv I k (u + 1) ≤
        8 * width K β ((u + 1 : ℕ) : ℝ) * (pullCount I k (u + 1) : ℝ) +
          Real.sqrt (2 * Real.log β * (pullCount I k (u + 1) : ℝ)) +
          (36 * (1 + Real.log n) * R0 * qEff K n β adv I k + 96 * K * Real.log β ^ 2) := by
      intro j k
      have hqk0 : 0 ≤ qEff K n β adv I k := by
        by_cases hk : k ∈ (S (u + 1)).active
        · exact hq0 k hk
        · obtain ⟨v, -, -, -, -, -, hqK, -⟩ := hinE k hk
          have : (0 : ℝ) < 1 / K := by positivity
          linarith
      have hrest0 : 0 ≤ (1 + Real.log n) * R0 * qEff K n β adv I k :=
        mul_nonneg (mul_nonneg (by linarith) hR0nn) hqk0
      have hKL0 : 0 ≤ (K : ℝ) * Real.log β ^ 2 := by positivity
      have hsq0 := Real.sqrt_nonneg (2 * Real.log β * (pullCount I k (u + 1) : ℝ))
      have hG0 : 0 ≤ algReward adv I k (u + 1) := Finset.sum_nonneg (fun r _ => (hrew r k).1)
      have hHj := hj22 j
      have hHj1 := hfix1 j
      rcases Nat.eq_zero_or_pos (pullCount I k (u + 1)) with h0 | hpos
      · have hG : algReward adv I k (u + 1) = 0 := by
          unfold pullCount at h0
          unfold algReward
          rw [Finset.card_eq_zero.1 h0]
          simp
        rw [hG, h0]
        simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, Real.sqrt_zero, zero_add]
        linarith [hrest0, hKL0]
      have hT1' : (1 : ℝ) ≤ (pullCount I k (u + 1) : ℝ) := by exact_mod_cast hpos
      have hT0 : (0 : ℝ) < (pullCount I k (u + 1) : ℝ) := by linarith
      have hTne : (pullCount I k (u + 1) : ℝ) ≠ 0 := hT0.ne'
      have hGk : algReward adv I k (u + 1) =
          (pullCount I k (u + 1) : ℝ) * algAvg adv I k (u + 1) := by
        unfold algAvg; field_simp
      have hTs : (pullCount I k (u + 1) : ℝ) *
          Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ)) =
          Real.sqrt (2 * Real.log β * (pullCount I k (u + 1) : ℝ)) :=
        mul_sqrt_div _ (2 * Real.log β) hT0 (by linarith)
      have hs0 := Real.sqrt_nonneg (2 * Real.log β / (pullCount I k (u + 1) : ℝ))
      obtain ⟨s', hg, hiff, hmx, hnfk, e1, e2⟩ := hnf k
      simp only [fire, not_or] at hnfk
      obtain ⟨nA, nB, nC⟩ := hnfk
      rw [e1, e2] at nA
      rw [e1, hmx] at nB nC
      rw [hGk]
      by_cases hk : k ∈ (S (u + 1)).active
      · have hτn : (S (u + 1)).tau k = n := (hinv (u + 1)).2.2 k hk
        rw [hτn, Nat.min_eq_right hmn, rad_eq' K β _ _ (u + 1) (by omega)] at nA
        have hA : |estAvg (sao K n β) adv I k (u + 1) - algAvg adv I k (u + 1)| ≤
            Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ)) +
              width K β ((u + 1 : ℕ) : ℝ) := by
          by_contra hc; exact nA ⟨hpos, not_le.1 hc⟩
        rw [abs_le] at hA
        have hWk := hW k hk
        have hd : fixedAvg adv I j (u + 1) - algAvg adv I k (u + 1) ≤
            8 * width K β ((u + 1 : ℕ) : ℝ) +
              Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ)) := by
          linarith [hA.2]
        have hm := mul_le_mul_of_nonneg_left hd hT0.le
        have e : (pullCount I k (u + 1) : ℝ) * (8 * width K β ((u + 1 : ℕ) : ℝ) +
            Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ))) =
            8 * width K β ((u + 1 : ℕ) : ℝ) * (pullCount I k (u + 1) : ℝ) +
              Real.sqrt (2 * Real.log β * (pullCount I k (u + 1) : ℝ)) := by
          rw [mul_add, hTs]; ring
        rw [e] at hm
        linarith [hm, hrest0, hKL0]
      · obtain ⟨v, hv1, hvm, hFv, hEv, hqE, hqK, hq1⟩ := hinE k hk
        have hks : k ∉ s'.1 := fun h => hk (hiff.1 h)
        have hTP : (pullCount I k (u + 1) : ℝ) ≤
            pullBound (qEff K n β adv I k) v (u + 1) (Real.log β) := by
          have := h24 k (u + 1) (Finset.mem_Icc.2 ⟨by omega, hmτ⟩)
          rwa [hEv] at this
        have hW8 : 0 ≤ 8 * width K β ((u + 1 : ℕ) : ℝ) * (pullCount I k (u + 1) : ℝ) :=
          mul_nonneg (by linarith) hT0.le
        by_cases hv2 : 2 ≤ v
        · rw [hFv] at nA nB
          rw [← hqE] at nA
          have hBk : M - estAvg (sao K n β) adv I k (u + 1) ≤
              10 * width K β ((v : ℝ) - 1) := by
            by_contra hc; exact nB ⟨hks, hv2, not_le.1 hc⟩
          have hR := rad_le K hK0 β hL0 v (qEff K n β adv I k) (u + 1) hv1 hvm hqK
          unfold estRadius at hR
          have hvle : (v : ℝ) ≤ ((u + 1 : ℕ) : ℝ) := by exact_mod_cast hvm
          have hmax0 : max (((u + 1 : ℕ) : ℝ) - (v : ℝ)) 0 = ((u + 1 : ℕ) : ℝ) - (v : ℝ) :=
            max_eq_left (by linarith)
          rw [Nat.min_eq_left hvm] at hR nA
          rw [hmax0] at hR
          have hA : |estAvg (sao K n β) adv I k (u + 1) - algAvg adv I k (u + 1)| ≤
              Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ)) + width K β v := by
            by_contra hc
            have hc' := not_le.1 hc
            exact nA ⟨hpos, by linarith⟩
          rw [abs_le] at hA
          have hvpos : (0 : ℝ) < v := by exact_mod_cast hv1
          have hv2r : (2 : ℝ) ≤ v := by exact_mod_cast hv2
          have hw1 := width_anti K β hL0 (v : ℝ) ((u + 1 : ℕ) : ℝ) hvpos hvle
          have hw2 := width_anti K β hL0 ((v : ℝ) - 1) (v : ℝ) (by linarith) (by linarith)
          have hwn := width_nonneg K β ((v : ℝ) - 1)
          have hd : fixedAvg adv I j (u + 1) - algAvg adv I k (u + 1) ≤
              12 * width K β ((v : ℝ) - 1) +
                Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ)) := by
            linarith [hA.2]
          have hm := mul_le_mul_of_nonneg_left hd hT0.le
          have e : (pullCount I k (u + 1) : ℝ) * (12 * width K β ((v : ℝ) - 1) +
              Real.sqrt (2 * Real.log β / (pullCount I k (u + 1) : ℝ))) =
              12 * ((pullCount I k (u + 1) : ℝ) * width K β ((v : ℝ) - 1)) +
                Real.sqrt (2 * Real.log β * (pullCount I k (u + 1) : ℝ)) := by
            rw [mul_add, hTs]; ring
          rw [e] at hm
          have hPw := mul_le_mul_of_nonneg_right hTP hwn
          have hz : pullBound (qEff K n β adv I k) v (u + 1) (Real.log β) *
              width K β ((v : ℝ) - 1) ≤
              3 * (1 + Real.log n) * qEff K n β adv I k * R0 + 8 * K * Real.log β ^ 2 := by
            have := zbound K n v (u + 1) (Real.log β) (qEff K n β adv I k) hK hL3 hLn hv2 hvm
              hmn hqk0 hq1
            rw [← hR0] at this
            exact this
          linarith [hm, hPw, hz, hW8, hrest0, hKL0]
        · obtain rfl : v = 1 := by omega
          have hP1 := pbound1 n (u + 1) (Real.log β) (qEff K n β adv I k) hL3 hLn (by omega)
            hmn hqk0 hq1
          have hTH : (pullCount I k (u + 1) : ℝ) * fixedAvg adv I j (u + 1) ≤
              (pullCount I k (u + 1) : ℝ) := mul_le_of_le_one_right hT0.le hHj1
          have hAa : 0 ≤ (pullCount I k (u + 1) : ℝ) * algAvg adv I k (u + 1) := by
            rw [← hGk]; exact hG0
          have h4L : 4 * Real.log β ≤ 96 * K * Real.log β ^ 2 := by
            have := mul_le_mul hKr hL3 (by norm_num) (by positivity)
            have h6 := mul_le_mul_of_nonneg_right this hL0
            have h7 : (K : ℝ) * Real.log β * Real.log β = K * Real.log β ^ 2 := by ring
            linarith [h6, h7]
          linarith [hTP, hP1, hTH, hAa, h4L, hW8, hrest0, hsq0]
    -- summing over the arms
    intro j
    have hsumT := sum_pull I (u + 1) hmn
    have hu0 : ((u + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hcum : cumReward adv I j (u + 1) = ((u + 1 : ℕ) : ℝ) * fixedAvg adv I j (u + 1) := by
      unfold fixedAvg; field_simp
    have hG : ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u + 1), reward adv I r (I r) =
        ∑ k : Fin K, algReward adv I k (u + 1) := by
      rw [← fiber_sum I (u + 1) (fun r => reward adv I r (I r))]
      apply Finset.sum_congr rfl
      intro k _
      unfold algReward
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      show reward adv I r (I r) = reward adv I r k
      rw [hr.2]
    have hdec : cumReward adv I j (u + 1) -
        ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < u + 1), reward adv I r (I r) =
        ∑ k : Fin K, ((pullCount I k (u + 1) : ℝ) * fixedAvg adv I j (u + 1) -
          algReward adv I k (u + 1)) := by
      rw [hcum, hG, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumT]
    rw [hdec]
    have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin K))) => hck j k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    have e1 : ∑ k : Fin K, 8 * width K β ((u + 1 : ℕ) : ℝ) * (pullCount I k (u + 1) : ℝ) =
        8 * width K β ((u + 1 : ℕ) : ℝ) * ((u + 1 : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, hsumT]
    have e3 : ∑ k : Fin K, 36 * (1 + Real.log n) * R0 * qEff K n β adv I k =
        36 * (1 + Real.log n) * R0 * ∑ k : Fin K, qEff K n β adv I k := by
      rw [← Finset.mul_sum]
    have e4 : ∑ _k : Fin K, (96 * K * Real.log β ^ 2 : ℝ) = K * (96 * K * Real.log β ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [e1, e3, e4] at hs
    have htw := twidth K n (u + 1) β hL0 (by omega) hmn
    rw [← hR0] at htw
    have hcs := sum_sqrt_sq_le (fun k => 2 * Real.log β * (pullCount I k (u + 1) : ℝ))
      (fun k => by positivity)
    have e5 : ∑ k : Fin K, 2 * Real.log β * (pullCount I k (u + 1) : ℝ) =
        2 * Real.log β * ((u + 1 : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, hsumT]
    rw [e5] at hcs
    have hsq : ∑ k : Fin K, Real.sqrt (2 * Real.log β * (pullCount I k (u + 1) : ℝ)) ≤ 2 * R0 := by
      apply le_of_sq' _ _ (by positivity)
      have hu : ((u + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hmn
      have h1 : (K : ℝ) * (2 * Real.log β * ((u + 1 : ℕ) : ℝ)) ≤ 2 * (n * K * Real.log β) := by
        have : (0 : ℝ) ≤ 2 * K * Real.log β := by positivity
        have := mul_le_mul_of_nonneg_left hu this
        linarith
      have h2 : (0 : ℝ) ≤ K ^ 2 * Real.log β ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ n * K * Real.log β := by positivity
      rw [show (2 * R0) ^ 2 = 4 * R0 ^ 2 by ring, hR0sq]
      linarith [hcs, h1, h2, h3]
    have hq36 := mul_le_mul_of_nonneg_left hsumq
      (by positivity : (0 : ℝ) ≤ 36 * (1 + Real.log n) * R0)
    have hW8 : 8 * width K β ((u + 1 : ℕ) : ℝ) * ((u + 1 : ℕ) : ℝ) ≤ 16 * R0 := by
      linarith [htw]
    rw [hB]
    linarith [hs, hsq, hq36, hW8]
  -- assembling
  have hsup : (⨆ i : Fin K, ∑ r : Fin n, reward adv I r i) ≤
      B + ∑ r ∈ Finset.univ.filter (fun r : Fin n => (r : ℕ) < m), reward adv I r (I r) + 1 +
        (⨆ i : Fin K, ∑ r ∈ Finset.univ.filter (fun r : Fin n => tau0 K n β adv I ≤ (r : ℕ)),
          reward adv I r i) := by
    apply ciSup_le
    intro i
    have h1 := (sum_split n (fun r => reward adv I r i) m _ hmτ hτm1 (fun r => (hrew r i).1)
      (fun r => (hrew r i).2)).2
    have h2 := hfirst i
    have h3 := le_ciSup (Finite.bddAbove_range (fun i : Fin K =>
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => tau0 K n β adv I ≤ (r : ℕ)), reward adv I r i)) i
    unfold cumReward at h2
    try simp only at h1 h3
    linarith
  have hlow := (sum_split n (fun r => reward adv I r (I r)) m _ hmτ hτm1
    (fun r => (hrew r _).1) (fun r => (hrew r _).2)).1
  try simp only at hlow
  have h25' := h25
  unfold regretFrom at h25'
  have htail : Real.sqrt (((n : ℝ) - tau0 K n β adv I) * K * Real.log β) ≤ R0 := by
    rw [hR0]
    apply Real.sqrt_le_sqrt
    have h0 : (0 : ℝ) ≤ (tau0 K n β adv I : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ K * Real.log β := by positivity
    have h2 : (0 : ℝ) ≤ K ^ 2 * Real.log β ^ 2 := by positivity
    have h3 := mul_nonneg h0 h1
    linarith
  have hprod : 1 ≤ (1 + Real.log K) * (1 + Real.log n) := by
    linarith [mul_nonneg hlogK hlogn]
  have hΛ : R0 ≤ (1 + Real.log K) * (1 + Real.log n) * R0 := by
    have := mul_le_mul_of_nonneg_right hprod hR0nn
    linarith
  unfold regret
  rw [hB] at hsup
  linarith [hsup, hlow, h25', htail, hΛ, hKL2]

end P8092e862

open MeasureTheory BestBothWorlds.SAO in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (adv : Adversary K) (hadv : adv.IsBounded)
    (I : Fin n → Fin K)
    (h22 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
      |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) adv I i t - fixedAvg adv I i t| ≤
        estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h24 : ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I),
      (pullCount I i t : ℝ) ≤
        pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)))
    (h25 : regretFrom adv I (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) ≤
      5.15 * Real.sqrt (((n : ℝ) - tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) adv I) * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) :
    regret adv I ≤
      60 * (1 + Real.log K) * (1 + Real.log n) *
          Real.sqrt (n * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) + 5 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2) +
        200 * K ^ 2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 := by
  obtain ⟨hβ, hL3, hLn⟩ := P8092e862.log_beta_bounds K n hK hKn δ hδ0 hδ1
  exact P8092e862.main K n hK hKn _ hβ hL3 hLn adv hadv I h22 h24 h25
