-- Prove2me | solution 1 for BestBothWorlds.SAO.sao_stochastic_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:21:41.735+00:00
-- url     : https://prove2.me/submissions/c4df9037-c2ab-4c49-846f-426c36e7f9ad

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation
import Theorems.Thm_BestBothWorlds_SAO_union_event_stochastic
import Theorems.Thm_BestBothWorlds_SAO_stochastic_no_switch
import Theorems.Thm_BestBothWorlds_SAO_stochastic_deactivation_time

set_option autoImplicit false

open MeasureTheory

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

theorem main (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
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

theorem prob_mono (K n : ℕ) (hK : 1 ≤ K) (β : ℝ) (ν : Fin K → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0)
    (E : (Fin n → Fin K → ℝ) → (Fin n → Fin K) → Prop) (F : (Fin n → Fin K) → Prop)
    (hEF : ∀ ω : Fin n → Fin K → ℝ, (∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1) → ∀ I, E ω I → F I) :
    probStoch n (sao K n β) ν E ≤ probStoch n (sao K n β) ν (fun _ I => F I) := by
  classical
  have hpp := fun (ω : Fin n → Fin K → ℝ) I => pathProb_bounds K n hK β (tableAdv ω) I
  have : IsProbabilityMeasure (rewardTableMeasure n ν) := by
    unfold rewardTableMeasure; infer_instance
  unfold probStoch
  apply integral_mono_of_nonneg
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    unfold probEvent
    refine Finset.sum_nonneg (fun I _ => ?_)
    split_ifs
    · exact (hpp ω I).1
    · exact le_rfl
  · have hm : Measurable fun ω : Fin n → Fin K → ℝ =>
        probEvent n (sao K n β) (tableAdv ω) (fun I => F I) := by
      unfold probEvent
      refine Finset.measurable_sum _ (fun I _ => ?_)
      by_cases hF : F I
      · simp only [hF, if_true]; exact meas_pathProb K n β I
      · simp only [hF, if_false]; exact measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable (Fintype.card (Fin n → Fin K) : ℝ)
      (Filter.Eventually.of_forall (fun ω => ?_))
    unfold probEvent
    have hb : ∀ I : Fin n → Fin K, 0 ≤ (if F I then pathProb (sao K n β) (tableAdv ω) I else 0) ∧
        (if F I then pathProb (sao K n β) (tableAdv ω) I else 0) ≤ 1 := by
      intro I
      split_ifs
      · exact hpp ω I
      · exact ⟨le_rfl, zero_le_one⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun I _ => (hb I).1))]
    calc _ ≤ ∑ _I : Fin n → Fin K, (1 : ℝ) := Finset.sum_le_sum (fun I _ => (hb I).2)
      _ = _ := by simp
  · filter_upwards [ae_table K n ν hν] with ω hω
    unfold probEvent
    refine Finset.sum_le_sum (fun I _ => ?_)
    by_cases hE : E ω I
    · simp [hE, hEF ω hω I hE]
    · simp only [hE, if_false]
      split_ifs
      · exact (hpp ω I).1
      · exact le_rfl

/-! ### The deterministic regret bound on the good event. -/

theorem mean_bounds {K : ℕ} (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (i : Fin K) : 0 ≤ mean ν i ∧ mean ν i ≤ 1 := by
  have h1 : ∀ᵐ y ∂(ν i), y ∈ Set.Icc (0 : ℝ) 1 := by rw [ae_iff]; exact hν i
  unfold mean
  constructor
  · exact integral_nonneg_of_ae (h1.mono fun y hy => hy.1)
  · have := integral_mono_of_nonneg (h1.mono fun y hy => hy.1) (integrable_const (1 : ℝ))
      (h1.mono fun y hy => hy.2)
    simpa using this

theorem pseudo_eq {K n : ℕ} (μ : Fin K → ℝ) (I : Fin n → Fin K) :
    pseudoRegret μ I = ∑ i, gap μ i * (pullCount I i n : ℝ) := by
  unfold pseudoRegret pullCount
  rw [← Finset.sum_fiberwise Finset.univ I (fun r => (⨆ j, μ j) - μ (I r))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hf : Finset.univ.filter (fun r : Fin n => (r : ℕ) < n ∧ I r = i) =
      Finset.univ.filter (fun r => I r = i) :=
    Finset.filter_congr (fun r _ => by simp [r.isLt])
  rw [hf, Finset.sum_congr rfl (g := fun _ => gap μ i)
    (fun r hr => by rw [(Finset.mem_filter.mp hr).2]; rfl), Finset.sum_const, nsmul_eq_mul,
    mul_comm]

theorem arm_bound (K L D Δ τ q m T : ℝ) (hK : 1 ≤ K) (hL : 3 ≤ L) (hm0 : 0 ≤ m)
    (hm : 2 * m ≤ L) (hΔ0 : 0 < Δ) (hΔD : Δ ≤ D) (hD1 : D ≤ 1) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 260 * K * L / D ^ 2) (hq0 : 0 ≤ q)
    (hT : T ≤ q * τ * m + Real.sqrt (4 * q * τ * m * L + 5 * L ^ 2)) :
    D * T ≤ 130 * K * L ^ 2 * q / Δ + K * L ^ 2 * q + 261 * L := by
  have hD0 : 0 < D := lt_of_lt_of_le hΔ0 hΔD
  have hX0 : 0 ≤ q * τ := mul_nonneg hq0 hτ0
  have hτD : τ * D ^ 2 ≤ 260 * K * L := by rwa [le_div_iff₀ (by positivity)] at hτ
  have hDX : D ^ 2 * (q * τ) ≤ 260 * K * L * q := by nlinarith
  have h1 : D * (q * τ * m) ≤ 130 * K * L ^ 2 * q / Δ := by
    have hA : D * (q * τ) ≤ 260 * K * L * q / Δ := by
      rw [le_div_iff₀ hΔ0]
      nlinarith [mul_le_mul_of_nonneg_left hΔD (mul_nonneg hD0.le hX0)]
    have hB : 0 ≤ 260 * K * L * q / Δ := by
      apply div_nonneg _ hΔ0.le
      have : 0 ≤ L := by linarith
      positivity
    calc D * (q * τ * m) = (D * (q * τ)) * m := by ring
      _ ≤ (260 * K * L * q / Δ) * (L / 2) := mul_le_mul hA (by linarith) hm0 hB
      _ = 130 * K * L ^ 2 * q / Δ := by ring
  have hL0 : 0 ≤ L := by linarith
  have h2 : D * Real.sqrt (4 * q * τ * m * L + 5 * L ^ 2) ≤ K * L ^ 2 * q + 261 * L := by
    have hR : 0 ≤ K * L ^ 2 * q + 261 * L := by positivity
    have hD : D = Real.sqrt (D ^ 2) := (Real.sqrt_sq hD0.le).symm
    rw [hD, ← Real.sqrt_mul (by positivity),
      show K * L ^ 2 * q + 261 * L = Real.sqrt ((K * L ^ 2 * q + 261 * L) ^ 2) from
        (Real.sqrt_sq hR).symm]
    apply Real.sqrt_le_sqrt
    have e1 : D ^ 2 * (4 * q * τ * m * L) ≤ 4 * (260 * K * L * q) * m * L := by
      have := mul_le_mul_of_nonneg_right hDX (by positivity : 0 ≤ 4 * m * L)
      nlinarith [this]
    have e2 : 4 * (260 * K * L * q) * m * L ≤ 520 * K * q * L ^ 3 := by
      have := mul_nonneg (by positivity : 0 ≤ 520 * K * q * L ^ 2) (sub_nonneg.mpr hm)
      nlinarith [this]
    have e3 : D ^ 2 * (5 * L ^ 2) ≤ 5 * L ^ 2 := by
      have : D ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg L]
    have e4 : 520 * K * q * L ^ 3 ≤ (K * L ^ 2 * q) ^ 2 + 260 ^ 2 * L ^ 2 := by
      nlinarith [sq_nonneg (K * L ^ 2 * q - 260 * L)]
    have e5 : 0 ≤ K * L ^ 2 * q * L := by positivity
    nlinarith [e1, e2, e3, e4, e5, sq_nonneg L]
  calc D * T ≤ D * (q * τ * m + Real.sqrt (4 * q * τ * m * L + 5 * L ^ 2)) :=
        mul_le_mul_of_nonneg_left hT hD0.le
    _ = D * (q * τ * m) + D * Real.sqrt (4 * q * τ * m * L + 5 * L ^ 2) := by ring
    _ ≤ _ := by linarith

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

theorem regret_det (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (μ : Fin K → ℝ) (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (hgap : ∃ i, 0 < gap μ i)
    (I : Fin n → Fin K) (τ : Fin K → ℕ) (q : Fin K → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hqs : ∑ i, q i ≤ 1 + Real.log K)
    (hτ : ∀ i, 0 < gap μ i →
      (τ i : ℝ) ≤ 260 * K * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / gap μ i ^ 2)
    (hT : ∀ i, (pullCount I i n : ℝ) ≤
      pullBound (q i) (τ i) n (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) :
    pseudoRegret μ I ≤ 260 * K * (1 + Real.log K) *
      Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 / minGap μ := by
  obtain ⟨_, hL3, hLm⟩ := log_beta_bounds K n hK hKn δ hδ0 hδ1
  set L := Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) with hLdef
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (le_trans (by norm_num) hK)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by omega) hKn)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  have hgap0 : ∀ i, 0 ≤ gap μ i := fun i =>
    sub_nonneg.mpr (le_ciSup (Set.finite_range μ).bddAbove i)
  have hgap1 : ∀ i, gap μ i ≤ 1 := by
    intro i
    have : (⨆ j, μ j) ≤ 1 := ciSup_le (fun j => (hμ j).2)
    unfold gap; linarith [(hμ i).1]
  have hΔle : ∀ i, 0 < gap μ i → minGap μ ≤ gap μ i := by
    intro i hi
    unfold minGap
    exact ciInf_le (Set.finite_range (fun j : {j // 0 < gap μ j} => gap μ j.1)).bddBelow ⟨i, hi⟩
  obtain ⟨i0, hi0⟩ := hgap
  have hΔ0 : 0 < minGap μ := by
    have : Nonempty {j // 0 < gap μ j} := ⟨⟨i0, hi0⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun j : {j // 0 < gap μ j} => gap μ j.1)
    unfold minGap
    rw [← hj]
    exact j.2
  have hΔ1 : minGap μ ≤ 1 := (hΔle i0 hi0).trans (hgap1 i0)
  set Δ := minGap μ with hΔdef
  have harm : ∀ i, gap μ i * (pullCount I i n : ℝ) ≤
      (130 * K * L ^ 2 / Δ + K * L ^ 2) * q i + 261 * L := by
    intro i
    by_cases hpos : 0 < gap μ i
    · have := arm_bound K L (gap μ i) Δ (τ i) (q i) (1 + Real.log n) (pullCount I i n) hK1 hL3
        (by linarith) hLm hΔ0 (hΔle i hpos) (hgap1 i) (Nat.cast_nonneg _) (hτ i hpos) (hq0 i)
        (hT i)
      have e : 130 * K * L ^ 2 * q i / Δ = 130 * K * L ^ 2 / Δ * q i := by ring
      linarith
    · have h0 : gap μ i = 0 := le_antisymm (not_lt.mp hpos) (hgap0 i)
      rw [h0, zero_mul]
      have : 0 ≤ (130 * K * L ^ 2 / Δ + K * L ^ 2) * q i := by
        apply mul_nonneg _ (hq0 i); positivity
      linarith
  have hc0 : 0 ≤ 130 * K * L ^ 2 / Δ + K * L ^ 2 := by positivity
  set H := 1 + Real.log K with hH
  have hH1 : 1 ≤ H := by linarith
  rw [pseudo_eq]
  calc ∑ i, gap μ i * (pullCount I i n : ℝ)
      ≤ ∑ i, ((130 * K * L ^ 2 / Δ + K * L ^ 2) * q i + 261 * L) :=
        Finset.sum_le_sum (fun i _ => harm i)
    _ = (130 * K * L ^ 2 / Δ + K * L ^ 2) * ∑ i, q i + K * (261 * L) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (130 * K * L ^ 2 / Δ + K * L ^ 2) * H + K * (261 * L) := by
        have := mul_le_mul_of_nonneg_left hqs hc0
        linarith
    _ ≤ 260 * K * H * L ^ 2 / Δ := by
        set Y := K * H * L ^ 2 / Δ with hY
        have hKHL : 0 ≤ K * H * L ^ 2 := by positivity
        have hY1 : K * H * L ^ 2 ≤ Y := le_div_self hKHL hΔ0 hΔ1
        have hY2 : 261 * K * L ≤ 87 * Y := by
          have : 261 * K * L ≤ 87 * (K * H * L ^ 2) := by
            have h3 : 3 * L ≤ L ^ 2 := by nlinarith
            have h4 : K * L ^ 2 ≤ K * H * L ^ 2 := by
              have := mul_le_mul_of_nonneg_left hH1 (by positivity : 0 ≤ K * L ^ 2)
              nlinarith [this]
            nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ K)]
          linarith
        have e1 : (130 * K * L ^ 2 / Δ + K * L ^ 2) * H = 130 * Y + K * H * L ^ 2 := by
          rw [hY]; ring
        have e2 : 260 * K * H * L ^ 2 / Δ = 260 * Y := by rw [hY]; ring
        have hY0 : 0 ≤ Y := by positivity
        rw [e1, e2]
        nlinarith

/-! ### Assembly: Theorem 4.1 (stochastic model) from the §4.1/§4.2 lemmas. -/

theorem glue (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (hgap : ∃ i, 0 < gap (mean ν) i)
    (β : ℝ) (hβ : β = 10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)
    (hU : 1 - δ ≤ probStoch n (sao K n β) ν (fun ω I =>
      ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
            estRadius K (tauEff K n β (tableAdv ω) I i)
              (qEff K n β (tableAdv ω) I i) t (Real.log β) ∧
        (1 ≤ pullCount I i t →
          |algAvg (tableAdv ω) I i t - mean ν i| ≤
            Real.sqrt (2 * Real.log β / pullCount I i t)) ∧
        (pullCount I i t : ℝ) ≤
            pullBound (qEff K n β (tableAdv ω) I i)
              (tauEff K n β (tableAdv ω) I i) t (Real.log β)))
    (hNS : ∀ (ω : Fin n → Fin K → ℝ), (∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (I : Fin n → Fin K),
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t
            (Real.log β)) →
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
        1 ≤ pullCount I i t →
          |algAvg (tableAdv ω) I i t - mean ν i| ≤
            Real.sqrt (2 * Real.log β / pullCount I i t)) →
      tau0 K n β (tableAdv ω) I = n)
    (hDT : ∀ (ω : Fin n → Fin K → ℝ), (∀ r i, ω r i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (I : Fin n → Fin K),
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
        |estAvg (sao K n β) (tableAdv ω) I i t - mean ν i| ≤
          estRadius K (tauEff K n β (tableAdv ω) I i) (qEff K n β (tableAdv ω) I i) t
            (Real.log β)) →
      (∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n β (tableAdv ω) I),
        1 ≤ pullCount I i t →
          |algAvg (tableAdv ω) I i t - mean ν i| ≤
            Real.sqrt (2 * Real.log β / pullCount I i t)) →
      ∀ i : Fin K, 0 < gap (mean ν) i →
        (tauEff K n β (tableAdv ω) I i : ℝ) ≤ 260 * K * Real.log β / gap (mean ν) i ^ 2) :
    1 - δ ≤ probStoch n (sao K n β) ν (fun _ I =>
      pseudoRegret (mean ν) I ≤ 260 * K * (1 + Real.log K) * Real.log β ^ 2 / minGap (mean ν)) := by
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK
  obtain ⟨hβ1, _, _⟩ := log_beta_bounds K n hK hKn δ hδ0 hδ1
  rw [← hβ] at hβ1
  refine hU.trans (prob_mono K n hK1 β ν hν _ _ ?_)
  intro ω hω I hE
  have h21 := fun i t ht => (hE i t ht).1
  have h23 := fun i t ht => (hE i t ht).2.1
  have hτ0 := hNS ω hω I h21 h23
  have hDT' := hDT ω hω I h21 h23
  have hadv : (tableAdv ω).IsBounded := by
    intro l i
    unfold tableAdv
    split_ifs
    · exact hω _ _
    · exact ⟨le_rfl, zero_le_one⟩
  have hqs := P5292263e.main K n hK hKn β hβ1 (tableAdv ω) hadv I
  have hq0 : ∀ i, 0 ≤ qEff K n β (tableAdv ω) I i := fun i => (sao_bounds K n hK1 β _ i).1
  have hn1 : 1 ≤ n := le_trans hK1 hKn
  have hT : ∀ i, (pullCount I i n : ℝ) ≤
      pullBound (qEff K n β (tableAdv ω) I i) (tauEff K n β (tableAdv ω) I i) n (Real.log β) :=
    fun i => (hE i n (by rw [hτ0]; exact Finset.mem_Icc.mpr ⟨hn1, le_rfl⟩)).2.2
  subst hβ
  exact regret_det K n hK hKn δ hδ0 hδ1 (mean ν) (mean_bounds ν hν) hgap I _ _ hq0 hqs hDT' hT

end Pd1470854

-- selective open: the child names stay fully qualified in `#print axioms` (shadow gate)
open BestBothWorlds.SAO (gap mean probStoch sao pseudoRegret minGap) in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) (hgap : ∃ i, 0 < gap (mean ν) i) :
    1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun _ I =>
      pseudoRegret (mean ν) I ≤
        260 * K * (1 + Real.log K) * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) ^ 2 / minGap (mean ν)) := by
  exact Pd1470854.glue K n hK hKn δ hδ0 hδ1 ν hν hgap _ rfl
    (BestBothWorlds.SAO.union_event_stochastic K n hK hKn δ hδ0 hδ1 ν hν)
    (fun ω hω I h21 h23 =>
      BestBothWorlds.SAO.stochastic_no_switch K n hK hKn δ hδ0 hδ1 ν hν ω hω I h21 h23)
    (fun ω hω I h21 h23 =>
      BestBothWorlds.SAO.stochastic_deactivation_time K n hK hKn δ hδ0 hδ1 ν hν ω hω I h21 h23)
