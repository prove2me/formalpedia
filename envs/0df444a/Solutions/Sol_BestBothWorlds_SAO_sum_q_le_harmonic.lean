-- Prove2me | solution 1 for BestBothWorlds.SAO.sum_q_le_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:39:06.88241+00:00
-- url     : https://prove2.me/submissions/e06a1349-4966-477e-9b75-383b168bc924

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

set_option autoImplicit false

open MeasureTheory

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

open BestBothWorlds.SAO in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (adv : Adversary K) (hadv : adv.IsBounded) (I : Fin n → Fin K) :
    ∑ i : Fin K, qEff K n β adv I i ≤ 1 + Real.log K := by
  exact P5292263e.main K n hK hKn β hβ adv hadv I
