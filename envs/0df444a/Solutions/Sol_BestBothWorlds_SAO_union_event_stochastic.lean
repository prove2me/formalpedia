-- Prove2me | solution 1 for BestBothWorlds.SAO.union_event_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:10:24.650929+00:00
-- url     : https://prove2.me/submissions/8e3550dd-bd2e-415a-9854-998216e80600

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation
import Theorems.Thm_BestBothWorlds_SAO_estimate_concentration_stochastic
import Theorems.Thm_BestBothWorlds_SAO_sample_mean_concentration
import Theorems.Thm_BestBothWorlds_SAO_pull_count_bound


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

namespace Pa12151c4

open BestBothWorlds.SAO

set_option maxHeartbeats 4000000 in
theorem main (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) :
    1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν
      (Ev K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν) := by
  have hK1 : 1 ≤ K := by omega
  have hn : 1 ≤ n := by omega
  haveI hPr : IsProbabilityMeasure (rewardTableMeasure n ν) := by
    unfold rewardTableMeasure; infer_instance
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hKn1 : (1 : ℝ) ≤ K * n := by nlinarith
  have hKn0 : (0 : ℝ) ≤ K * n := by positivity
  have hKn3 : (0 : ℝ) ≤ K * n ^ 3 := by positivity
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hE2 : (K : ℝ) * n * n ≤ K * n * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hKn0
  have hE1 : (K : ℝ) * n * 1 ≤ K * n * n := mul_le_mul_of_nonneg_left hnr hKn0
  set β : ℝ := 10 * (K : ℝ) * (n : ℝ) ^ 3 / δ with hβdef
  have hβ1 : 1 < β := by
    rw [hβdef, lt_div_iff₀ hδ0]
    nlinarith
  set Lβ := Real.log β with hLβ
  set δe : ℝ := δ / (3 * K * n) with hδe
  set δs : ℝ := δ / (3 * K) with hδs
  have hδe0 : 0 < δe := by positivity
  have hδs0 : 0 < δs := by positivity
  have hδe1 : δe < 1 := by
    rw [hδe, div_lt_one (by positivity)]; nlinarith
  have hδs1 : δs < 1 := by
    rw [hδs, div_lt_one (by positivity)]; nlinarith
  set μ := rewardTableMeasure n ν with hμ
  set S1 : Finset (Fin K × ℕ) := Finset.univ ×ˢ Finset.Icc 1 n with hS1
  set S2 : Finset (Fin K) := Finset.univ with hS2
  have hS1c : (S1.card : ℝ) = K * n := by
    rw [hS1, Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.card_Icc,
      Nat.add_sub_cancel, Nat.cast_mul]
  have hS2c : (S2.card : ℝ) = K := by simp [hS2]
  -- child events
  let F5 : Fin K × ℕ → (Fin n → Fin K → ℝ) → (Fin n → Fin K) → Prop := fun j ω I =>
    j.2 ≤ tau0 K n β (tableAdv ω) I →
      |estAvg (sao K n β) (tableAdv ω) I j.1 j.2 - mean ν j.1| ≤
        estRadius K (tauEff K n β (tableAdv ω) I j.1) (qEff K n β (tableAdv ω) I j.1) j.2
          (Real.log (2 * (j.2 : ℝ) ^ 2 / δe))
  let F6 : Fin K → (Fin n → Fin K → ℝ) → (Fin n → Fin K) → Prop := fun i ω I =>
    ∀ t ∈ Finset.Icc 1 n, 1 ≤ pullCount I i t →
      |algAvg (tableAdv ω) I i t - mean ν i| ≤
        Real.sqrt (2 * Real.log (2 * n / δs) / pullCount I i t)
  let F7 : Adversary K → Fin K × ℕ → (Fin n → Fin K) → Prop := fun adv j I =>
    j.2 ≤ tau0 K n β adv I →
      (pullCount I j.1 j.2 : ℝ) ≤
        pullBound (qEff K n β adv I j.1) (tauEff K n β adv I j.1) j.2 (Real.log (j.2 / δe))
  let f : (Fin n → Fin K → ℝ) → ℝ := fun ω =>
    probEvent n (sao K n β) (tableAdv ω) (Ev K n β Lβ ν ω)
  let g5 : Fin K × ℕ → (Fin n → Fin K → ℝ) → ℝ := fun j ω =>
    probEvent n (sao K n β) (tableAdv ω) (F5 j ω)
  let g6 : Fin K → (Fin n → Fin K → ℝ) → ℝ := fun i ω =>
    probEvent n (sao K n β) (tableAdv ω) (F6 i ω)
  -- the children
  have c5 : ∀ j ∈ S1, 1 - δe ≤ ∫ ω, g5 j ω ∂μ := by
    intro j hj
    obtain ⟨-, ht⟩ := Finset.mem_product.mp hj
    obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
    exact estimate_concentration_stochastic K n hK hKn β hβ1 ν hν j.1 j.2 ht1 ht2 δe hδe0
  have c6 : ∀ i ∈ S2, 1 - δs ≤ ∫ ω, g6 i ω ∂μ := by
    intro i _
    exact sample_mean_concentration K n hK hKn β hβ1 ν hν i δs hδs0
  have hint5 : ∀ j ∈ S1, Integrable (g5 j) μ := fun j hj =>
    integrable_of_pos (by linarith [c5 j hj])
  have hint6 : ∀ i ∈ S2, Integrable (g6 i) μ := fun i hi =>
    integrable_of_pos (by linarith [c6 i hi])
  -- the parent integrand
  have hsum : ∀ ω : Fin n → Fin K → ℝ, ∑ I, pathProb (sao K n β) (tableAdv ω) I = 1 :=
    Pb0242b1c.sum_pathProb _ (Pb0242b1c.sao_sum K n hK1 β) n
  have hP0 : ∀ (ω : Fin n → Fin K → ℝ) I, 0 ≤ pathProb (sao K n β) (tableAdv ω) I :=
    fun ω I => (Pd1470854.pathProb_bounds K n hK1 β (tableAdv ω) I).1
  have hfm : Measurable f := by
    show Measurable fun ω => probEvent n (sao K n β) (tableAdv ω) (Ev K n β Lβ ν ω)
    unfold probEvent
    exact Finset.measurable_sum _ (fun I _ =>
      Measurable.ite (meas_Ev K n β Lβ ν I) (Pd1470854.meas_pathProb K n β I) measurable_const)
  have hf01 : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1 := by
    intro ω
    have h0 : 0 ≤ f ω := by
      show 0 ≤ probEvent n (sao K n β) (tableAdv ω) (Ev K n β Lβ ν ω)
      unfold probEvent
      refine Finset.sum_nonneg (fun I _ => ?_)
      split_ifs
      · exact hP0 ω I
      · exact le_rfl
    have h1 : f ω ≤ 1 := by
      show probEvent n (sao K n β) (tableAdv ω) (Ev K n β Lβ ν ω) ≤ 1
      rw [← hsum ω]
      unfold probEvent
      refine Finset.sum_le_sum (fun I _ => ?_)
      split_ifs
      · exact le_rfl
      · exact hP0 ω I
    exact ⟨h0, h1⟩
  have hfi : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hf01 ω).1]
    exact (hf01 ω).2
  -- pointwise union bound, a.e.
  set c : ℝ := (S1.card : ℝ) + S2.card - 1 + S1.card * δe with hc
  let h : (Fin n → Fin K → ℝ) → ℝ := fun ω => (∑ j ∈ S1, g5 j ω + ∑ i ∈ S2, g6 i ω) - c
  have hae : ∀ᵐ ω ∂μ, h ω ≤ f ω := by
    filter_upwards [Pd1470854.ae_table K n ν hν] with ω hω
    have hadv : (tableAdv ω).IsBounded := by
      intro l j
      unfold tableAdv
      split_ifs
      · exact hω _ _
      · exact ⟨le_rfl, zero_le_one⟩
    have c7 : ∀ j ∈ S1, 1 - δe ≤ probEvent n (sao K n β) (tableAdv ω) (F7 (tableAdv ω) j) := by
      intro j hj
      obtain ⟨-, ht⟩ := Finset.mem_product.mp hj
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
      exact pull_count_bound K n hK hKn β hβ1 (tableAdv ω) hadv j.1 j.2 ht1 ht2 δe hδe0
    have hcov : ∀ I, (∀ j ∈ S1, F5 j ω I) → (∀ j ∈ S2, F6 j ω I) →
        (∀ j ∈ S1, F7 (tableAdv ω) j I) → Ev K n β Lβ ν ω I := by
      intro I h5 h6 h7
      unfold Ev
      intro i t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp ht
      have htn : t ≤ n := le_trans ht2 (tau0_le K n β (tableAdv ω) I)
      have hmem : (i, t) ∈ S1 :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨ht1, htn⟩⟩
      have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      have htnr : (t : ℝ) ≤ n := by exact_mod_cast htn
      have hq := qEff_nonneg K n hK1 β (tableAdv ω) I i
      have htt : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
      have ht2' : (t : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) htnr 2
      have hA : (K : ℝ) * n * t ^ 2 ≤ K * n * n ^ 2 := mul_le_mul_of_nonneg_left ht2' hKn0
      have hB : (K : ℝ) * n * 1 ≤ K * n * t ^ 2 := mul_le_mul_of_nonneg_left htt hKn0
      have hC : (K : ℝ) * n * t ≤ K * n * n := mul_le_mul_of_nonneg_left htnr hKn0
      have hD : (K : ℝ) * n * 1 ≤ K * n * t := mul_le_mul_of_nonneg_left htr hKn0
      refine ⟨?_, ?_, ?_⟩
      · have e1 : 2 * (t : ℝ) ^ 2 / δe = (6 * K * n * (t : ℝ) ^ 2) / δ := by
          rw [hδe, div_div_eq_mul_div]; ring
        have hl := log_cmp (6 * K * n * (t : ℝ) ^ 2) (10 * K * (n : ℝ) ^ 3) δ hδ0 hδ1
          (by linarith) (by linarith)
        rw [← e1] at hl
        exact le_trans (h5 (i, t) hmem ht2) (estRadius_mono K _ t _ _ _ hq hl.1 hl.2)
      · intro hT
        have e1 : 2 * (n : ℝ) / δs = (6 * K * n) / δ := by
          rw [hδs, div_div_eq_mul_div]; ring
        have hl := log_cmp (6 * K * n) (10 * K * (n : ℝ) ^ 3) δ hδ0 hδ1
          (by linarith) (by linarith)
        rw [← e1] at hl
        refine le_trans (h6 i (Finset.mem_univ _) t (Finset.mem_Icc.mpr ⟨ht1, htn⟩) hT) ?_
        exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
      · have e1 : (t : ℝ) / δe = (3 * K * n * (t : ℝ)) / δ := by
          rw [hδe, div_div_eq_mul_div]; ring
        have hl := log_cmp (3 * K * n * (t : ℝ)) (10 * K * (n : ℝ) ^ 3) δ hδ0 hδ1
          (by linarith) (by linarith)
        rw [← e1] at hl
        exact le_trans (h7 (i, t) hmem ht2) (pullBound_mono _ _ t _ _ hq ht1 hl.1 hl.2)
    have hu := union3 (sao K n β) (tableAdv ω) (hP0 ω) S1 S2 S1 (Ev K n β Lβ ν ω)
      (fun j => F5 j ω) (fun j => F6 j ω) (fun j => F7 (tableAdv ω) j) hcov
    rw [hsum ω] at hu
    have h7s : ∑ j ∈ S1, (1 - probEvent n (sao K n β) (tableAdv ω) (F7 (tableAdv ω) j)) ≤
        ∑ j ∈ S1, δe := Finset.sum_le_sum (fun j hj => by linarith [c7 j hj])
    have hs5 : ∑ j ∈ S1, (1 - g5 j ω) = S1.card - ∑ j ∈ S1, g5 j ω := by
      rw [Finset.sum_sub_distrib]; simp
    have hs6 : ∑ j ∈ S2, (1 - g6 j ω) = S2.card - ∑ j ∈ S2, g6 j ω := by
      rw [Finset.sum_sub_distrib]; simp
    have hs7 : ∑ j ∈ S1, δe = S1.card * δe := by simp
    change 1 - f ω ≤ ∑ j ∈ S1, (1 - g5 j ω) + ∑ j ∈ S2, (1 - g6 j ω) +
      ∑ j ∈ S1, (1 - probEvent n (sao K n β) (tableAdv ω) (F7 (tableAdv ω) j)) at hu
    show (∑ j ∈ S1, g5 j ω + ∑ i ∈ S2, g6 i ω) - c ≤ f ω
    rw [hc]
    linarith
  have hA5 : Integrable (fun ω => ∑ j ∈ S1, g5 j ω) μ := integrable_finset_sum _ hint5
  have hA6 : Integrable (fun ω => ∑ i ∈ S2, g6 i ω) μ := integrable_finset_sum _ hint6
  have hA : Integrable (fun ω => ∑ j ∈ S1, g5 j ω + ∑ i ∈ S2, g6 i ω) μ := hA5.add hA6
  have hhi : Integrable h μ := hA.sub (integrable_const c)
  have hle : ∫ ω, h ω ∂μ ≤ ∫ ω, f ω ∂μ := integral_mono_ae hhi hfi hae
  have hcalc : ∫ ω, h ω ∂μ = ∑ j ∈ S1, ∫ ω, g5 j ω ∂μ + ∑ i ∈ S2, ∫ ω, g6 i ω ∂μ - c := by
    show ∫ ω, ((∑ j ∈ S1, g5 j ω + ∑ i ∈ S2, g6 i ω) - c) ∂μ = _
    rw [integral_sub hA (integrable_const c), integral_add hA5 hA6, integral_finset_sum _ hint5,
      integral_finset_sum _ hint6]
    simp
  have hb5 : (S1.card : ℝ) * (1 - δe) ≤ ∑ j ∈ S1, ∫ ω, g5 j ω ∂μ := by
    have := Finset.sum_le_sum c5
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hb6 : (S2.card : ℝ) * (1 - δs) ≤ ∑ i ∈ S2, ∫ ω, g6 i ω ∂μ := by
    have := Finset.sum_le_sum c6
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hδsum : (S1.card : ℝ) * δe + S2.card * δs + S1.card * δe = δ := by
    rw [hS1c, hS2c, hδe, hδs]
    field_simp
    ring
  unfold probStoch
  change 1 - δ ≤ ∫ ω, f ω ∂μ
  linarith

end Pa12151c4

open BestBothWorlds.SAO MeasureTheory in
theorem solution (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i (Set.Icc 0 1)ᶜ = 0) :
    1 - δ ≤ probStoch n (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ν (fun ω I =>
      ∀ i : Fin K, ∀ t ∈ Finset.Icc 1 (tau0 K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I),
        |estAvg (sao K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) (tableAdv ω) I i t - mean ν i| ≤
            estRadius K (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i)
              (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ)) ∧
        (1 ≤ pullCount I i t →
          |algAvg (tableAdv ω) I i t - mean ν i| ≤
            Real.sqrt (2 * Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) / pullCount I i t)) ∧
        (pullCount I i t : ℝ) ≤
            pullBound (qEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i)
              (tauEff K n (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ) (tableAdv ω) I i) t (Real.log (10 * (K : ℝ) * (n : ℝ) ^ 3 / δ))) := by
  exact Pa12151c4.main K n hK hKn δ hδ0 hδ1 ν hν
