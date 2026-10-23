-- Prove2me | solution 1 for FoodTrace.Adoption.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:18:43.52266+00:00
-- url     : https://prove2.me/submissions/6a2e51c9-d3e7-4714-a678-32fe62bec4df

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

open FoodTrace.Adoption

section g79z
variable (P : Params)

theorem g79z_payT (p : ℝ) (a : Profile P) (i : Fin P.n) :
    tier2Payoff .T P p a i = survival P (a i) * p - supplierCost P (a i) := rfl

theorem g79z_upd (p : ℝ) (a : Profile P) (i : Fin P.n) (v : Bool) :
    tier2Payoff .T P p (Function.update a i v) i = survival P v * p - supplierCost P v := by
  simp [tier2Payoff]

/-- viability in case T, coordinatewise -/
theorem g79z_viable (p : ℝ) (a : Profile P) :
    IsViableEq .T P p a ↔ ∀ i, (a i = true → P.e ≤ ρτ P * p ∧ 0 ≤ (1 - P.ρe) * p - (P.e + P.cp)) ∧
      (a i = false → ρτ P * p < P.e ∧ 0 ≤ (1 - P.ρ) * p - P.cp) := by
  unfold IsViableEq
  refine forall_congr' fun i => ?_
  rw [g79z_payT, g79z_upd, g79z_upd]
  cases a i <;> simp [survival, supplierCost, ρτ] <;> constructor <;> intro h <;>
    first | (constructor <;> linarith [h.1, h.2]) | (obtain ⟨h1, h2⟩ := h; constructor <;> linarith)
end g79z

theorem g79z_L3 (P : Params) (hP : Standing P) :
    pTo P < pTe P ∧
    (∀ (p : ℝ) (a : Profile P), IsViableEq .T P p a → (∀ i, a i = true) ∨ (∀ i, a i = false)) ∧
    (∀ p : ℝ, pTe P ≤ p → ∀ o, Tier2Selects .T P p o ↔ o = some (allEffort P)) ∧
    (∀ p : ℝ, pTo P ≤ p → p < pTe P → ∀ o, Tier2Selects .T P p o ↔ o = some (noEffort P)) ∧
    (∀ p : ℝ, (∃ o, Tier2Selects .T P p o) ∧
      ∀ o, Tier2Selects .T P p o → (o ≠ none ↔ pTo P ≤ p)) := by
  obtain ⟨hn, hρe, hρ, hρ1, he, hcp, hbar⟩ := hP
  have hτ : 0 < ρτ P := by unfold ρτ; linarith
  have h1ρ : 0 < 1 - P.ρ := by linarith
  have hbar' : P.cp * ρτ P < (1 - P.ρ) * P.e := by
    unfold cpBar at hbar; rwa [lt_div_iff₀ hτ] at hbar
  have hTe : ∀ p, pTe P ≤ p ↔ P.e ≤ ρτ P * p := fun p => by
    unfold pTe; rw [div_le_iff₀ hτ, mul_comm]
  have hTo : ∀ p, pTo P ≤ p ↔ 0 ≤ (1 - P.ρ) * p - P.cp := fun p => by
    unfold pTo; rw [div_le_iff₀ h1ρ, sub_nonneg, mul_comm]
  have hlt : pTo P < pTe P := by
    unfold pTo pTe; rw [div_lt_div_iff₀ h1ρ hτ]; linarith
  -- payT nonneg when effort is preferred
  have hpayT : ∀ p, P.e ≤ ρτ P * p → 0 ≤ (1 - P.ρe) * p - (P.e + P.cp) := by
    intro p hp
    have hp' : P.e / ρτ P ≤ p := by rw [div_le_iff₀ hτ, mul_comm]; exact hp
    have : (1 - P.ρe) * (P.e / ρτ P) - (P.e + P.cp) = ((1 - P.ρ) * P.e - P.cp * ρτ P) / ρτ P := by
      unfold ρτ at *; field_simp; ring
    have h2 : 0 ≤ (1 - P.ρe) * (P.e / ρτ P) - (P.e + P.cp) := by
      rw [this]; exact div_nonneg (by linarith) hτ.le
    have : (1 - P.ρe) * (P.e / ρτ P) ≤ (1 - P.ρe) * p := mul_le_mul_of_nonneg_left hp' (by linarith)
    linarith
  have hne : Nonempty (Fin P.n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i0⟩ := hne
  -- dichotomy
  have hdich : ∀ (p : ℝ) (a : Profile P), IsViableEq .T P p a →
      ((∀ i, a i = true) ∧ P.e ≤ ρτ P * p) ∨ ((∀ i, a i = false) ∧ ρτ P * p < P.e ∧
        0 ≤ (1 - P.ρ) * p - P.cp) := by
    intro p a hv
    rw [g79z_viable] at hv
    by_cases h : ∃ i, a i = true
    · obtain ⟨i, hi⟩ := h
      have hE := ((hv i).1 hi).1
      left; refine ⟨fun j => ?_, hE⟩
      by_contra hj; simp only [Bool.not_eq_true] at hj
      have := ((hv j).2 hj).1; linarith
    · push Not at h
      right
      have hf : ∀ i, a i = false := fun i => by simpa using h i
      exact ⟨hf, ((hv i0).2 (hf i0)).1, ((hv i0).2 (hf i0)).2⟩
  have hAllV : ∀ p, P.e ≤ ρτ P * p → IsViableEq .T P p (allEffort P) := by
    intro p hp; rw [g79z_viable]; intro i
    exact ⟨fun _ => ⟨hp, hpayT p hp⟩, fun h => by simp [allEffort] at h⟩
  have hNoV : ∀ p, ρτ P * p < P.e → 0 ≤ (1 - P.ρ) * p - P.cp → IsViableEq .T P p (noEffort P) := by
    intro p hp hp2; rw [g79z_viable]; intro i
    exact ⟨fun h => by simp [noEffort] at h, fun _ => ⟨hp, hp2⟩⟩
  have hAll : ∀ a : Profile P, (∀ i, a i = true) → a = allEffort P := fun a h => funext fun i => h i
  have hNo : ∀ a : Profile P, (∀ i, a i = false) → a = noEffort P := fun a h => funext fun i => h i
  have part3 : ∀ p : ℝ, pTe P ≤ p → ∀ o, Tier2Selects .T P p o ↔ o = some (allEffort P) := by
    intro p hp o
    rw [hTe] at hp
    have huniq : ∀ b, IsViableEq .T P p b → b = allEffort P := by
      intro b hb
      rcases hdich p b hb with ⟨h, _⟩ | ⟨_, h, _⟩
      · exact hAll b h
      · linarith
    constructor
    · intro hs
      cases o with
      | none => exact absurd (hAllV p hp) (hs _)
      | some a => rw [huniq a hs.1]
    · rintro rfl
      exact ⟨hAllV p hp, fun b hb i => by rw [huniq b hb]⟩
  have part4 : ∀ p : ℝ, pTo P ≤ p → p < pTe P → ∀ o, Tier2Selects .T P p o ↔ o = some (noEffort P) := by
    intro p hp1 hp2 o
    rw [hTo] at hp1
    have hp2' : ρτ P * p < P.e := by by_contra h; push Not at h; exact absurd ((hTe p).2 h) (not_le.mpr hp2)
    have huniq : ∀ b, IsViableEq .T P p b → b = noEffort P := by
      intro b hb
      rcases hdich p b hb with ⟨_, h⟩ | ⟨h, _, _⟩
      · linarith
      · exact hNo b h
    constructor
    · intro hs
      cases o with
      | none => exact absurd (hNoV p hp2' hp1) (hs _)
      | some a => rw [huniq a hs.1]
    · rintro rfl
      exact ⟨hNoV p hp2' hp1, fun b hb i => by rw [huniq b hb]⟩
  refine ⟨hlt, fun p a hv => ?_, part3, part4, fun p => ?_⟩
  · rcases hdich p a hv with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · by_cases hpo : pTo P ≤ p
    · by_cases hpe : pTe P ≤ p
      · refine ⟨⟨_, (part3 p hpe _).2 rfl⟩, fun o ho => ?_⟩
        rw [(part3 p hpe o).1 ho]; simp [hpo]
      · push Not at hpe
        refine ⟨⟨_, (part4 p hpo hpe _).2 rfl⟩, fun o ho => ?_⟩
        rw [(part4 p hpo hpe o).1 ho]; simp [hpo]
    · have hnone : ∀ a : Profile P, ¬ IsViableEq .T P p a := by
        intro a hv
        rcases hdich p a hv with ⟨_, h⟩ | ⟨_, _, h⟩
        · exact hpo (le_of_lt (lt_of_lt_of_le hlt ((hTe p).2 h)))
        · exact hpo ((hTo p).2 h)
      refine ⟨⟨none, hnone⟩, fun o ho => ?_⟩
      cases o with
      | none => simp [hpo]
      | some a => exact absurd ho.1 (hnone a)

theorem solution (P : Params) (hP : Standing P) :
    wTo P = pTo P ∧ pTo P < pTe P ∧ pTe P < wTe P ∧
    (∃ σ₂ : ℝ → Option (Profile P), ∀ p, Tier2Selects .T P p (σ₂ p)) ∧
    (∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) →
      ∀ w : ℝ, ∃ x, IsTier1BR .T σ₂ w x) ∧
    ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .T P p (σ₂ p)) → (∀ w, IsTier1BR .T σ₂ w (σ₁ w)) →
      (∀ w : ℝ, wTe P ≤ w → σ₁ w = some (pTe P)) ∧
      (∀ w : ℝ, wTo P ≤ w → w < wTe P → σ₁ w = some (pTo P)) ∧
      (∀ w : ℝ, tier1Outcome σ₂ (σ₁ w) ≠ none ↔ wTo P ≤ w) := by
  obtain ⟨hlt, -, part3, part4, part5⟩ := g79z_L3 P hP
  obtain ⟨hn, hρe, hρ, hρ1, he, hcp, hbar⟩ := hP
  set A := 1 - P.ρe with hA
  set B := 1 - P.ρ with hB
  have hτ : ρτ P = A - B := by unfold ρτ; rw [hA, hB]; ring
  have hτpos : 0 < ρτ P := by rw [hτ]; linarith
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hbar' : P.cp * ρτ P < B * P.e := by
    unfold cpBar at hbar; rw [lt_div_iff₀ hτpos] at hbar; rw [hB]; linarith
  set N : ℝ := (P.n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast (show 0 < P.n by omega)
  have hpTe : pTe P = P.e / ρτ P := rfl
  have hpTo : pTo P = P.cp / B := rfl
  have hwTe : pTe P < wTe P := by
    unfold wTe; rw [hpTe, div_lt_div_iff₀ hτpos (by positivity)]
    rw [← hA]; rw [hτ] at hbar' ⊢; nlinarith
  -- comparison of branch values
  have hcmp : ∀ w, N * A * (w - pTe P) - N * B * (w - pTo P) = N * ρτ P * (w - wTe P) := by
    intro w; rw [hpTe, hpTo]; unfold wTe; rw [← hA]; rw [hτ] at hτpos ⊢
    field_simp; ring
  have i0 : Fin P.n := ⟨0, by omega⟩
  have hAB : allEffort P ≠ noEffort P := by
    intro h; have := congrFun h i0; simp [allEffort, noEffort] at this
  have uA : unitsSold .T P (allEffort P) = N * A := by
    simp [unitsSold, allEffort, survival, hN, hA]; ring
  have uB : unitsSold .T P (noEffort P) = N * B := by
    simp [unitsSold, noEffort, survival, hN, hB]; ring
  -- the tier-2 response is determined
  have hσ : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) →
      (∀ p, pTe P ≤ p → σ₂ p = some (allEffort P)) ∧
      (∀ p, pTo P ≤ p → p < pTe P → σ₂ p = some (noEffort P)) ∧
      (∀ p, p < pTo P → σ₂ p = none) := by
    intro σ₂ hs
    refine ⟨fun p hp => (part3 p hp _).1 (hs p), fun p h1 h2 => (part4 p h1 h2 _).1 (hs p),
      fun p hp => ?_⟩
    by_contra hne
    exact absurd ((((part5 p).2 _ (hs p)).1 hne)) (not_le.mpr hp)
  -- profit evaluation
  have hprof : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) → ∀ w p,
      (pTe P ≤ p → tier1Profit .T σ₂ w (some p) = N * A * (w - p)) ∧
      (pTo P ≤ p → p < pTe P → tier1Profit .T σ₂ w (some p) = N * B * (w - p)) ∧
      (p < pTo P → tier1Profit .T σ₂ w (some p) = 0) := by
    intro σ₂ hs w p
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    refine ⟨fun hp => ?_, fun hp hp' => ?_, fun hp => ?_⟩
    · simp only [tier1Profit, h1 p hp, uA]
    · simp only [tier1Profit, h2 p hp hp', uB]
    · simp only [tier1Profit, h3 p hp]
  have hnone : ∀ σ₂ : ℝ → Option (Profile P) , ∀ w, tier1Profit .T σ₂ w none = 0 := fun _ _ => rfl
  -- upper bound on profits and characterisation of effort/trading choices
  have hbound : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) → ∀ w y,
      tier1Profit .T σ₂ w y ≤ max 0 (max (N * A * (w - pTe P)) (N * B * (w - pTo P))) ∧
      (InducesEffort P (tier1Outcome σ₂ y) → tier1Profit .T σ₂ w y ≤ N * A * (w - pTe P)) ∧
      (tier1Outcome σ₂ y ≠ none → tier1Profit .T σ₂ w y ≤ max (N * A * (w - pTe P)) (N * B * (w - pTo P))) := by
    intro σ₂ hs w y
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    cases y with
    | none =>
      refine ⟨by simp [hnone], fun h => by simp [tier1Outcome, InducesEffort] at h, fun h => by
        simp [tier1Outcome] at h⟩
    | some p =>
      obtain ⟨e1, e2, e3⟩ := hprof σ₂ hs w p
      rcases le_or_gt (pTe P) p with hp | hp
      · rw [e1 hp]
        have : N * A * (w - p) ≤ N * A * (w - pTe P) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        exact ⟨le_trans this (le_trans (le_max_left _ _) (le_max_right _ _)), fun _ => this,
          fun _ => le_trans this (le_max_left _ _)⟩
      · rcases le_or_gt (pTo P) p with hp' | hp'
        · rw [e2 hp' hp]
          have : N * B * (w - p) ≤ N * B * (w - pTo P) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          refine ⟨le_trans this (le_trans (le_max_right _ _) (le_max_right _ _)), fun h => ?_,
            fun _ => le_trans this (le_max_right _ _)⟩
          simp only [tier1Outcome, InducesEffort, h2 p hp' hp] at h
          exact absurd (Option.some.inj h).symm hAB
        · rw [e3 hp']
          refine ⟨le_max_left _ _, fun h => ?_, fun h => ?_⟩
          · simp only [tier1Outcome, InducesEffort, h3 p hp'] at h; exact absurd h (by simp)
          · simp only [tier1Outcome, h3 p hp'] at h; exact absurd rfl h
  have hBR : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) → ∀ w x,
      IsTier1BR .T σ₂ w x →
      (wTe P ≤ w → x = some (pTe P)) ∧ (wTo P ≤ w → w < wTe P → x = some (pTo P)) ∧
      (w < wTo P → tier1Outcome σ₂ x = none) := by
    intro σ₂ hs w x ⟨hmax, heff, htrade⟩
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    obtain ⟨e1, -, -⟩ := hprof σ₂ hs w (pTe P)
    have vA := e1 le_rfl
    obtain ⟨-, e2, -⟩ := hprof σ₂ hs w (pTo P)
    have vB := e2 le_rfl hlt
    have hcw := hcmp w
    refine ⟨fun hw => ?_, fun hw1 hw2 => ?_, fun hw => ?_⟩
    · -- effort region
      have hVA : 0 < N * A * (w - pTe P) := by
        apply mul_pos (by positivity); linarith
      have hge := hmax (some (pTe P)); rw [vA] at hge
      cases x with
      | none => simp [hnone] at hge; linarith
      | some p =>
        obtain ⟨f1, f2, f3⟩ := hprof σ₂ hs w p
        rcases le_or_gt (pTe P) p with hp | hp
        · rw [f1 hp] at hge
          have : p ≤ pTe P := by
            by_contra hc; push Not at hc
            have : N * A * (w - p) < N * A * (w - pTe P) :=
              mul_lt_mul_of_pos_left (by linarith) (by positivity)
            linarith
          rw [le_antisymm this hp]
        · rcases le_or_gt (pTo P) p with hp' | hp'
          · rw [f2 hp' hp] at hge
            have hle : N * B * (w - p) ≤ N * B * (w - pTo P) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have hVAB : N * B * (w - pTo P) ≤ N * A * (w - pTe P) := by
              have : 0 ≤ N * ρτ P * (w - wTe P) := mul_nonneg (by positivity) (by linarith)
              linarith
            have heq : tier1Profit .T σ₂ w (some (pTe P)) = tier1Profit .T σ₂ w (some p) := by
              rw [vA, f2 hp' hp]; linarith
            have := heff ⟨some (pTe P), heq, by simp [tier1Outcome, InducesEffort, h1 _ le_rfl]⟩
            simp only [tier1Outcome, InducesEffort, h2 p hp' hp] at this
            exact absurd (Option.some.inj this) hAB.symm
          · rw [f3 hp'] at hge; linarith
    · -- no-effort region
      have hVB : 0 ≤ N * B * (w - pTo P) :=
        mul_nonneg (by positivity) (by have : wTo P = pTo P := rfl; linarith)
      have hVAB : N * A * (w - pTe P) < N * B * (w - pTo P) := by
        have : N * ρτ P * (w - wTe P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
        linarith
      have hge := hmax (some (pTo P)); rw [vB] at hge
      have hnt : tier1Outcome σ₂ x = none → False := by
        intro hx
        have hx0 : tier1Profit .T σ₂ w x ≤ 0 := by
          cases x with
          | none => simp [hnone]
          | some p =>
            have hp : p < pTo P := by
              by_contra hc; push Not at hc
              rcases le_or_gt (pTe P) p with h | h
              · simp [tier1Outcome, h1 p h] at hx
              · simp [tier1Outcome, h2 p hc h] at hx
            rw [(hprof σ₂ hs w p).2.2 hp]
        have heq : tier1Profit .T σ₂ w (some (pTo P)) = tier1Profit .T σ₂ w x := by
          rw [vB]; linarith
        have := htrade ⟨some (pTo P), heq, by simp [tier1Outcome, h2 _ le_rfl hlt]⟩
        exact this hx
      cases x with
      | none => exact absurd rfl (fun h => hnt h)
      | some p =>
        obtain ⟨f1, f2, f3⟩ := hprof σ₂ hs w p
        rcases le_or_gt (pTe P) p with hp | hp
        · rw [f1 hp] at hge
          have : N * A * (w - p) ≤ N * A * (w - pTe P) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
        · rcases le_or_gt (pTo P) p with hp' | hp'
          · rw [f2 hp' hp] at hge
            have : p ≤ pTo P := by
              by_contra hc; push Not at hc
              have : N * B * (w - p) < N * B * (w - pTo P) :=
                mul_lt_mul_of_pos_left (by linarith) (by positivity)
              linarith
            rw [le_antisymm this hp']
          · exact absurd (by simp [tier1Outcome, h3 p hp']) hnt
    · -- no trade
      by_contra hne
      have h0 := hmax none
      rw [hnone] at h0
      cases x with
      | none => exact hne rfl
      | some p =>
        obtain ⟨f1, f2, f3⟩ := hprof σ₂ hs w p
        have hwo : w < pTo P := hw
        rcases le_or_gt (pTe P) p with hp | hp
        · rw [f1 hp] at h0
          have : N * A * (w - p) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
          linarith
        · rcases le_or_gt (pTo P) p with hp' | hp'
          · rw [f2 hp' hp] at h0
            have : N * B * (w - p) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
            linarith
          · exact hne (by simp [tier1Outcome, h3 p hp'])
  refine ⟨rfl, hlt, hwTe, ⟨fun p => Classical.choose (part5 p).1,
    fun p => Classical.choose_spec (part5 p).1⟩, ?_, ?_⟩
  · intro σ₂ hs w
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    obtain ⟨e1, -, -⟩ := hprof σ₂ hs w (pTe P)
    have vA := e1 le_rfl
    obtain ⟨-, e2, -⟩ := hprof σ₂ hs w (pTo P)
    have vB := e2 le_rfl hlt
    have hcw := hcmp w
    by_cases hw1 : wTe P ≤ w
    · refine ⟨some (pTe P), fun y => ?_, fun _ => by simp [tier1Outcome, InducesEffort, h1 _ le_rfl],
        fun _ => by simp [tier1Outcome, h1 _ le_rfl]⟩
      have hb := (hbound σ₂ hs w y).1
      have hVA : 0 < N * A * (w - pTe P) := mul_pos (by positivity) (by linarith)
      have hVAB : N * B * (w - pTo P) ≤ N * A * (w - pTe P) := by
        have : 0 ≤ N * ρτ P * (w - wTe P) := mul_nonneg (by positivity) (by linarith)
        linarith
      rw [vA]
      calc tier1Profit .T σ₂ w y ≤ _ := hb
        _ = N * A * (w - pTe P) := by rw [max_eq_left hVAB, max_eq_right hVA.le]
    · push Not at hw1
      by_cases hw2 : wTo P ≤ w
      · have hVB : 0 ≤ N * B * (w - pTo P) :=
          mul_nonneg (by positivity) (by have : wTo P = pTo P := rfl; linarith)
        have hVAB : N * A * (w - pTe P) < N * B * (w - pTo P) := by
          have : N * ρτ P * (w - wTe P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
          linarith
        refine ⟨some (pTo P), fun y => ?_, fun ⟨y, hy, hye⟩ => ?_,
          fun _ => by simp [tier1Outcome, h2 _ le_rfl hlt]⟩
        · rw [vB]
          calc tier1Profit .T σ₂ w y ≤ _ := (hbound σ₂ hs w y).1
            _ = N * B * (w - pTo P) := by rw [max_eq_right hVAB.le, max_eq_right hVB]
        · have := (hbound σ₂ hs w y).2.1 hye
          rw [hy, vB] at this; linarith
      · push Not at hw2
        have hwo : w < pTo P := hw2
        have hVA : N * A * (w - pTe P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
        have hVB : N * B * (w - pTo P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
        refine ⟨none, fun y => ?_, fun ⟨y, hy, hye⟩ => ?_, fun ⟨y, hy, hye⟩ => ?_⟩
        · rw [hnone]
          calc tier1Profit .T σ₂ w y ≤ _ := (hbound σ₂ hs w y).1
            _ = 0 := by rw [max_eq_left (max_lt hVA hVB).le]
        · have := (hbound σ₂ hs w y).2.1 hye
          rw [hy, hnone] at this; linarith
        · have := (hbound σ₂ hs w y).2.2 hye
          rw [hy, hnone] at this; linarith [max_lt hVA hVB]
  · intro σ₂ σ₁ hs hbr
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    refine ⟨fun w hw => (hBR σ₂ hs w _ (hbr w)).1 hw, fun w hw1 hw2 => (hBR σ₂ hs w _ (hbr w)).2.1 hw1 hw2,
      fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hc; push Not at hc
      exact h ((hBR σ₂ hs w _ (hbr w)).2.2 hc)
    · by_cases hw1 : wTe P ≤ w
      · rw [(hBR σ₂ hs w _ (hbr w)).1 hw1]; simp [tier1Outcome, h1 _ le_rfl]
      · push Not at hw1
        rw [(hBR σ₂ hs w _ (hbr w)).2.1 h hw1]; simp [tier1Outcome, h2 _ le_rfl hlt]
