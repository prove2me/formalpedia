-- Prove2me | solution 1 for FoodTrace.Adoption.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:09:49.579967+00:00
-- url     : https://prove2.me/submissions/269c030c-0dd4-4858-bc74-e73794cf80c0

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

theorem solution (P : Params) (hP : Standing P) :
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
