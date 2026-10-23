-- Prove2me | solution 1 for FoodTrace.Adoption.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:14:32.037106+00:00
-- url     : https://prove2.me/submissions/a86606bb-93d9-4284-8004-2346fb655222

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

open FoodTrace.Adoption

section g79z
variable (P : Params)

noncomputable def g79z_Q (a : Profile P) (i : Fin P.n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, survival P (a j)

theorem g79z_prod_upd (a : Profile P) (i : Fin P.n) (v : Bool) :
    ∏ j, survival P (Function.update a i v j) = survival P v * g79z_Q P a i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, g79z_Q]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem g79z_prod (a : Profile P) (i : Fin P.n) :
    ∏ j, survival P (a j) = survival P (a i) * g79z_Q P a i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), g79z_Q]

theorem g79z_payN (p : ℝ) (a : Profile P) (i : Fin P.n) :
    tier2Payoff .N P p a i = survival P (a i) * g79z_Q P a i * p - supplierCost P (a i) := by
  simp only [tier2Payoff]; rw [g79z_prod P a i]

theorem g79z_updN (p : ℝ) (a : Profile P) (i : Fin P.n) (v : Bool) :
    tier2Payoff .N P p (Function.update a i v) i = survival P v * g79z_Q P a i * p - supplierCost P v := by
  simp only [tier2Payoff]; rw [g79z_prod_upd P a i v, Function.update_self]

theorem g79z_viableN (p : ℝ) (a : Profile P) :
    IsViableEq .N P p a ↔ ∀ i,
      (a i = true → P.e ≤ ρτ P * g79z_Q P a i * p ∧
          0 ≤ (1 - P.ρe) * g79z_Q P a i * p - (P.e + P.cp)) ∧
      (a i = false → ρτ P * g79z_Q P a i * p < P.e ∧ 0 ≤ (1 - P.ρ) * g79z_Q P a i * p - P.cp) := by
  unfold IsViableEq
  refine forall_congr' fun i => ?_
  rw [g79z_payN, g79z_updN, g79z_updN]
  cases a i <;> simp [survival, supplierCost, ρτ] <;> constructor <;> intro h <;>
    first | (constructor <;> nlinarith [h.1, h.2]) | (obtain ⟨h1, h2⟩ := h; constructor <;> nlinarith)

theorem g79z_Q_const (a : Profile P) (v : Bool) (h : ∀ j, a j = v) (i : Fin P.n) :
    g79z_Q P a i = survival P v ^ (P.n - 1) := by
  unfold g79z_Q
  rw [Finset.prod_congr rfl fun j _ => by rw [h j], Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
end g79z

theorem solution (P : Params) (hP : Standing P) :
    (∀ (p : ℝ) (a : Profile P), IsViableEq .N P p a → (∀ i, a i = true) ∨ (∀ i, a i = false)) ∧
    (P.cp < cpLow P → pNo P < pNe P ∧
      (∀ p : ℝ, pNe P ≤ p → ∀ o, Tier2Selects .N P p o ↔ o = some (allEffort P)) ∧
      (∀ p : ℝ, pNo P ≤ p → p < pNe P → ∀ o, Tier2Selects .N P p o ↔ o = some (noEffort P))) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧
      (∀ p : ℝ, pNe P ≤ p → ∀ o, Tier2Selects .N P p o ↔ o = some (allEffort P))) ∧
    (∀ p : ℝ, (∃ o, Tier2Selects .N P p o) ∧
      ∀ o, Tier2Selects .N P p o → (o ≠ none ↔ min (pNe P) (pNo P) ≤ p)) := by
  obtain ⟨hn, hρe, hρ, hρ1, he, hcp, hbar⟩ := hP
  set A := 1 - P.ρe with hA
  set B := 1 - P.ρ with hB
  set m := P.n - 1 with hm
  have hnm : P.n = m + 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hBpos : 0 < B := by linarith
  have hBA : B < A := by linarith
  have hApos : 0 < A := by linarith
  have hτ : ρτ P = A - B := by unfold ρτ; rw [hA, hB]; ring
  have hτpos : 0 < ρτ P := by rw [hτ]; linarith
  have hAm : 0 < A ^ m := pow_pos hApos m
  have hBm : 0 < B ^ m := pow_pos hBpos m
  have hBmA : B ^ m < A ^ m := pow_lt_pow_left₀ hBA hBpos.le (by omega)
  have hbar' : P.cp * ρτ P < B * P.e := by
    unfold cpBar at hbar; rw [lt_div_iff₀ hτpos] at hbar; rw [hB]; linarith
  have sT : survival P true = A := rfl
  have sF : survival P false = B := rfl
  have QT : ∀ i, g79z_Q P (allEffort P) i = A ^ m := fun i =>
    g79z_Q_const P (allEffort P) true (fun _ => rfl) i
  have QF : ∀ i, g79z_Q P (noEffort P) i = B ^ m := fun i =>
    g79z_Q_const P (noEffort P) false (fun _ => rfl) i
  have i0 : Fin P.n := ⟨0, by omega⟩
  have payA : ∀ p i, tier2Payoff .N P p (allEffort P) i = A * A ^ m * p - (P.e + P.cp) := by
    intro p i; rw [g79z_payN, QT]; rfl
  have payB : ∀ p i, tier2Payoff .N P p (noEffort P) i = B * B ^ m * p - P.cp := by
    intro p i; rw [g79z_payN, QF]; simp [noEffort, survival, supplierCost, hB]
  -- dichotomy
  have hdich : ∀ (p : ℝ) (x : Profile P), IsViableEq .N P p x →
      (x = allEffort P ∧ P.e ≤ ρτ P * A ^ m * p ∧ 0 ≤ A * A ^ m * p - (P.e + P.cp)) ∨
      (x = noEffort P ∧ ρτ P * B ^ m * p < P.e ∧ 0 ≤ B * B ^ m * p - P.cp) := by
    intro p x hv
    rw [g79z_viableN] at hv
    by_cases h : ∃ i, x i = true
    · obtain ⟨i, hi⟩ := h
      have hall : ∀ j, x j = true := by
        intro j; by_contra hj; simp only [Bool.not_eq_true] at hj
        have h1 := ((hv i).1 hi).1
        have h2 := ((hv j).2 hj).1
        have hrel : A * g79z_Q P x i = B * g79z_Q P x j := by
          have e1 := g79z_prod P x i; have e2 := g79z_prod P x j
          rw [hi, sT] at e1; rw [hj, sF] at e2; rw [← e1, ← e2]
        -- A e ≤ τ A Q_i p = τ B Q_j p < B e
        have h3 : A * P.e ≤ ρτ P * (A * g79z_Q P x i) * p := by nlinarith
        have h4 : ρτ P * (B * g79z_Q P x j) * p < B * P.e := by nlinarith
        rw [hrel] at h3
        nlinarith
      have hx : x = allEffort P := funext hall
      subst hx
      left
      have := (hv i0).1 rfl
      rw [QT] at this
      exact ⟨rfl, this.1, by rw [hA]; linarith [this.2]⟩
    · push Not at h
      have hall : ∀ j, x j = false := fun j => by simpa using h j
      have hx : x = noEffort P := funext hall
      subst hx
      right
      have := (hv i0).2 rfl
      rw [QF] at this
      exact ⟨rfl, this.1, by rw [hB]; linarith [this.2]⟩
  have hAllV : ∀ p, P.e ≤ ρτ P * A ^ m * p → 0 ≤ A * A ^ m * p - (P.e + P.cp) →
      IsViableEq .N P p (allEffort P) := by
    intro p h1 h2; rw [g79z_viableN]; intro i
    refine ⟨fun _ => ?_, fun h => by simp [allEffort] at h⟩
    rw [QT]; exact ⟨h1, by rw [← hA]; exact h2⟩
  have hNoV : ∀ p, ρτ P * B ^ m * p < P.e → 0 ≤ B * B ^ m * p - P.cp →
      IsViableEq .N P p (noEffort P) := by
    intro p h1 h2; rw [g79z_viableN]; intro i
    refine ⟨fun h => by simp [noEffort] at h, fun _ => ?_⟩
    rw [QF]; exact ⟨h1, by rw [← hB]; exact h2⟩
  -- key inequalities
  have hpNe : ∀ p, pNe P ≤ p ↔ P.e ≤ ρτ P * A ^ m * p := fun p => by
    unfold pNe; rw [← hm, ← hA, div_le_iff₀ (mul_pos hτpos hAm)]; constructor <;> intro h <;> linarith
  have hpNo : ∀ p, pNo P ≤ p ↔ 0 ≤ B * B ^ m * p - P.cp := fun p => by
    unfold pNo; rw [← hB, hnm, pow_succ, div_le_iff₀ (mul_pos hBm hBpos)]
    constructor <;> intro h <;> linarith
  have hK2 : ∀ p, P.e ≤ ρτ P * A ^ m * p → 0 < A * A ^ m * p - (P.e + P.cp) := by
    intro p hp
    -- τ (A A^m p) ≥ A e, and A e - τ (e + cp) = B e - τ cp > 0
    have h1 : A * P.e ≤ ρτ P * (A * A ^ m * p) := by nlinarith
    have h2 : 0 < ρτ P * (A * A ^ m * p - (P.e + P.cp)) := by rw [hτ] at h1 hbar' ⊢; nlinarith
    exact pos_of_mul_pos_right h2 hτpos.le
  have hK3 : ∀ p, P.e ≤ ρτ P * A ^ m * p → B * B ^ m * p - P.cp < A * A ^ m * p - (P.e + P.cp) := by
    intro p hp
    have hppos : 0 < p := by
      by_contra h; push Not at h
      have : ρτ P * A ^ m * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      linarith
    have hgap : 0 < A * A ^ m - B * B ^ m - ρτ P * A ^ m := by
      rw [hτ]; nlinarith
    nlinarith
  have hK5 : ∀ p, p < pNe P → ρτ P * B ^ m * p < P.e := by
    intro p hp
    have h := (not_le.mpr hp); rw [hpNe] at h; push Not at h
    rcases le_or_gt p 0 with hp0 | hp0
    · have : ρτ P * B ^ m * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hp0
      linarith
    · have : ρτ P * B ^ m * p ≤ ρτ P * A ^ m * p := by
        apply mul_le_mul_of_nonneg_right _ hp0.le
        exact mul_le_mul_of_nonneg_left hBmA.le hτpos.le
      linarith
  have selA : ∀ p : ℝ, pNe P ≤ p → ∀ o, Tier2Selects .N P p o ↔ o = some (allEffort P) := by
    intro p hp o
    rw [hpNe] at hp
    have hvA := hAllV p hp (hK2 p hp).le
    constructor
    · intro hs
      cases o with
      | none => exact absurd hvA (hs _)
      | some x =>
        rcases hdich p x hs.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · rfl
        · have := hs.2 _ hvA i0
          rw [payA, payB] at this
          linarith [hK3 p hp]
    · rintro rfl
      refine ⟨hvA, fun y hy i => ?_⟩
      rcases hdich p y hy with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact le_rfl
      · rw [payA, payB]; exact (hK3 p hp).le
  have selB : ∀ p : ℝ, pNo P ≤ p → p < pNe P → ∀ o, Tier2Selects .N P p o ↔ o = some (noEffort P) := by
    intro p hp1 hp2 o
    have hvB := hNoV p (hK5 p hp2) ((hpNo p).1 hp1)
    have hnotA : ¬ (P.e ≤ ρτ P * A ^ m * p) := fun h => absurd ((hpNe p).2 h) (not_le.mpr hp2)
    have huniq : ∀ y, IsViableEq .N P p y → y = noEffort P := by
      intro y hy
      rcases hdich p y hy with ⟨_, h, _⟩ | ⟨h, _⟩
      · exact absurd h hnotA
      · exact h
    constructor
    · intro hs
      cases o with
      | none => exact absurd hvB (hs _)
      | some x => rw [huniq x hs.1]
    · rintro rfl
      exact ⟨hvB, fun y hy i => by rw [huniq y hy]⟩
  have hlow : P.cp < cpLow P ↔ pNo P < pNe P := by
    unfold cpLow pNo pNe
    rw [← hm, ← hA, ← hB, div_lt_div_iff₀ (pow_pos hBpos _) (mul_pos hτpos hAm),
      lt_div_iff₀ (mul_pos hτpos hAm)]
    try (constructor <;> intro h <;> linarith)
  refine ⟨fun p x hv => ?_, fun h => ⟨hlow.1 h, selA, selB⟩,
    fun h => ⟨not_lt.mp (fun h' => absurd (hlow.2 h') (not_lt.mpr h)), selA⟩, fun p => ?_⟩
  · rcases hdich p x hv with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl fun _ => rfl
    · exact Or.inr fun _ => rfl
  · by_cases hpe : pNe P ≤ p
    · refine ⟨⟨_, (selA p hpe _).2 rfl⟩, fun o ho => ?_⟩
      rw [(selA p hpe o).1 ho]; simp [le_trans (min_le_left _ _) hpe]
    · push Not at hpe
      by_cases hpo : pNo P ≤ p
      · refine ⟨⟨_, (selB p hpo hpe _).2 rfl⟩, fun o ho => ?_⟩
        rw [(selB p hpo hpe o).1 ho]; simp [le_trans (min_le_right _ _) hpo]
      · push Not at hpo
        have hnone : ∀ x : Profile P, ¬ IsViableEq .N P p x := by
          intro x hv
          rcases hdich p x hv with ⟨_, h, _⟩ | ⟨_, _, h⟩
          · exact absurd ((hpNe p).2 h) (not_le.mpr hpe)
          · exact absurd ((hpNo p).2 h) (not_le.mpr hpo)
        refine ⟨⟨none, hnone⟩, fun o ho => ?_⟩
        cases o with
        | none => exact iff_of_false (by simp) (not_le.mpr (lt_min hpe hpo))
        | some x => exact absurd ho.1 (hnone x)
