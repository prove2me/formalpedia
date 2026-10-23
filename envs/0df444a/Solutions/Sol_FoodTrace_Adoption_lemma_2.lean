-- Prove2me | solution 1 for FoodTrace.Adoption.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:28:15.059005+00:00
-- url     : https://prove2.me/submissions/56748996-678a-40b6-98f8-ebabc13c3a36

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

theorem g79z_L1 (P : Params) (hP : Standing P) :
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

theorem solution (P : Params) (hP : Standing P) :
    (P.cp < cpLow P → pNo P < pNe P ∧ pNe P < wNe P) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧ pNe P = wNe P) ∧
    (∃ σ₂ : ℝ → Option (Profile P), ∀ p, Tier2Selects .N P p (σ₂ p)) ∧
    (∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) →
      ∀ w : ℝ, ∃ x, IsTier1BR .N σ₂ w x) ∧
    ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) →
      (P.cp < cpLow P →
        (∀ w : ℝ, wNe P ≤ w → σ₁ w = some (pNe P)) ∧
        (∀ w : ℝ, wNo P ≤ w → w < wNe P → σ₁ w = some (pNo P))) ∧
      (cpLow P ≤ P.cp → ∀ w : ℝ, wNe P ≤ w → σ₁ w = some (pNe P)) ∧
      (∀ w : ℝ, tier1Outcome σ₂ (σ₁ w) ≠ none ↔ min (wNe P) (wNo P) ≤ w) := by
  obtain ⟨-, hL2, hL3, hL4⟩ := g79z_L1 P hP
  obtain ⟨hn, hρe, hρ, hρ1, he, hcp, hbar⟩ := hP
  set A := 1 - P.ρe with hA
  set B := 1 - P.ρ with hB
  set m := P.n - 1 with hm
  have hnm : P.n = m + 1 := by omega
  have hBpos : 0 < B := by linarith
  have hApos : 0 < A := by linarith
  have hBA : B < A := by linarith
  have hτ : ρτ P = A - B := by unfold ρτ; rw [hA, hB]; ring
  have hτpos : 0 < ρτ P := by rw [hτ]; linarith
  have hAm : 0 < A ^ m := pow_pos hApos m
  set N : ℝ := (P.n : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast (show 0 < P.n by omega)
  have hAn : 0 < A ^ P.n := pow_pos hApos _
  have hBn : 0 < B ^ P.n := pow_pos hBpos _
  have hell : ell P = A ^ P.n - B ^ P.n := rfl
  have hellpos : 0 < ell P := by rw [hell]; exact sub_pos.mpr (pow_lt_pow_left₀ hBA hBpos.le (by omega))
  set ws := (A * P.e - ρτ P * P.cp) / (ρτ P * ell P) with hws
  have hwNe : wNe P = max ws (pNe P) := rfl
  have hpNe : pNe P = P.e / (ρτ P * A ^ m) := rfl
  have hpNo : pNo P = P.cp / B ^ P.n := rfl
  have hwNo : wNo P = pNo P := rfl
  have hcpLow : cpLow P = P.e * B ^ P.n / (ρτ P * A ^ m) := rfl
  -- comparison V_A - V_B
  have hAn' : A ^ P.n = A * A ^ m := by rw [hnm, pow_succ, mul_comm]
  have hcmp : ∀ w, N * A ^ P.n * (w - pNe P) - N * B ^ P.n * (w - pNo P) = N * ell P * (w - ws) := by
    intro w
    have hl := hellpos.ne'
    have hb := hBn.ne'
    have ha := hAm.ne'
    have ht := hτpos.ne'
    rw [hpNe, hpNo, hws]
    field_simp
    rw [hell, hAn']
    ring
  have hid : ws - pNe P = (cpLow P - P.cp) / ell P := by
    have hl := hellpos.ne'
    have ha := hAm.ne'
    have ht := hτpos.ne'
    rw [hws, hpNe, hcpLow]
    field_simp
    rw [hell, hAn']
    ring
  have hlow1 : P.cp < cpLow P → pNe P < ws := by
    intro h; have : 0 < (cpLow P - P.cp) / ell P := div_pos (by linarith) hellpos
    linarith
  have hlow2 : cpLow P ≤ P.cp → ws ≤ pNe P := by
    intro h; have : (cpLow P - P.cp) / ell P ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hellpos.le
    linarith
  have i0 : Fin P.n := ⟨0, by omega⟩
  have hAB : allEffort P ≠ noEffort P := by
    intro h; have := congrFun h i0; simp [allEffort, noEffort] at this
  have uA : unitsSold .N P (allEffort P) = N * A ^ P.n := by
    simp [unitsSold, allEffort, survival, hN, hA]
  have uB : unitsSold .N P (noEffort P) = N * B ^ P.n := by
    simp [unitsSold, noEffort, survival, hN, hB]
  -- tier-2 response
  have hσ : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) →
      (∀ p, pNe P ≤ p → σ₂ p = some (allEffort P)) ∧
      (∀ p, pNo P ≤ p → p < pNe P → σ₂ p = some (noEffort P)) ∧
      (∀ p, p < pNe P → p < pNo P → σ₂ p = none) := by
    intro σ₂ hs
    have selA : ∀ p, pNe P ≤ p → σ₂ p = some (allEffort P) := by
      intro p hp
      by_cases hc : P.cp < cpLow P
      · exact ((hL2 hc).2.1 p hp _).1 (hs p)
      · exact ((hL3 (not_lt.mp hc)).2 p hp _).1 (hs p)
    refine ⟨selA, fun p h1 h2 => ?_, fun p h1 h2 => ?_⟩
    · have hc : P.cp < cpLow P := by
        by_contra hc; have := (hL3 (not_lt.mp hc)).1; linarith
      exact ((hL2 hc).2.2 p h1 h2 _).1 (hs p)
    · by_contra hne
      have := ((hL4 p).2 _ (hs p)).1 hne
      exact absurd this (not_le.mpr (lt_min h1 h2))
  have hprof : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w p,
      (pNe P ≤ p → tier1Profit .N σ₂ w (some p) = N * A ^ P.n * (w - p)) ∧
      (pNo P ≤ p → p < pNe P → tier1Profit .N σ₂ w (some p) = N * B ^ P.n * (w - p)) ∧
      (p < pNe P → p < pNo P → tier1Profit .N σ₂ w (some p) = 0) := by
    intro σ₂ hs w p
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    refine ⟨fun hp => ?_, fun hp hp' => ?_, fun hp hp' => ?_⟩
    · simp only [tier1Profit, h1 p hp, uA]
    · simp only [tier1Profit, h2 p hp hp', uB]
    · simp only [tier1Profit, h3 p hp hp']
  have hnone : ∀ σ₂ : ℝ → Option (Profile P), ∀ w, tier1Profit .N σ₂ w none = 0 := fun _ _ => rfl
  -- classification of tier-1 choices
  have hcls : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w y,
      (tier1Outcome σ₂ y = none ∧ tier1Profit .N σ₂ w y = 0) ∨
      (∃ p, y = some p ∧ pNe P ≤ p ∧ tier1Profit .N σ₂ w y = N * A ^ P.n * (w - p) ∧
        tier1Outcome σ₂ y = some (allEffort P)) ∨
      (∃ p, y = some p ∧ pNo P ≤ p ∧ p < pNe P ∧ tier1Profit .N σ₂ w y = N * B ^ P.n * (w - p) ∧
        tier1Outcome σ₂ y = some (noEffort P)) := by
    intro σ₂ hs w y
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    cases y with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨f1, f2, f3⟩ := hprof σ₂ hs w p
      rcases le_or_gt (pNe P) p with hp | hp
      · exact Or.inr (Or.inl ⟨p, rfl, hp, f1 hp, h1 p hp⟩)
      · rcases le_or_gt (pNo P) p with hp' | hp'
        · exact Or.inr (Or.inr ⟨p, rfl, hp', hp, f2 hp' hp, h2 p hp' hp⟩)
        · exact Or.inl ⟨h3 p hp hp', f3 hp hp'⟩
  have hmid : ∀ p, pNo P ≤ p → p < pNe P → P.cp < cpLow P := by
    intro p h1 h2; by_contra hc; have := (hL3 (not_lt.mp hc)).1; linarith
  have hmonoA : ∀ w p, pNe P ≤ p → N * A ^ P.n * (w - p) ≤ N * A ^ P.n * (w - pNe P) :=
    fun w p hp => mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hmonoB : ∀ w p, pNo P ≤ p → N * B ^ P.n * (w - p) ≤ N * B ^ P.n * (w - pNo P) :=
    fun w p hp => mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hwNe1 : ws ≤ wNe P := le_max_left _ _
  have hwNe2 : pNe P ≤ wNe P := le_max_right _ _
  -- region R1
  have hR1 : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w x,
      IsTier1BR .N σ₂ w x → wNe P ≤ w → x = some (pNe P) := by
    intro σ₂ hs w x ⟨hmax, heff, _⟩ hw
    obtain ⟨h1, -, -⟩ := hσ σ₂ hs
    have vA := (hprof σ₂ hs w (pNe P)).1 le_rfl
    have hVA : 0 ≤ N * A ^ P.n * (w - pNe P) := mul_nonneg (by positivity) (by linarith)
    have hge := hmax (some (pNe P)); rw [vA] at hge
    have htie : tier1Profit .N σ₂ w x = N * A ^ P.n * (w - pNe P) →
        tier1Outcome σ₂ x = some (allEffort P) := fun h =>
      heff ⟨some (pNe P), by rw [vA, h], by simp [tier1Outcome, InducesEffort, h1 _ le_rfl]⟩
    rcases hcls σ₂ hs w x with ⟨ho, hp⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, hp1, hp2, hpr, ho⟩
    · rw [hp] at hge
      have := htie (by rw [hp]; linarith)
      rw [ho] at this; exact absurd this (by simp)
    · rw [hpr] at hge
      have : p ≤ pNe P := by
        by_contra hc; push Not at hc
        have : N * A ^ P.n * (w - p) < N * A ^ P.n * (w - pNe P) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        linarith
      rw [le_antisymm this hp]
    · have hc := hmid p hp1 hp2
      have hVAB : N * B ^ P.n * (w - pNo P) ≤ N * A ^ P.n * (w - pNe P) := by
        have : 0 ≤ N * ell P * (w - ws) := mul_nonneg (by positivity) (by linarith)
        linarith [hcmp w]
      have := htie (by rw [hpr] at hge ⊢; linarith [hmonoB w p hp1])
      rw [ho] at this; exact absurd (Option.some.inj this) hAB.symm
  -- region R2
  have hR2 : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w x,
      IsTier1BR .N σ₂ w x → P.cp < cpLow P → wNo P ≤ w → w < wNe P → x = some (pNo P) := by
    intro σ₂ hs w x ⟨hmax, _, htrade⟩ hc hw1 hw2
    obtain ⟨-, h2, -⟩ := hσ σ₂ hs
    have hlt := (hL2 hc).1
    have hws' : wNe P = ws := max_eq_left (hlow1 hc).le
    have vB := (hprof σ₂ hs w (pNo P)).2.1 le_rfl hlt
    have hVB : 0 ≤ N * B ^ P.n * (w - pNo P) := mul_nonneg (by positivity) (by rw [← hwNo]; linarith)
    have hVAB : N * A ^ P.n * (w - pNe P) < N * B ^ P.n * (w - pNo P) := by
      have : N * ell P * (w - ws) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith [hcmp w]
    have hge := hmax (some (pNo P)); rw [vB] at hge
    rcases hcls σ₂ hs w x with ⟨ho, hp⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, hp1, hp2, hpr, -⟩
    · rw [hp] at hge
      have := htrade ⟨some (pNo P), by rw [vB, hp]; linarith, by simp [tier1Outcome, h2 _ le_rfl hlt]⟩
      exact absurd ho this
    · rw [hpr] at hge; linarith [hmonoA w p hp]
    · rw [hpr] at hge
      have : p ≤ pNo P := by
        by_contra hc'; push Not at hc'
        have : N * B ^ P.n * (w - p) < N * B ^ P.n * (w - pNo P) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        linarith
      rw [le_antisymm this hp1]
  -- region R3: below both thresholds every trading option loses money
  have hlow3 : ∀ w, w < min (wNe P) (wNo P) → w < pNe P ∧ w < pNo P := by
    intro w hw
    have h1 := lt_of_lt_of_le hw (min_le_left _ _)
    have h2 : w < pNo P := lt_of_lt_of_le hw (min_le_right _ _)
    refine ⟨?_, h2⟩
    by_cases hc : P.cp < cpLow P
    · linarith [(hL2 hc).1]
    · have := max_eq_right (hlow2 (not_lt.mp hc)); rw [← hwNe] at this; linarith
  have hneg : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w y,
      w < min (wNe P) (wNo P) → tier1Outcome σ₂ y ≠ none → tier1Profit .N σ₂ w y < 0 := by
    intro σ₂ hs w y hw hy
    obtain ⟨hw1, hw2⟩ := hlow3 w hw
    rcases hcls σ₂ hs w y with ⟨ho, -⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, hp1, -, hpr, -⟩
    · exact absurd ho hy
    · rw [hpr]; exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
    · rw [hpr]; exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hR3 : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) → ∀ w x,
      IsTier1BR .N σ₂ w x → w < min (wNe P) (wNo P) → tier1Outcome σ₂ x = none := by
    intro σ₂ hs w x ⟨hmax, _, _⟩ hw
    by_contra hne
    have := hneg σ₂ hs w x hw hne
    have h0 := hmax none; rw [hnone] at h0; linarith
  refine ⟨fun hc => ⟨(hL2 hc).1, by have := hlow1 hc; linarith⟩,
    fun hc => ⟨(hL3 hc).1, (max_eq_right (hlow2 hc)).symm⟩,
    ⟨fun p => Classical.choose (hL4 p).1, fun p => Classical.choose_spec (hL4 p).1⟩, ?_, ?_⟩
  · intro σ₂ hs w
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    by_cases hw1 : wNe P ≤ w
    · have vA := (hprof σ₂ hs w (pNe P)).1 le_rfl
      have hVA : 0 ≤ N * A ^ P.n * (w - pNe P) := mul_nonneg (by positivity) (by linarith)
      refine ⟨some (pNe P), fun y => ?_, fun _ => by simp [tier1Outcome, InducesEffort, h1 _ le_rfl],
        fun _ => by simp [tier1Outcome, h1 _ le_rfl]⟩
      rw [vA]
      rcases hcls σ₂ hs w y with ⟨-, hp⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, hp1, hp2, hpr, -⟩
      · rw [hp]; exact hVA
      · rw [hpr]; exact hmonoA w p hp
      · have hc := hmid p hp1 hp2
        have : 0 ≤ N * ell P * (w - ws) := mul_nonneg (by positivity) (by linarith)
        rw [hpr]; linarith [hcmp w, hmonoB w p hp1]
    · push Not at hw1
      by_cases hw2 : wNo P ≤ w
      · have hc : P.cp < cpLow P := by
          by_contra hc
          have e1 := max_eq_right (hlow2 (not_lt.mp hc)); rw [← hwNe] at e1
          have := (hL3 (not_lt.mp hc)).1; rw [hwNo] at hw2; linarith
        have hlt := (hL2 hc).1
        have hws' : wNe P = ws := max_eq_left (hlow1 hc).le
        have vB := (hprof σ₂ hs w (pNo P)).2.1 le_rfl hlt
        have hVB : 0 ≤ N * B ^ P.n * (w - pNo P) := mul_nonneg (by positivity) (by rw [← hwNo]; linarith)
        have hVAB : N * A ^ P.n * (w - pNe P) < N * B ^ P.n * (w - pNo P) := by
          have : N * ell P * (w - ws) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
          linarith [hcmp w]
        refine ⟨some (pNo P), fun y => ?_, fun ⟨y, hy, hye⟩ => ?_,
          fun _ => by simp [tier1Outcome, h2 _ le_rfl hlt]⟩
        · rw [vB]
          rcases hcls σ₂ hs w y with ⟨-, hp⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, hp1, -, hpr, -⟩
          · rw [hp]; exact hVB
          · rw [hpr]; linarith [hmonoA w p hp]
          · rw [hpr]; exact hmonoB w p hp1
        · exfalso
          rw [vB] at hy
          rcases hcls σ₂ hs w y with ⟨ho, -⟩ | ⟨p, rfl, hp, hpr, -⟩ | ⟨p, rfl, -, -, -, ho⟩
          · simp [InducesEffort, ho] at hye
          · rw [hpr] at hy; linarith [hmonoA w p hp]
          · simp only [InducesEffort, ho] at hye; exact hAB.symm (Option.some.inj hye)
      · push Not at hw2
        have hw : w < min (wNe P) (wNo P) := lt_min hw1 hw2
        refine ⟨none, fun y => ?_, fun ⟨y, hy, hye⟩ => ?_, fun ⟨y, hy, hye⟩ => ?_⟩
        · rw [hnone]
          by_cases ho : tier1Outcome σ₂ y = none
          · rcases hcls σ₂ hs w y with ⟨-, hp⟩ | ⟨p, rfl, -, -, ho'⟩ | ⟨p, rfl, -, -, -, ho'⟩
            · rw [hp]
            · rw [ho'] at ho; exact absurd ho (by simp)
            · rw [ho'] at ho; exact absurd ho (by simp)
          · exact (hneg σ₂ hs w y hw ho).le
        · have hne : tier1Outcome σ₂ y ≠ none := by
            simp only [InducesEffort] at hye; rw [hye]; simp
          have := hneg σ₂ hs w y hw hne; rw [hy, hnone] at this; linarith
        · have := hneg σ₂ hs w y hw hye; rw [hy, hnone] at this; linarith
  · intro σ₂ σ₁ hs hbr
    obtain ⟨h1, h2, h3⟩ := hσ σ₂ hs
    refine ⟨fun hc => ⟨fun w hw => hR1 σ₂ hs w _ (hbr w) hw,
      fun w hw1 hw2 => hR2 σ₂ hs w _ (hbr w) hc hw1 hw2⟩,
      fun _ w hw => hR1 σ₂ hs w _ (hbr w) hw, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hc; push Not at hc
      exact h (hR3 σ₂ hs w _ (hbr w) hc)
    · by_cases hw1 : wNe P ≤ w
      · rw [hR1 σ₂ hs w _ (hbr w) hw1]; simp [tier1Outcome, h1 _ le_rfl]
      · push Not at hw1
        have hw2 : wNo P ≤ w := by
          by_contra hc; push Not at hc; exact absurd h (not_le.mpr (lt_min hw1 hc))
        have hc : P.cp < cpLow P := by
          by_contra hc
          have e1 := max_eq_right (hlow2 (not_lt.mp hc)); rw [← hwNe] at e1
          have := (hL3 (not_lt.mp hc)).1; rw [hwNo] at hw2; linarith
        rw [hR2 σ₂ hs w _ (hbr w) hc hw2 hw1]; simp [tier1Outcome, h2 _ le_rfl (hL2 hc).1]
