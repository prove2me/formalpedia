-- Prove2me | solution 1 for FoodTrace.Adoption.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:47:17.16772+00:00
-- url     : https://prove2.me/submissions/2fdcb9a7-fe7e-43a5-871b-c79d9c717c36

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

theorem g79z_L2 (P : Params) (hP : Standing P) :
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

set_option maxHeartbeats 4000000 in
theorem solution (P : Params) (hP : Standing P) :
    (∀ r : ℝ, ∃ s : Strategy P, IsSPNE .N P r s) ∧
    (P.cp < cpLow P → pNo P < pNe P ∧ pNe P < wNe P ∧ wNe P < rNe P ∧
      ∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s →
        (rNe P ≤ r → s.w = some (wNe P) ∧ s.σ₁ (wNe P) = some (pNe P) ∧
          s.σ₂ (pNe P) = some (allEffort P)) ∧
        (rNo P ≤ r → r < rNe P → s.w = some (wNo P) ∧ s.σ₁ (wNo P) = some (pNo P) ∧
          s.σ₂ (pNo P) = some (noEffort P))) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧ pNe P = wNe P ∧ wNe P = rNe P ∧
      ∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s →
        rNe P ≤ r → s.w = some (wNe P) ∧ s.σ₁ (wNe P) = some (pNe P) ∧
          s.σ₂ (pNe P) = some (allEffort P)) ∧
    (∀ (r : ℝ) (s : Strategy P), IsSPNE .N P r s → (Trades s ↔ min (rNe P) (rNo P) ≤ r)) := by
  obtain ⟨-, hL1b, hL1c, hL1d⟩ := g79z_L1 P hP
  obtain ⟨hK1, hK2, ⟨σ₂0, hσ₂0⟩, hBRex, hBRchar⟩ := g79z_L2 P hP
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
  have hAn' : A ^ P.n = A * A ^ m := by rw [hnm, pow_succ, mul_comm]
  have hpNe : pNe P = P.e / (ρτ P * A ^ m) := rfl
  have hpNo : pNo P = P.cp / B ^ P.n := rfl
  have hwNo : wNo P = pNo P := rfl
  have hrNo : rNo P = pNo P := rfl
  have hcpLow : cpLow P = P.e * B ^ P.n / (ρτ P * A ^ m) := rfl
  set ws := (A * P.e - ρτ P * P.cp) / (ρτ P * ell P) with hws
  have hwNe : wNe P = max ws (pNe P) := rfl
  set rs1 := (A ^ (P.n + 1) * P.e - (2 * A ^ P.n - B ^ P.n) * ρτ P * P.cp) / (ρτ P * ell P ^ 2) with hrs1
  have hrNe : rNe P = max rs1 (pNe P) := rfl
  have hBpNo : B ^ P.n * pNo P = P.cp := by rw [hpNo]; field_simp
  -- algebra
  have hid1 : ws - pNe P = (cpLow P - P.cp) / ell P := by
    have hl := hellpos.ne'; have ha := hAm.ne'; have ht := hτpos.ne'
    rw [hws, hpNe, hcpLow]; field_simp; rw [hell, hAn']; ring
  have hrs1ws : rs1 - ws = B ^ P.n * (ws - pNo P) / ell P := by
    have hl := hellpos.ne'; have ht := hτpos.ne'; have hb := hBn.ne'
    rw [hrs1, hws, hpNo]; field_simp; rw [hell, pow_succ]; ring
  have hrs1pNe : rs1 - pNe P = ((P.e * B ^ P.n - P.cp * ρτ P * A ^ m) * (2 * A ^ P.n - B ^ P.n)
      - P.e * (A ^ P.n - B ^ P.n) ^ 2 + P.e * (A ^ P.n - B ^ P.n) ^ 2
      - P.e * B ^ P.n * (2 * A ^ P.n - B ^ P.n) + A ^ m * A ^ (P.n + 1) * P.e
      - P.e * (A ^ P.n - B ^ P.n) ^ 2) / (ρτ P * ell P ^ 2 * A ^ m) := by
    have hl := hellpos.ne'; have ha := hAm.ne'; have ht := hτpos.ne'
    rw [hrs1, hpNe]; field_simp; rw [hell]; ring
  have hcase1 : P.cp < cpLow P → pNe P < ws ∧ ws < rs1 ∧ wNe P = ws ∧ rNe P = rs1 := by
    intro hc
    have h1 : pNe P < ws := by
      have : 0 < (cpLow P - P.cp) / ell P := div_pos (by linarith) hellpos
      linarith
    have hpo : pNo P < pNe P := (hK1 hc).1
    have h2 : ws < rs1 := by
      have : 0 < B ^ P.n * (ws - pNo P) / ell P := div_pos (mul_pos hBn (by linarith)) hellpos
      linarith
    exact ⟨h1, h2, max_eq_left h1.le, max_eq_left (by linarith)⟩
  have hcase2 : cpLow P ≤ P.cp → wNe P = pNe P ∧ rNe P = pNe P := by
    intro hc
    have h1 : ws ≤ pNe P := by
      have : (cpLow P - P.cp) / ell P ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hellpos.le
      linarith
    have hcl : P.e * B ^ P.n ≤ P.cp * ρτ P * A ^ m := by
      rw [hcpLow, div_le_iff₀ (mul_pos hτpos hAm)] at hc; linarith
    have h2 : rs1 ≤ pNe P := by
      have hpos : 0 < 2 * A ^ P.n - B ^ P.n := by linarith
      have hnum : (P.e * B ^ P.n - P.cp * ρτ P * A ^ m) * (2 * A ^ P.n - B ^ P.n)
          - P.e * (A ^ P.n - B ^ P.n) ^ 2 + P.e * (A ^ P.n - B ^ P.n) ^ 2
          - P.e * B ^ P.n * (2 * A ^ P.n - B ^ P.n) + A ^ m * A ^ (P.n + 1) * P.e
          - P.e * (A ^ P.n - B ^ P.n) ^ 2 ≤ 0 := by
        have e1 : A ^ m * A ^ (P.n + 1) = (A ^ P.n) ^ 2 := by rw [hAn', pow_succ, hAn']; ring
        rw [e1]
        have := mul_le_mul_of_nonneg_right (sub_nonpos.mpr hcl) hpos.le
        nlinarith
      have : (_ : ℝ) / (ρτ P * ell P ^ 2 * A ^ m) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
      linarith [hrs1pNe]
    exact ⟨max_eq_right h1, max_eq_right h2⟩
  have i0 : Fin P.n := ⟨0, by omega⟩
  have hAB : allEffort P ≠ noEffort P := by
    intro h; have := congrFun h i0; simp [allEffort, noEffort] at this
  have uA : unitsSold .N P (allEffort P) = N * A ^ P.n := by
    simp [unitsSold, allEffort, survival, hN, hA]
  have uB : unitsSold .N P (noEffort P) = N * B ^ P.n := by
    simp [unitsSold, noEffort, survival, hN, hB]
  have hpNeWNe : pNe P ≤ wNe P := le_max_right _ _
  have hmidc : ∀ w, wNo P ≤ w → w < wNe P → P.cp < cpLow P := by
    intro w h1 h2; by_contra hc
    have e := (hcase2 (not_lt.mp hc)).1
    have := (hL1c (not_lt.mp hc)).1
    rw [hwNo] at h1; linarith
  -- tier-2 at pNe / pNo
  have s2A : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) →
      σ₂ (pNe P) = some (allEffort P) := by
    intro σ₂ hs
    by_cases hc : P.cp < cpLow P
    · exact ((hL1b hc).2.1 _ le_rfl _).1 (hs _)
    · exact ((hL1c (not_lt.mp hc)).2 _ le_rfl _).1 (hs _)
  have s2B : ∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) →
      P.cp < cpLow P → σ₂ (pNo P) = some (noEffort P) := by
    intro σ₂ hs hc
    exact ((hL1b hc).2.2 _ le_rfl (hL1b hc).1 _).1 (hs _)
  have hzone : ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) →
      (∀ w, wNe P ≤ w → σ₁ w = some (pNe P)) ∧
      (∀ w, wNo P ≤ w → w < wNe P → σ₁ w = some (pNo P)) ∧
      (∀ w, w < min (wNe P) (wNo P) → tier1Outcome σ₂ (σ₁ w) = none) := by
    intro σ₂ σ₁ hs hbr
    obtain ⟨c1, c2, c3⟩ := hBRchar σ₂ σ₁ hs hbr
    refine ⟨fun w hw => ?_, fun w hw1 hw2 => (c1 (hmidc w hw1 hw2)).2 w hw1 hw2, fun w hw => ?_⟩
    · by_cases hc : P.cp < cpLow P
      · exact (c1 hc).1 w hw
      · exact c2 (not_lt.mp hc) w hw
    · by_contra h; exact absurd ((c3 w).1 h) (not_le.mpr hw)
  have hcls : ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r y,
      (retailerOutcome σ₂ σ₁ y = none ∧ retailerPayoff .N σ₂ σ₁ r y = 0) ∨
      (∃ w, y = some w ∧ wNe P ≤ w ∧ retailerPayoff .N σ₂ σ₁ r y = N * A ^ P.n * (r - w) ∧
        retailerOutcome σ₂ σ₁ y = some (allEffort P)) ∨
      (∃ w, y = some w ∧ wNo P ≤ w ∧ w < wNe P ∧ retailerPayoff .N σ₂ σ₁ r y = N * B ^ P.n * (r - w) ∧
        retailerOutcome σ₂ σ₁ y = some (noEffort P)) := by
    intro σ₂ σ₁ hs hbr r y
    obtain ⟨z1, z2, z3⟩ := hzone σ₂ σ₁ hs hbr
    cases y with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some w =>
      rcases le_or_gt (wNe P) w with hw | hw
      · have ho : tier1Outcome σ₂ (σ₁ w) = some (allEffort P) := by
          rw [z1 w hw]; exact s2A σ₂ hs
        refine Or.inr (Or.inl ⟨w, rfl, hw, ?_, by simp [retailerOutcome, ho]⟩)
        simp only [retailerPayoff, ho, uA]
      · rcases le_or_gt (wNo P) w with hw' | hw'
        · have ho : tier1Outcome σ₂ (σ₁ w) = some (noEffort P) := by
            rw [z2 w hw' hw]; exact s2B σ₂ hs (hmidc w hw' hw)
          refine Or.inr (Or.inr ⟨w, rfl, hw', hw, ?_, by simp [retailerOutcome, ho]⟩)
          simp only [retailerPayoff, ho, uB]
        · have ho := z3 w (lt_min hw hw')
          refine Or.inl ⟨by simp [retailerOutcome, ho], ?_⟩
          simp only [retailerPayoff, ho]
  have hmonoA : ∀ r w, wNe P ≤ w → N * A ^ P.n * (r - w) ≤ N * A ^ P.n * (r - wNe P) :=
    fun r w hw => mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hmonoB : ∀ r w, wNo P ≤ w → N * B ^ P.n * (r - w) ≤ N * B ^ P.n * (r - wNo P) :=
    fun r w hw => mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- comparison in case 1
  have hcmpR : P.cp < cpLow P → ∀ r,
      N * A ^ P.n * (r - wNe P) - N * B ^ P.n * (r - wNo P) = N * ell P * (r - rNe P) := by
    intro hc r
    obtain ⟨-, -, e1, e2⟩ := hcase1 hc
    have hl := hellpos.ne'
    have key : ell P * rs1 = ell P * ws + B ^ P.n * (ws - pNo P) := by
      have := hrs1ws; field_simp at this; linarith
    rw [e1, e2, hwNo]
    have : N * A ^ P.n * (r - ws) - N * B ^ P.n * (r - pNo P) =
        N * ((A ^ P.n - B ^ P.n) * r - (ell P * ws + B ^ P.n * (ws - pNo P))) := by rw [hell]; ring
    rw [this, ← key, hell]; ring
  have vA : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r,
      retailerPayoff .N σ₂ σ₁ r (some (wNe P)) = N * A ^ P.n * (r - wNe P) ∧
      retailerOutcome σ₂ σ₁ (some (wNe P)) = some (allEffort P) := by
    intro σ₂ σ₁ hs hbr r
    rcases hcls σ₂ σ₁ hs hbr r (some (wNe P)) with ⟨ho, -⟩ | ⟨w, hw, -, hp, ho⟩ | ⟨w, hw, -, h2, -⟩
    · exfalso; have := (hzone σ₂ σ₁ hs hbr).1 _ le_rfl
      simp [retailerOutcome, tier1Outcome, this, s2A σ₂ hs] at ho
    · cases hw; exact ⟨hp, ho⟩
    · cases hw; exact absurd h2 (lt_irrefl _)
  have vB : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) →
      P.cp < cpLow P → ∀ r,
      retailerPayoff .N σ₂ σ₁ r (some (wNo P)) = N * B ^ P.n * (r - wNo P) ∧
      retailerOutcome σ₂ σ₁ (some (wNo P)) = some (noEffort P) := by
    intro σ₂ σ₁ hs hbr hc r
    have hwl : wNo P < wNe P := by
      obtain ⟨h1, -, e1, -⟩ := hcase1 hc; rw [hwNo, e1]; linarith [(hK1 hc).1, (hL1b hc).1]
    rcases hcls σ₂ σ₁ hs hbr r (some (wNo P)) with ⟨ho, -⟩ | ⟨w, hw, h1, -, -⟩ | ⟨w, hw, -, -, hp, ho⟩
    · exfalso; have := (hzone σ₂ σ₁ hs hbr).2.1 _ le_rfl hwl
      simp [retailerOutcome, tier1Outcome, this, s2B σ₂ hs hc] at ho
    · cases hw; linarith
    · cases hw; exact ⟨hp, ho⟩
  -- regions
  have hrNeW : wNe P ≤ rNe P := by
    by_cases hc : P.cp < cpLow P
    · obtain ⟨-, h2, e1, e2⟩ := hcase1 hc; rw [e1, e2]; exact h2.le
    · obtain ⟨e1, e2⟩ := hcase2 (not_lt.mp hc); rw [e1, e2]
  have hR1 : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r x,
      IsRetailerOpt .N σ₂ σ₁ r x → rNe P ≤ r → x = some (wNe P) := by
    intro σ₂ σ₁ hs hbr r x ⟨hmax, heff, _⟩ hr
    obtain ⟨va, oa⟩ := vA σ₂ σ₁ hs hbr r
    have hVA : 0 ≤ N * A ^ P.n * (r - wNe P) := mul_nonneg (by positivity) (by linarith)
    have hge := hmax (some (wNe P)); rw [va] at hge
    have htie : retailerPayoff .N σ₂ σ₁ r x = N * A ^ P.n * (r - wNe P) →
        retailerOutcome σ₂ σ₁ x = some (allEffort P) := fun h =>
      heff ⟨some (wNe P), by rw [va, h], by simp only [InducesEffort, oa]⟩
    rcases hcls σ₂ σ₁ hs hbr r x with ⟨ho, hp⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, hw1, hw2, hpr, ho⟩
    · rw [hp] at hge
      have := htie (by rw [hp]; linarith)
      rw [ho] at this; exact absurd this (by simp)
    · rw [hpr] at hge
      have : w ≤ wNe P := by
        by_contra hc; push Not at hc
        have : N * A ^ P.n * (r - w) < N * A ^ P.n * (r - wNe P) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        linarith
      rw [le_antisymm this hw]
    · have hc := hmidc w hw1 hw2
      have hVAB : N * B ^ P.n * (r - wNo P) ≤ N * A ^ P.n * (r - wNe P) := by
        have : 0 ≤ N * ell P * (r - rNe P) := mul_nonneg (by positivity) (by linarith)
        linarith [hcmpR hc r]
      have := htie (by rw [hpr] at hge ⊢; linarith [hmonoB r w hw1])
      rw [ho] at this; exact absurd (Option.some.inj this) hAB.symm
  have hR2 : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r x,
      IsRetailerOpt .N σ₂ σ₁ r x → P.cp < cpLow P → rNo P ≤ r → r < rNe P → x = some (wNo P) := by
    intro σ₂ σ₁ hs hbr r x ⟨hmax, _, htrade⟩ hc hr1 hr2
    obtain ⟨vb, ob⟩ := vB σ₂ σ₁ hs hbr hc r
    have hVB : 0 ≤ N * B ^ P.n * (r - wNo P) :=
      mul_nonneg (by positivity) (by rw [hwNo]; rw [hrNo] at hr1; linarith)
    have hVAB : N * A ^ P.n * (r - wNe P) < N * B ^ P.n * (r - wNo P) := by
      have : N * ell P * (r - rNe P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
      linarith [hcmpR hc r]
    have hge := hmax (some (wNo P)); rw [vb] at hge
    rcases hcls σ₂ σ₁ hs hbr r x with ⟨ho, hp⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, hw1, hw2, hpr, -⟩
    · rw [hp] at hge
      have := htrade ⟨some (wNo P), by rw [vb, hp]; linarith, by rw [ob]; simp⟩
      exact absurd ho this
    · rw [hpr] at hge; linarith [hmonoA r w hw]
    · rw [hpr] at hge
      have : w ≤ wNo P := by
        by_contra hc'; push Not at hc'
        have : N * B ^ P.n * (r - w) < N * B ^ P.n * (r - wNo P) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
        linarith
      rw [le_antisymm this hw1]
  have hlow3 : ∀ r, r < min (rNe P) (rNo P) → r < wNe P ∧ r < wNo P := by
    intro r hr
    have h1 := lt_of_lt_of_le hr (min_le_left _ _)
    have h2 : r < rNo P := lt_of_lt_of_le hr (min_le_right _ _)
    rw [hrNo] at h2
    refine ⟨?_, by rw [hwNo]; exact h2⟩
    by_cases hc : P.cp < cpLow P
    · linarith [(hL1b hc).1]
    · obtain ⟨e1, e2⟩ := hcase2 (not_lt.mp hc); rw [e2] at h1; rw [e1]; exact h1
  have hneg : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r y,
      r < min (rNe P) (rNo P) → retailerOutcome σ₂ σ₁ y ≠ none → retailerPayoff .N σ₂ σ₁ r y < 0 := by
    intro σ₂ σ₁ hs hbr r y hr hy
    obtain ⟨h1, h2⟩ := hlow3 r hr
    rcases hcls σ₂ σ₁ hs hbr r y with ⟨ho, -⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, hw1, -, hpr, -⟩
    · exact absurd ho hy
    · rw [hpr]; exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
    · rw [hpr]; exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hR3 : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r x,
      IsRetailerOpt .N σ₂ σ₁ r x → r < min (rNe P) (rNo P) → retailerOutcome σ₂ σ₁ x = none := by
    intro σ₂ σ₁ hs hbr r x ⟨hmax, _, _⟩ hr
    by_contra hne
    have := hneg σ₂ σ₁ hs hbr r x hr hne
    have h0 := hmax none
    have hz : retailerPayoff .N σ₂ σ₁ r none = 0 := rfl
    rw [hz] at h0; linarith
  -- existence of retailer optimum
  have hRex : ∀ σ₂ σ₁, (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) → ∀ r,
      ∃ x, IsRetailerOpt .N σ₂ σ₁ r x := by
    intro σ₂ σ₁ hs hbr r
    have hz : retailerPayoff .N σ₂ σ₁ r none = 0 := rfl
    obtain ⟨va, oa⟩ := vA σ₂ σ₁ hs hbr r
    by_cases hr1 : rNe P ≤ r
    · have hVA : 0 ≤ N * A ^ P.n * (r - wNe P) := mul_nonneg (by positivity) (by linarith)
      refine ⟨some (wNe P), fun y => ?_, fun _ => by simp only [InducesEffort, oa],
        fun _ => by rw [oa]; simp⟩
      rw [va]
      rcases hcls σ₂ σ₁ hs hbr r y with ⟨-, hp⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, hw1, hw2, hpr, -⟩
      · rw [hp]; exact hVA
      · rw [hpr]; exact hmonoA r w hw
      · have hc := hmidc w hw1 hw2
        have : 0 ≤ N * ell P * (r - rNe P) := mul_nonneg (by positivity) (by linarith)
        rw [hpr]; linarith [hcmpR hc r, hmonoB r w hw1]
    · push Not at hr1
      by_cases hr2 : rNo P ≤ r
      · have hc : P.cp < cpLow P := by
          by_contra hc
          obtain ⟨e1, e2⟩ := hcase2 (not_lt.mp hc)
          have := (hL1c (not_lt.mp hc)).1
          rw [hrNo] at hr2; rw [e2] at hr1; linarith
        obtain ⟨vb, ob⟩ := vB σ₂ σ₁ hs hbr hc r
        have hVB : 0 ≤ N * B ^ P.n * (r - wNo P) :=
          mul_nonneg (by positivity) (by rw [hwNo]; rw [hrNo] at hr2; linarith)
        have hVAB : N * A ^ P.n * (r - wNe P) < N * B ^ P.n * (r - wNo P) := by
          have : N * ell P * (r - rNe P) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
          linarith [hcmpR hc r]
        refine ⟨some (wNo P), fun y => ?_, fun ⟨y, hy, hye⟩ => ?_, fun _ => by rw [ob]; simp⟩
        · rw [vb]
          rcases hcls σ₂ σ₁ hs hbr r y with ⟨-, hp⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, hw1, -, hpr, -⟩
          · rw [hp]; exact hVB
          · rw [hpr]; linarith [hmonoA r w hw]
          · rw [hpr]; exact hmonoB r w hw1
        · exfalso
          rw [vb] at hy
          rcases hcls σ₂ σ₁ hs hbr r y with ⟨ho, -⟩ | ⟨w, rfl, hw, hpr, -⟩ | ⟨w, rfl, -, -, -, ho⟩
          · simp [InducesEffort, ho] at hye
          · rw [hpr] at hy; linarith [hmonoA r w hw]
          · simp only [InducesEffort, ho] at hye; exact hAB.symm (Option.some.inj hye)
      · push Not at hr2
        have hr : r < min (rNe P) (rNo P) := lt_min hr1 hr2
        refine ⟨none, fun y => ?_, fun ⟨y, hy, hye⟩ => ?_, fun ⟨y, hy, hye⟩ => ?_⟩
        · rw [hz]
          by_cases ho : retailerOutcome σ₂ σ₁ y = none
          · rcases hcls σ₂ σ₁ hs hbr r y with ⟨-, hp⟩ | ⟨w, rfl, -, -, ho'⟩ | ⟨w, rfl, -, -, -, ho'⟩
            · rw [hp]
            · rw [ho'] at ho; exact absurd ho (by simp)
            · rw [ho'] at ho; exact absurd ho (by simp)
          · exact (hneg σ₂ σ₁ hs hbr r y hr ho).le
        · have hne : retailerOutcome σ₂ σ₁ y ≠ none := by
            simp only [InducesEffort] at hye; rw [hye]; simp
          have := hneg σ₂ σ₁ hs hbr r y hr hne; rw [hy, hz] at this; linarith
        · have := hneg σ₂ σ₁ hs hbr r y hr hye; rw [hy, hz] at this; linarith
  refine ⟨fun r => ?_, fun hc => ?_, fun hc => ?_, fun r s ⟨hs, hbr, hopt⟩ => ?_⟩
  · set σ₁0 : ℝ → Option ℝ := fun w => Classical.choose (hBRex σ₂0 hσ₂0 w)
    have hσ₁0 : ∀ w, IsTier1BR .N σ₂0 w (σ₁0 w) := fun w => Classical.choose_spec (hBRex σ₂0 hσ₂0 w)
    obtain ⟨x, hx⟩ := hRex σ₂0 σ₁0 hσ₂0 hσ₁0 r
    exact ⟨⟨σ₂0, σ₁0, x⟩, hσ₂0, hσ₁0, hx⟩
  · obtain ⟨h1, h2, e1, e2⟩ := hcase1 hc
    have hpo := (hL1b hc).1
    refine ⟨hpo, by rw [e1]; exact h1, by rw [e1, e2]; exact h2, fun r s ⟨hs, hbr, hopt⟩ => ⟨fun hr => ?_,
      fun hr1 hr2 => ?_⟩⟩
    · exact ⟨hR1 s.σ₂ s.σ₁ hs hbr r s.w hopt hr, (hzone s.σ₂ s.σ₁ hs hbr).1 _ le_rfl, s2A s.σ₂ hs⟩
    · have hwl : wNo P < wNe P := by rw [hwNo, e1]; linarith
      exact ⟨hR2 s.σ₂ s.σ₁ hs hbr r s.w hopt hc hr1 hr2, (hzone s.σ₂ s.σ₁ hs hbr).2.1 _ le_rfl hwl,
        s2B s.σ₂ hs hc⟩
  · obtain ⟨e1, e2⟩ := hcase2 hc
    refine ⟨(hL1c hc).1, e1.symm, by rw [e1, e2], fun r s ⟨hs, hbr, hopt⟩ hr => ?_⟩
    exact ⟨hR1 s.σ₂ s.σ₁ hs hbr r s.w hopt hr, (hzone s.σ₂ s.σ₁ hs hbr).1 _ le_rfl, s2A s.σ₂ hs⟩
  · unfold Trades
    constructor
    · intro h; by_contra hc; push Not at hc; exact h (hR3 s.σ₂ s.σ₁ hs hbr r s.w hopt hc)
    · intro h
      by_cases hr : rNe P ≤ r
      · rw [hR1 s.σ₂ s.σ₁ hs hbr r s.w hopt hr, (vA s.σ₂ s.σ₁ hs hbr r).2]; simp
      · push Not at hr
        have hr2 : rNo P ≤ r := by
          by_contra hc; push Not at hc; exact absurd h (not_le.mpr (lt_min hr hc))
        have hc : P.cp < cpLow P := by
          by_contra hc
          obtain ⟨e1, e2⟩ := hcase2 (not_lt.mp hc)
          have := (hL1c (not_lt.mp hc)).1
          rw [hrNo] at hr2; rw [e2] at hr; linarith
        rw [hR2 s.σ₂ s.σ₁ hs hbr r s.w hopt hc hr2 hr, (vB s.σ₂ s.σ₁ hs hbr hc r).2]; simp
