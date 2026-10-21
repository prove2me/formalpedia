-- Prove2me | solution 1 for ContractUnobs.Compare.equation_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:19:50.583979+00:00
-- url     : https://prove2.me/submissions/d151c829-e371-4145-bddc-9ee7ad274acb

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

set_option autoImplicit false
open ContractUnobs.Compare

lemma dem_eq (θ p pt : ℝ) : demand θ p pt = (1 + θ * pt) - (1 + θ) * p := by
  unfold demand; ring

lemma conj_acc (θ pt : ℝ) (C : Contract) (a : Action) (h : a.accept = true) :
    conjProfit θ pt C a = a.p * min a.Q (max 0 (demand θ a.p pt)) - C.w * a.Q - C.K := by
  simp [conjProfit, sales, h]

lemma conj_rej (θ pt : ℝ) (C : Contract) (a : Action) (h : a.accept = false) :
    conjProfit θ pt C a = 0 := by
  simp [conjProfit, h]

lemma core (A s w p Q D : ℝ) (hs : 0 < s) (hw : 0 ≤ w) (hint : s * w < A) (hp : 0 ≤ p)
    (hQ : 0 ≤ Q) (hD : D = A - s * p) :
    p * min Q (max 0 D) - w * Q ≤ (A - s * w) ^ 2 / (4 * s) ∧
    (p * min Q (max 0 D) - w * Q = (A - s * w) ^ 2 / (4 * s) ↔
      (p = A / (2 * s) + w / 2 ∧ (Q = D ∨ (w = 0 ∧ D ≤ Q)))) := by
  have hV : (p - w) * (A - s * p) + s * (p - (A / (2 * s) + w / 2)) ^ 2
      = (A - s * w) ^ 2 / (4 * s) := by
    field_simp
    ring
  have hV' : (p - w) * D + s * (p - (A / (2 * s) + w / 2)) ^ 2
      = (A - s * w) ^ 2 / (4 * s) := by rw [hD]; exact hV
  have hAw : 0 < A - s * w := by linarith
  have hVpos : 0 < (A - s * w) ^ 2 / (4 * s) := by
    apply div_pos
    · positivity
    · linarith
  have hsq : 0 ≤ s * (p - (A / (2 * s) + w / 2)) ^ 2 := by positivity
  rcases le_or_gt D 0 with hD0 | hD0
  · have h1 : max 0 D = 0 := max_eq_left hD0
    have h2 : min Q 0 = 0 := min_eq_right hQ
    rw [h1, h2]
    have hwQ : 0 ≤ w * Q := mul_nonneg hw hQ
    refine ⟨by nlinarith, ?_⟩
    constructor
    · intro h; nlinarith
    · rintro ⟨hp1, _⟩
      exfalso
      have : D = (A - s * w) / 2 := by rw [hD, hp1]; field_simp; ring
      linarith
  · have h1 : max 0 D = D := max_eq_right hD0.le
    rw [h1]
    have hm1 : min Q D ≤ Q := min_le_left _ _
    have hm2 : min Q D ≤ D := min_le_right _ _
    have hm0 : 0 ≤ min Q D := le_min hQ hD0.le
    have hwm : w * min Q D ≤ w * Q := mul_le_mul_of_nonneg_left hm1 hw
    have hle1 : p * min Q D - w * Q ≤ (p - w) * min Q D := by nlinarith
    have hpos : ∀ h : w < p, (p - w) * min Q D ≤ (p - w) * D := fun h =>
      mul_le_mul_of_nonneg_left hm2 (by linarith)
    have hneg : ¬ (w < p) → (p - w) * min Q D ≤ 0 := fun h => by
      have := not_lt.1 h
      nlinarith [mul_nonneg (sub_nonneg.2 this) hm0]
    refine ⟨?_, ?_⟩
    · by_cases hpw : w < p
      · linarith [hpos hpw]
      · linarith [hneg hpw]
    · constructor
      · intro h
        have hpw : w < p := by
          by_contra hh
          linarith [hneg hh]
        have hc := hpos hpw
        have e1 : s * (p - (A / (2 * s) + w / 2)) ^ 2 = 0 := by linarith
        have e1' : p = A / (2 * s) + w / 2 := by
          have h0 : (p - (A / (2 * s) + w / 2)) ^ 2 = 0 := by
            rcases mul_eq_zero.1 e1 with h | h
            · exact absurd h hs.ne'
            · exact h
          have := pow_eq_zero_iff (two_ne_zero) |>.1 h0
          linarith
        have e2 : (p - w) * min Q D = (p - w) * D := by linarith
        have e2' : min Q D = D := mul_left_cancel₀ (by linarith : p - w ≠ 0) e2
        have e3 : w * Q = w * D := by
          have : w * min Q D = w * Q := by nlinarith
          rw [e2'] at this; linarith
        have hDQ : D ≤ Q := by rw [← e2']; exact hm1
        refine ⟨e1', ?_⟩
        rcases mul_eq_zero.1 (show w * (Q - D) = 0 by linarith) with h | h
        · exact Or.inr ⟨h, hDQ⟩
        · exact Or.inl (by linarith)
      · rintro ⟨hp1, h2⟩
        have hwQ : w * Q = w * D := by
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [h2]
          · rw [h2]; simp
        have hDQ : D ≤ Q := by
          rcases h2 with h2 | ⟨_, h2⟩
          · exact h2.ge
          · exact h2
        have hmD : min Q D = D := min_eq_right hDQ
        have hz : p - (A / (2 * s) + w / 2) = 0 := by linarith
        rw [hmD, hwQ]
        have : s * (p - (A / (2 * s) + w / 2)) ^ 2 = 0 := by rw [hz]; ring
        linarith

lemma conj_key (θ pt : ℝ) (C : Contract) (hθ : 0 ≤ θ) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) (a : Action) (ha : a.Feasible) (hacc : a.accept = true) :
    conjProfit θ pt C a ≤ (1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K ∧
    (conjProfit θ pt C a = (1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K ↔
      (a.p = (1 + θ * pt) / (2 + 2 * θ) + C.w / 2 ∧
        (a.Q = demand θ a.p pt ∨ (C.w = 0 ∧ demand θ a.p pt ≤ a.Q)))) := by
  have hs : 0 < 1 + θ := by linarith
  have h2 : (2 : ℝ) + 2 * θ = 2 * (1 + θ) := by ring
  have := core (1 + θ * pt) (1 + θ) C.w a.p a.Q (demand θ a.p pt) hs hw hint ha.1 ha.2
    (dem_eq θ a.p pt)
  rw [conj_acc θ pt C a hacc, h2]
  obtain ⟨h1, h3⟩ := this
  refine ⟨by linarith, ?_⟩
  rw [← h3]
  constructor <;> intro h <;> linarith

lemma attain (θ pt : ℝ) (C : Contract) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) :
    ∃ a0 : Action, a0.Feasible ∧ a0.accept = true ∧
      conjProfit θ pt C a0 = (1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K := by
  have hs : 0 < 1 + θ := by linarith
  have hA : 0 ≤ θ * pt := mul_nonneg hθ hpt
  refine ⟨⟨true, (1 + θ * pt) / (2 + 2 * θ) + C.w / 2, demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt⟩, ?_, rfl, ?_⟩
  · have hD : demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt = (1 + θ * pt - (1 + θ) * C.w) / 2 := by
      rw [dem_eq]; field_simp; ring
    refine ⟨?_, ?_⟩
    · show 0 ≤ (1 + θ * pt) / (2 + 2 * θ) + C.w / 2
      positivity
    · show 0 ≤ demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt
      rw [hD]; linarith
  · have := (conj_key θ pt C hθ hw hint ⟨true, (1 + θ * pt) / (2 + 2 * θ) + C.w / 2,
      demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt⟩ ?_ rfl).2
    · exact this.2 ⟨rfl, Or.inl rfl⟩
    · have hD : demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt = (1 + θ * pt - (1 + θ) * C.w) / 2 := by
        rw [dem_eq]; field_simp; ring
      refine ⟨?_, ?_⟩
      · show 0 ≤ (1 + θ * pt) / (2 + 2 * θ) + C.w / 2
        positivity
      · show 0 ≤ demand θ ((1 + θ * pt) / (2 + 2 * θ) + C.w / 2) pt
        rw [hD]; linarith

theorem eq2 (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) :
    (∀ a : Action, a.Feasible → a.accept = true →
      ((∀ b : Action, b.Feasible → b.accept = true → conjProfit θ pt C b ≤ conjProfit θ pt C a) ↔
        (a.p = (1 + θ * pt) / (2 + 2 * θ) + C.w / 2 ∧
          (a.Q = demand θ a.p pt ∨ (C.w = 0 ∧ demand θ a.p pt ≤ a.Q))))) ∧
    IsGreatest (conjProfit θ pt C '' {b : Action | b.Feasible ∧ b.accept = true})
      ((1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K) := by
  obtain ⟨a0, ha0, ha0acc, ha0v⟩ := attain θ pt C hθ hpt hw hint
  refine ⟨?_, ⟨⟨a0, ⟨ha0, ha0acc⟩, ha0v⟩, ?_⟩⟩
  · intro a ha hacc
    obtain ⟨hle, hiff⟩ := conj_key θ pt C hθ hw hint a ha hacc
    constructor
    · intro hmax
      have := hmax a0 ha0 ha0acc
      exact hiff.1 (le_antisymm hle (by linarith))
    · intro h b hb hbacc
      rw [hiff.2 h]
      exact (conj_key θ pt C hθ hw hint b hb hbacc).1
  · rintro _ ⟨b, ⟨hb, hbacc⟩, rfl⟩
    exact (conj_key θ pt C hθ hw hint b hb hbacc).1
theorem solution (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) :
    (∀ a : Action, a.Feasible → a.accept = true →
      ((∀ b : Action, b.Feasible → b.accept = true → conjProfit θ pt C b ≤ conjProfit θ pt C a) ↔
        (a.p = (1 + θ * pt) / (2 + 2 * θ) + C.w / 2 ∧
          (a.Q = demand θ a.p pt ∨ (C.w = 0 ∧ demand θ a.p pt ≤ a.Q))))) ∧
    IsGreatest (conjProfit θ pt C '' {b : Action | b.Feasible ∧ b.accept = true})
      ((1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K) :=
  eq2 θ pt hθ hpt C hw hint
