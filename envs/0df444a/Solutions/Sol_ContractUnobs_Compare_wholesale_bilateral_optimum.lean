-- Prove2me | solution 1 for ContractUnobs.Compare.wholesale_bilateral_optimum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:27:16.698813+00:00
-- url     : https://prove2.me/submissions/6f2bae9a-12c8-47e2-81e7-076481b16fe5

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

lemma opt_accept (θ pt : ℝ) (C : Contract) (a : Action) (hopt : RetailerOptimal θ pt C a)
    (b : Action) (hb : b.Feasible) (hba : b.accept = true) (h0 : 0 ≤ conjProfit θ pt C b) :
    a.accept = true := by
  by_contra h
  have h' : a.accept = false := by simpa using h
  have := hopt.2.2 h' b hb hba
  linarith

lemma opt_nonneg (θ pt : ℝ) (C : Contract) (a : Action) (hopt : RetailerOptimal θ pt C a) :
    0 ≤ conjProfit θ pt C a := by
  have := hopt.2.1 ⟨false, 0, 0⟩ ⟨le_refl _, le_refl _⟩
  rw [conj_rej θ pt C ⟨false, 0, 0⟩ rfl] at this
  exact this

lemma opt_char (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) (a : Action) (hopt : RetailerOptimal θ pt C a)
    (hacc : a.accept = true) :
    a.p = (1 + θ * pt) / (2 + 2 * θ) + C.w / 2 ∧
    (a.Q = demand θ a.p pt ∨ (C.w = 0 ∧ demand θ a.p pt ≤ a.Q)) ∧
    conjProfit θ pt C a = (1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K := by
  obtain ⟨a0, ha0, ha0acc, ha0v⟩ := attain θ pt C hθ hpt hw hint
  obtain ⟨hle, hiff⟩ := conj_key θ pt C hθ hw hint a hopt.1 hacc
  have := hopt.2.1 a0 ha0
  have heq : conjProfit θ pt C a = (1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K :=
    le_antisymm hle (by linarith)
  exact ⟨(hiff.1 heq).1, (hiff.1 heq).2, heq⟩

lemma opt_wQ (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) (a : Action) (hopt : RetailerOptimal θ pt C a)
    (hacc : a.accept = true) :
    C.w * a.Q = C.w * ((1 + θ * pt - (1 + θ) * C.w) / 2) := by
  have hs : 0 < 1 + θ := by linarith
  obtain ⟨hp, hQ, _⟩ := opt_char θ pt hθ hpt C hw hint a hopt hacc
  have hD : demand θ a.p pt = (1 + θ * pt - (1 + θ) * C.w) / 2 := by
    rw [dem_eq, hp]; field_simp; ring
  rcases hQ with h | ⟨h, _⟩
  · rw [h, hD]
  · rw [h]; simp

lemma tar_bil (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (a : Action)
    (hopt : RetailerOptimal θ pt C a) :
    bilateral C a ≤ (1 + θ * pt) ^ 2 / (4 * (1 + θ)) ∧
    (bilateral C a = (1 + θ * pt) ^ 2 / (4 * (1 + θ)) →
      a.accept = true ∧ a.p = (1 + θ * pt) / (2 * (1 + θ)) ∧ demand θ a.p pt ≤ a.Q ∧
        C.w * a.Q + C.K = (1 + θ * pt) ^ 2 / (4 * (1 + θ))) := by
  have hs : 0 < 1 + θ := by linarith
  have hApos : 0 < 1 + θ * pt := by nlinarith [mul_nonneg hθ hpt]
  have hVpos : 0 < (1 + θ * pt) ^ 2 / (4 * (1 + θ)) := by positivity
  cases hacc : a.accept
  · have : bilateral C a = 0 := by simp [bilateral, hacc]
    rw [this]
    exact ⟨hVpos.le, fun h => absurd h hVpos.ne⟩
  · have hb : bilateral C a = C.w * a.Q + C.K := by simp [bilateral, hacc]
    have h0 := opt_nonneg θ pt C a hopt
    rw [conj_acc θ pt C a hacc] at h0
    have hD := dem_eq θ a.p pt
    have hp := hopt.1.1
    have hQ := hopt.1.2
    generalize demand θ a.p pt = D at hD h0 ⊢
    have hmn : min a.Q (max 0 D) ≤ max 0 D := min_le_right _ _
    have h1 : a.p * min a.Q (max 0 D) ≤ a.p * max 0 D := mul_le_mul_of_nonneg_left hmn hp
    have hid : (1 + θ * pt) ^ 2 / (4 * (1 + θ)) - a.p * ((1 + θ * pt) - (1 + θ) * a.p)
        = (1 + θ) * (a.p - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 := by
      field_simp; ring
    have hsq : 0 ≤ (1 + θ) * (a.p - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 := by positivity
    have h3a : a.p * max 0 D ≤ (1 + θ * pt) ^ 2 / (4 * (1 + θ)) := by
      rcases le_or_gt D 0 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h.le, hD]; linarith
    have h3b : (1 + θ * pt) ^ 2 / (4 * (1 + θ)) ≤ a.p * max 0 D →
        0 < D ∧ a.p = (1 + θ * pt) / (2 * (1 + θ)) := by
      intro hh
      rcases le_or_gt D 0 with h | h
      · rw [max_eq_left h] at hh; linarith
      · refine ⟨h, ?_⟩
        rw [max_eq_right h.le, hD] at hh
        have e : (1 + θ) * (a.p - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 = 0 := by linarith
        have e2 : (a.p - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 = 0 := by
          rcases mul_eq_zero.1 e with h | h
          · exact absurd h hs.ne'
          · exact h
        have := pow_eq_zero_iff (two_ne_zero) |>.1 e2
        linarith
    rw [hb]
    refine ⟨by linarith, ?_⟩
    intro heq
    have hv : (1 + θ * pt) ^ 2 / (4 * (1 + θ)) ≤ a.p * min a.Q (max 0 D) := by linarith
    obtain ⟨hDpos, hpq⟩ := h3b (by linarith)
    have hppos : 0 < a.p := by rw [hpq]; positivity
    have hmm : a.p * min a.Q (max 0 D) = a.p * max 0 D := by linarith
    have hmm' : min a.Q (max 0 D) = max 0 D := mul_left_cancel₀ hppos.ne' hmm
    rw [max_eq_right hDpos.le] at hmm'
    have hDQ : D ≤ a.Q := by rw [← hmm']; exact min_le_left _ _
    exact ⟨rfl, hpq, hDQ, heq⟩

lemma tar_dev (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (a : Action)
    (hopt : RetailerOptimal θ pt C a) (hw : 0 < C.w) (hacc : a.accept = true)
    (hp : a.p = (1 + θ * pt) / (2 * (1 + θ))) (hDQ : demand θ a.p pt ≤ a.Q)
    (hsum : C.w * a.Q + C.K = (1 + θ * pt) ^ 2 / (4 * (1 + θ))) : False := by
  have hs : 0 < 1 + θ := by linarith
  have hA : 0 < 1 + θ * pt := by nlinarith [mul_nonneg hθ hpt]
  have hsp0 : (1 + θ) * a.p = (1 + θ * pt) / 2 := by rw [hp]; field_simp
  have hD : demand θ a.p pt = (1 + θ * pt) / 2 := by rw [dem_eq]; linarith
  obtain ⟨t, ht1, ht2, ht3⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ C.w / 2 ∧ (1 + θ) * t ≤ (1 + θ * pt) / 4 := by
    refine ⟨min (C.w / 2) ((1 + θ * pt) / (4 * (1 + θ))), lt_min (by linarith) (by positivity),
      min_le_left _ _, ?_⟩
    have := min_le_right (C.w / 2) ((1 + θ * pt) / (4 * (1 + θ)))
    calc (1 + θ) * min (C.w / 2) ((1 + θ * pt) / (4 * (1 + θ)))
        ≤ (1 + θ) * ((1 + θ * pt) / (4 * (1 + θ))) := mul_le_mul_of_nonneg_left this hs.le
      _ = (1 + θ * pt) / 4 := by field_simp
  have hD' : demand θ (a.p + t) pt = (1 + θ * pt) / 2 - (1 + θ) * t := by
    rw [dem_eq]; linear_combination (-1) * hsp0
  have hD'pos : 0 < demand θ (a.p + t) pt := by rw [hD']; linarith
  have hp0 := hopt.1.1
  have hbf : (⟨true, a.p + t, demand θ (a.p + t) pt⟩ : Action).Feasible :=
    ⟨by show 0 ≤ a.p + t; linarith, by show 0 ≤ demand θ (a.p + t) pt; exact hD'pos.le⟩
  have h1 := hopt.2.1 _ hbf
  rw [conj_acc θ pt C _ rfl] at h1
  rw [conj_acc θ pt C a hacc] at h1
  simp only [] at h1
  rw [max_eq_right hD'pos.le, min_self, hD, max_eq_right (by linarith : (0:ℝ) ≤ (1 + θ * pt) / 2),
    min_eq_right (by rw [hD] at hDQ; exact hDQ)] at h1
  have hpD : a.p * ((1 + θ * pt) / 2) = (1 + θ * pt) ^ 2 / (4 * (1 + θ)) := by
    rw [hp]; field_simp; ring
  have hwQ : C.w * ((1 + θ * pt) / 2) ≤ C.w * a.Q := by
    apply mul_le_mul_of_nonneg_left _ hw.le
    rw [hD] at hDQ; exact hDQ
  have key : (a.p + t - C.w) * ((1 + θ * pt) / 2 - (1 + θ) * t) - (a.p - C.w) * ((1 + θ * pt) / 2)
      = (1 + θ) * t * (C.w - t) := by linear_combination (-t) * hsp0
  have hpos : 0 < (1 + θ) * t * (C.w - t) := by
    have : 0 < C.w - t := by linarith
    positivity
  rw [hD'] at h1
  nlinarith

theorem tariff_opt (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (σ : Contract → Action)
    (hσ : ∀ C ∈ tariffClass, RetailerOptimal θ pt C (σ C)) :
    IsGreatest ((fun C => bilateral C (σ C)) '' tariffClass)
        ((1 + θ * pt) ^ 2 / (4 * (1 + θ))) ∧
      ∀ C ∈ tariffClass, bilateral C (σ C) = (1 + θ * pt) ^ 2 / (4 * (1 + θ)) →
        C = ⟨(1 + θ * pt) ^ 2 / (4 * (1 + θ)), 0⟩ := by
  have hs : 0 < 1 + θ := by linarith
  have hA : 0 < 1 + θ * pt := by nlinarith [mul_nonneg hθ hpt]
  have hC0 : (⟨(1 + θ * pt) ^ 2 / (4 * (1 + θ)), 0⟩ : Contract) ∈ tariffClass := by
    show (0 : ℝ) ≤ 0
    exact le_refl _
  refine ⟨⟨⟨_, hC0, ?_⟩, ?_⟩, ?_⟩
  · have hopt := hσ _ hC0
    obtain ⟨a0, ha0, ha0acc, ha0v⟩ := attain θ pt ⟨(1 + θ * pt) ^ 2 / (4 * (1 + θ)), 0⟩ hθ hpt
      (le_refl _) (by simp; exact hA)
    have h0 : 0 ≤ conjProfit θ pt ⟨(1 + θ * pt) ^ 2 / (4 * (1 + θ)), 0⟩ a0 := by
      rw [ha0v]; simp
    have hacc := opt_accept θ pt _ _ hopt a0 ha0 ha0acc h0
    simp [bilateral, hacc]
  · rintro _ ⟨C, hC, rfl⟩
    exact (tar_bil θ pt hθ hpt C (σ C) (hσ C hC)).1
  · intro C hC hbil
    have hopt := hσ C hC
    obtain ⟨hacc, hp, hDQ, hsum⟩ := (tar_bil θ pt hθ hpt C (σ C) hopt).2 hbil
    have hw0 : C.w = 0 := by
      by_contra hne
      have hwpos : 0 < C.w := lt_of_le_of_ne hC (Ne.symm hne)
      exact tar_dev θ pt hθ hpt C (σ C) hopt hwpos hacc hp hDQ hsum
    obtain ⟨K, w⟩ := C
    simp only [] at hw0 hsum
    subst hw0
    simp only [Contract.mk.injEq, and_true]
    linarith

lemma wh_bil (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hK : C.K = 0)
    (hw : 0 ≤ C.w) (a : Action) (hopt : RetailerOptimal θ pt C a) :
    bilateral C a ≤ (1 + θ * pt) ^ 2 / (8 * (1 + θ)) ∧
    (bilateral C a = (1 + θ * pt) ^ 2 / (8 * (1 + θ)) → C.w = (1 + θ * pt) / (2 * (1 + θ))) := by
  have hs : 0 < 1 + θ := by linarith
  have hApos : 0 < 1 + θ * pt := by nlinarith [mul_nonneg hθ hpt]
  have hVpos : 0 < (1 + θ * pt) ^ 2 / (8 * (1 + θ)) := by positivity
  cases hacc : a.accept
  · have : bilateral C a = 0 := by simp [bilateral, hacc]
    rw [this]
    exact ⟨hVpos.le, fun h => absurd h hVpos.ne⟩
  · have hb : bilateral C a = C.w * a.Q := by simp [bilateral, hacc, hK]
    rw [hb]
    by_cases hint : (1 + θ) * C.w < 1 + θ * pt
    · rw [opt_wQ θ pt hθ hpt C hw hint a hopt hacc]
      have hid : (1 + θ * pt) ^ 2 / (8 * (1 + θ)) - C.w * ((1 + θ * pt - (1 + θ) * C.w) / 2)
          = (1 + θ) / 2 * (C.w - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 := by
        field_simp; ring
      have hsq : 0 ≤ (1 + θ) / 2 * (C.w - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 := by positivity
      refine ⟨by linarith, ?_⟩
      intro heq
      have e : (1 + θ) / 2 * (C.w - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 = 0 := by linarith
      have e2 : (C.w - (1 + θ * pt) / (2 * (1 + θ))) ^ 2 = 0 := by
        rcases mul_eq_zero.1 e with h | h
        · exact absurd h (by positivity)
        · exact h
      have := pow_eq_zero_iff (two_ne_zero) |>.1 e2
      linarith
    · have hnint : 1 + θ * pt ≤ (1 + θ) * C.w := not_lt.1 hint
      have h0 := opt_nonneg θ pt C a hopt
      rw [conj_acc θ pt C a hacc, hK] at h0
      have hD := dem_eq θ a.p pt
      have hp := hopt.1.1
      have hQ := hopt.1.2
      generalize demand θ a.p pt = D at hD h0
      have hwQ : C.w * a.Q ≤ 0 := by
        rcases le_or_gt D 0 with h | h
        · rw [max_eq_left h, min_eq_right hQ] at h0
          linarith
        · rw [max_eq_right h.le] at h0
          have hmn : min a.Q D ≤ a.Q := min_le_left _ _
          have h1 : a.p * min a.Q D ≤ a.p * a.Q := mul_le_mul_of_nonneg_left hmn hp
          by_contra hcon
          have hQpos : 0 < a.Q := by
            rcases lt_or_eq_of_le hQ with h' | h'
            · exact h'
            · rw [← h'] at hcon; simp at hcon
          have hpw : a.p < C.w := by
            by_contra hh
            have : C.w ≤ a.p := not_lt.1 hh
            nlinarith [mul_le_mul_of_nonneg_left this hs.le]
          nlinarith [mul_pos (sub_pos.2 hpw) hQpos]
      refine ⟨by linarith, ?_⟩
      intro heq
      linarith

theorem wholesale_opt (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt)
    (σ : Contract → Action) (hσ : ∀ C ∈ wholesaleClass, RetailerOptimal θ pt C (σ C)) :
    IsGreatest ((fun C => bilateral C (σ C)) '' wholesaleClass)
        ((1 + θ * pt) ^ 2 / (8 * (1 + θ))) ∧
      ∀ C ∈ wholesaleClass, bilateral C (σ C) = (1 + θ * pt) ^ 2 / (8 * (1 + θ)) →
        C = ⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ := by
  have hs : 0 < 1 + θ := by linarith
  have hA : 0 < 1 + θ * pt := by nlinarith [mul_nonneg hθ hpt]
  have hw0 : 0 < (1 + θ * pt) / (2 * (1 + θ)) := by positivity
  have hC0 : (⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ : Contract) ∈ wholesaleClass :=
    ⟨rfl, hw0.le⟩
  refine ⟨⟨⟨_, hC0, ?_⟩, ?_⟩, ?_⟩
  · have hopt := hσ _ hC0
    have hsw : (1 + θ) * ((1 + θ * pt) / (2 * (1 + θ))) = (1 + θ * pt) / 2 := by
      field_simp
    have hint : (1 + θ) * (⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ : Contract).w
        < 1 + θ * pt := by
      show (1 + θ) * ((1 + θ * pt) / (2 * (1 + θ))) < 1 + θ * pt
      rw [hsw]; linarith
    have hsw2 : 1 + θ * pt - (1 + θ) * ((1 + θ * pt) / (2 * (1 + θ))) = (1 + θ * pt) / 2 := by
      rw [hsw]; ring
    obtain ⟨a0, ha0, ha0acc, ha0v⟩ := attain θ pt ⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ hθ hpt
      hw0.le hint
    have h0 : 0 ≤ conjProfit θ pt ⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ a0 := by
      rw [ha0v]
      show 0 ≤ (1 + θ * pt - (1 + θ) * ((1 + θ * pt) / (2 * (1 + θ)))) ^ 2 / (4 * (1 + θ)) - 0
      rw [hsw2, sub_zero]; positivity
    have hacc := opt_accept θ pt _ _ hopt a0 ha0 ha0acc h0
    have hwQ := opt_wQ θ pt hθ hpt _ hw0.le hint _ hopt hacc
    simp only [bilateral, hacc, if_true]
    simp only [] at hwQ ⊢
    rw [add_zero, hwQ]
    rw [hsw2]
    field_simp
    ring
  · rintro _ ⟨C, hC, rfl⟩
    exact (wh_bil θ pt hθ hpt C hC.1 hC.2 (σ C) (hσ C hC)).1
  · intro C hC hbil
    have := (wh_bil θ pt hθ hpt C hC.1 hC.2 (σ C) (hσ C hC)).2 hbil
    obtain ⟨K, w⟩ := C
    have hK : K = 0 := hC.1
    simp only [] at this hK
    subst hK; subst this
    rfl
theorem solution (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt)
    (σ : Contract → Action) (hσ : ∀ C ∈ wholesaleClass, RetailerOptimal θ pt C (σ C)) :
    IsGreatest ((fun C => bilateral C (σ C)) '' wholesaleClass)
        ((1 + θ * pt) ^ 2 / (8 * (1 + θ))) ∧
      ∀ C ∈ wholesaleClass, bilateral C (σ C) = (1 + θ * pt) ^ 2 / (8 * (1 + θ)) →
        C = ⟨0, (1 + θ * pt) / (2 * (1 + θ))⟩ :=
  wholesale_opt θ pt hθ hpt σ hσ
