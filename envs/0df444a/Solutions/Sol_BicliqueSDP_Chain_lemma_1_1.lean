-- Prove2me | solution 1 for BicliqueSDP.Chain.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:30:20.775988+00:00
-- url     : https://prove2.me/submissions/60964e5b-b533-4370-b2f4-582e4b45d6b5

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

set_option autoImplicit false

namespace BicliqueSDP.Chain.Research

lemma sqrt_product_le_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (a - b)]

lemma quotient_le_sqrt_product (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b / (a + b) ≤ (1 / 2) * Real.sqrt (a * b) := by
  by_cases hs : a + b = 0
  · simp [hs, Real.sqrt_nonneg]
  · have hspos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    apply (div_le_iff₀ hspos).mpr
    have hr := Real.sqrt_nonneg (a * b)
    have hrsq := Real.sq_sqrt (mul_nonneg ha hb)
    have hsum := sqrt_product_le_sum a b ha hb
    nlinarith [mul_le_mul_of_nonneg_left hsum hr]

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
variable (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)]

lemma alpha_nonneg : 0 ≤ alpha E := by
  simpa [alpha] using
    (Finset.le_sup' (fun p : Finset V1 × Finset V2 => (p.1.card : ℝ) + p.2.card)
      (empty_mem_pairs E))

lemma g_nonneg : 0 ≤ g E := by
  simpa [g] using
    (Finset.le_sup' (fun p : Finset V1 × Finset V2 => (p.1.card : ℝ) * p.2.card)
      (empty_mem_pairs E))

lemma card_sum_le_alpha (p : Finset V1 × Finset V2) (hp : p ∈ pairs E) :
    (p.1.card : ℝ) + p.2.card ≤ alpha E := by
  exact Finset.le_sup' (fun p => (p.1.card : ℝ) + p.2.card) hp

lemma card_product_le_g (p : Finset V1 × Finset V2) (hp : p ∈ pairs E) :
    (p.1.card : ℝ) * p.2.card ≤ g E := by
  exact Finset.le_sup' (fun p => (p.1.card : ℝ) * p.2.card) hp

lemma h_le_half_sqrt_g : h E ≤ (1 / 2) * Real.sqrt (g E) := by
  apply Finset.sup'_le
  intro p hp
  calc
    ((p.1.card : ℝ) * p.2.card) / ((p.1.card : ℝ) + p.2.card) ≤
        (1 / 2) * Real.sqrt ((p.1.card : ℝ) * p.2.card) :=
      quotient_le_sqrt_product _ _ (by positivity) (by positivity)
    _ ≤ (1 / 2) * Real.sqrt (g E) := by
      gcongr
      exact card_product_le_g E p hp

lemma half_sqrt_g_le_quarter_alpha : (1 / 2) * Real.sqrt (g E) ≤ (1 / 4) * alpha E := by
  have hg : g E ≤ (alpha E / 2) ^ 2 := by
    apply Finset.sup'_le
    intro p hp
    have ha : 0 ≤ (p.1.card : ℝ) := by positivity
    have hb : 0 ≤ (p.2.card : ℝ) := by positivity
    have hs := card_sum_le_alpha E p hp
    have hsq := sq_le_sq₀ (add_nonneg ha hb) (alpha_nonneg E) |>.mpr hs
    nlinarith [sq_nonneg ((p.1.card : ℝ) - p.2.card)]
  have hsqrt : Real.sqrt (g E) ≤ alpha E / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity [alpha_nonneg E], hg⟩
  linarith

lemma tight_sqrt_implies_alpha_bal
    (heq : (1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E) :
    alpha E ≤ alphaBal E := by
  obtain ⟨p, hp, hpval⟩ :=
    Finset.exists_mem_eq_sup' ⟨_, empty_mem_pairs E⟩
      (fun p : Finset V1 × Finset V2 => (p.1.card : ℝ) * p.2.card)
  change g E = (p.1.card : ℝ) * p.2.card at hpval
  have ha : 0 ≤ (p.1.card : ℝ) := by positivity
  have hb : 0 ≤ (p.2.card : ℝ) := by positivity
  have hs := card_sum_le_alpha E p hp
  have hsq := sq_le_sq₀ (add_nonneg ha hb) (alpha_nonneg E) |>.mpr hs
  have hgsq := Real.sq_sqrt (g_nonneg E)
  have hsqrt : Real.sqrt (g E) = alpha E / 2 := by linarith
  rw [hsqrt, hpval] at hgsq
  have heqcard : (p.1.card : ℝ) = p.2.card := by nlinarith [sq_nonneg ((p.1.card : ℝ) - p.2.card)]
  have hpbal : p ∈ balPairs E := by
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_⟩
    exact_mod_cast heqcard
  have hsum : alpha E = (p.1.card : ℝ) + p.2.card := by
    have hr : Real.sqrt (g E) = (p.1.card : ℝ) := by
      rw [hpval, ← heqcard, Real.sqrt_mul_self ha]
    linarith
  rw [hsum]
  exact Finset.le_sup' (fun p => (p.1.card : ℝ) + p.2.card) hpbal

end BicliqueSDP.Chain.Research


namespace BicliqueSDP.Chain.Research

noncomputable section

variable {V1 V2 : Type} [Fintype V1] [Fintype V2]
  [DecidableEq V1] [DecidableEq V2]
variable (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)]

theorem balanced_harmonic (x : ℝ) : (x * x) / (x + x) = x / 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxx : x + x ≠ 0 := by simpa [← two_mul] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx
    field_simp
    ring

theorem balanced_common_max :
    ∃ p ∈ balPairs E,
      alphaBal E = 2 * (p.1.card : ℝ) ∧
      gBal E = (p.1.card : ℝ) ^ 2 ∧
      hBal E = (p.1.card : ℝ) / 2 := by
  obtain ⟨p, hp, hpa⟩ := Finset.exists_mem_eq_sup'
    (s := balPairs E) ⟨_, empty_mem_balPairs E⟩
    (fun p => (p.1.card : ℝ) + p.2.card)
  have hbalp : p.1.card = p.2.card := (Finset.mem_filter.mp hp).2
  have halpha : alphaBal E = 2 * (p.1.card : ℝ) := by
    change alphaBal E = _ at hpa
    rw [← hbalp] at hpa
    linarith
  have hmax (q : Finset V1 × Finset V2) (hq : q ∈ balPairs E) :
      (q.1.card : ℝ) ≤ p.1.card := by
    have hbalq : q.1.card = q.2.card := (Finset.mem_filter.mp hq).2
    have hqalpha : (q.1.card : ℝ) + q.2.card ≤ alphaBal E :=
      Finset.le_sup' (fun q => (q.1.card : ℝ) + q.2.card) hq
    rw [halpha, ← hbalq] at hqalpha
    linarith
  refine ⟨p, hp, halpha, ?_, ?_⟩
  · apply le_antisymm
    · apply Finset.sup'_le
      intro q hq
      have hbalq : q.1.card = q.2.card := (Finset.mem_filter.mp hq).2
      rw [← hbalq]
      have hqnonneg : (0 : ℝ) ≤ q.1.card := Nat.cast_nonneg _
      have hpnonneg : (0 : ℝ) ≤ p.1.card := Nat.cast_nonneg _
      have hqp := hmax q hq
      nlinarith
    · have hpgle : (p.1.card : ℝ) * p.2.card ≤ gBal E :=
        Finset.le_sup' (fun q => (q.1.card : ℝ) * q.2.card) hp
      rw [← hbalp] at hpgle
      nlinarith
  · apply le_antisymm
    · apply Finset.sup'_le
      intro q hq
      have hbalq : q.1.card = q.2.card := (Finset.mem_filter.mp hq).2
      rw [← hbalq, balanced_harmonic]
      exact div_le_div_of_nonneg_right (hmax q hq) (by norm_num)
    · have hphle : ((p.1.card : ℝ) * p.2.card) /
          ((p.1.card : ℝ) + p.2.card) ≤ hBal E :=
        Finset.le_sup' (fun q => ((q.1.card : ℝ) * q.2.card) /
          ((q.1.card : ℝ) + q.2.card)) hp
      rwa [← hbalp, balanced_harmonic] at hphle

theorem balanced_identities :
    (1 / 4 : ℝ) * alphaBal E = (1 / 2 : ℝ) * Real.sqrt (gBal E) ∧
    (1 / 2 : ℝ) * Real.sqrt (gBal E) = hBal E := by
  obtain ⟨p, _, ha, hg, hh⟩ := balanced_common_max E
  rw [ha, hg, hh, Real.sqrt_sq (Nat.cast_nonneg _)]
  constructor <;> ring

theorem alphaBal_le_alpha : alphaBal E ≤ alpha E := by
  apply Finset.sup'_le
  intro p hp
  have hp' : p ∈ pairs E := (Finset.mem_filter.mp hp).1
  exact Finset.le_sup' (fun p => (p.1.card : ℝ) + p.2.card)
    hp'

theorem hBal_le_h : hBal E ≤ h E := by
  apply Finset.sup'_le
  intro p hp
  have hp' : p ∈ pairs E := (Finset.mem_filter.mp hp).1
  exact Finset.le_sup' (fun p => ((p.1.card : ℝ) * p.2.card) /
    ((p.1.card : ℝ) + p.2.card)) hp'

end

end BicliqueSDP.Chain.Research


open BicliqueSDP.Chain

/-- Lemma 1.1: the extremal combinatorial chain and its equality cases. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    ((1 / 4) * alphaBal E = (1 / 2) * Real.sqrt (gBal E) ∧
      (1 / 2) * Real.sqrt (gBal E) = hBal E ∧ hBal E ≤ h E ∧
      h E ≤ (1 / 2) * Real.sqrt (g E) ∧ (1 / 2) * Real.sqrt (g E) ≤ (1 / 4) * alpha E) ∧
    ((h E = (1 / 4) * alpha E ↔ (1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E) ∧
      ((1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E ↔ alpha E = alphaBal E)) := by
  have hbalanced := Research.balanced_identities E
  have hbalanced_le := Research.hBal_le_h E
  have hh := Research.h_le_half_sqrt_g E
  have hg := Research.half_sqrt_g_le_quarter_alpha E
  have hab := Research.alphaBal_le_alpha E
  have htight : (1 / 2) * Real.sqrt (g E) = (1 / 4) * alpha E ↔
      alpha E = alphaBal E := by
    constructor
    · intro heq
      exact le_antisymm (Research.tight_sqrt_implies_alpha_bal E heq) hab
    · intro heq
      linarith [hbalanced.1, hbalanced.2]
  refine ⟨⟨hbalanced.1, hbalanced.2, hbalanced_le, hh, hg⟩, ⟨?_, htight⟩⟩
  constructor
  · intro heq
    linarith
  · intro heq
    have hbal := htight.mp heq
    linarith [hbalanced.1, hbalanced.2]
