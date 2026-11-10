-- Prove2me | solution 1 for ExponomialAssortment.FPTAS.lemma_4
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T13:09:03.447144+00:00
-- url     : https://prove2.me/submissions/433483f9-f66f-4287-83be-99a103b24f85

import Definitions.Def_ExponomialAssortment_FPTAS_DP

open scoped BigOperators
open ExponomialAssortment.FPTAS

def inst4 : Instance 2 where
  outside := 0
  price i := if i = 0 then 0 else 1
  utility _ := 0

private lemma valid_inst4 : Valid inst4 := by
  refine ⟨?_, ?_, ?_, ⟨0, rfl⟩, ?_⟩
  · intro i
    fin_cases i <;> simp [inst4]
  · simp [inst4]
  · intro i j _
    simp [inst4]
  · intro i
    simp [inst4]

private lemma roundedUtility_inst4 (i : Fin 2) :
    roundedUtility inst4 16 i = 0 := by
  unfold roundedUtility
  simp [inst4]

private lemma pmax_inst4 : pmax inst4 = 1 := by
  unfold pmax
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    fin_cases i <;> simp [inst4]
  · have hmem : (1 : ℝ) ∈ Finset.univ.image inst4.price :=
      Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    exact Finset.le_sup' (f := id) hmem

private lemma pmin_inst4 : pmin inst4 = 1 := by
  unfold pmin
  have hpos : positivePrices inst4 = {1} := by
    ext x
    simp only [positivePrices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨i, rfl⟩, hx⟩
      fin_cases i
      · simp [inst4] at hx
      · rfl
    · rintro rfl
      exact ⟨⟨1, rfl⟩, by norm_num⟩
  have hne : (positivePrices inst4).Nonempty := by
    rw [hpos]
    exact Finset.singleton_nonempty 1
  rw [dif_pos hne]
  apply le_antisymm
  · have hmem : (1 : ℝ) ∈ positivePrices inst4 := by rw [hpos]; exact Finset.mem_singleton_self 1
    exact Finset.inf'_le (f := id) hmem
  · refine Finset.le_inf' _ _ ?_
    intro y hy
    rw [hpos, Finset.mem_singleton] at hy
    rw [hy]
    rfl

private lemma Delta_inst4 : Delta inst4 16 = Real.log (1 / 2) := by
  unfold Delta
  rw [pmax_inst4, pmin_inst4]
  norm_num

private lemma kIndex_inst4 : kIndex inst4 16 1 = 0 := by
  unfold kIndex
  simp [inst4]

private lemma not_profitable_initial_inst4 :
    ¬ Profitable inst4 16 1 (initial inst4 16 1) := by
  unfold Profitable stateCoefficient initial stateGap
  have hlt : inst4.outside < (1 : Fin 2) := by decide
  simp only [hlt, ↓reduceDIte, Fin.val_one, Nat.lt_add_one, Nat.cast_one, one_mul,
    roundedUtility_inst4]
  rw [kIndex_inst4, Delta_inst4]
  simp only [Nat.cast_zero, neg_zero, zero_mul, zero_sub, sub_self, Real.exp_zero]
  intro hle
  have hlog : Real.log (1 / 2 : ℝ) ≤ 1 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hpos : (0 : ℝ) < -Real.log (1 / 2 : ℝ) := by linarith
  have hexp : (1 : ℝ) < Real.exp (-Real.log (1 / 2 : ℝ)) := Real.one_lt_exp_iff.mpr hpos
  linarith

private lemma no_prunedOptimal_inst4 (S : Finset (Fin 2)) (v : ℝ) :
    ¬ PrunedOptimal inst4 2 16 1 1 S v := by
  rintro ⟨⟨_, hfmem, T, hpath, hS⟩, _⟩
  cases hpath with
  | stop _ =>
    have hinit : initialSelection inst4 1 = {0} := by
      unfold initialSelection
      have hlt : inst4.outside < (1 : Fin 2) := by decide
      rw [if_pos hlt]
      rfl
    rw [hinit, Finset.union_empty] at hS
    subst hS
    exact absurd hfmem (by decide)
  | move _ _ _ _ _ _ _ hp _ _ =>
    exact not_profitable_initial_inst4 (hp rfl)

private lemma round_zero_iff (x : ℝ) : Round inst4 16 0 x ↔ x = 0 := by
  constructor
  · rintro ⟨_, hxge0, hmin⟩
    have h0mem : (0 : ℝ) ∈ priceGrid inst4 16 := Or.inl rfl
    have hxle0 : x ≤ 0 := hmin 0 h0mem le_rfl
    linarith
  · rintro rfl
    refine ⟨Or.inl rfl, le_rfl, ?_⟩
    intro b _ h0b
    exact h0b

private lemma prefixSet_zero_empty (S : Finset (Fin 2)) : prefixSet S 0 = ∅ := by
  ext j
  simp [prefixSet]

private lemma avgTraj_zero (S : Finset (Fin 2)) (h0 : (0 : Fin 2) ∈ S) :
    AverageTrajectory inst4 16 S (fun _ => 0) := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by fin_cases i <;> omega
  subst hi0
  rw [if_pos h0]
  simp only [Fin.val_zero, prefixSet_zero_empty, Finset.card_empty, Nat.cast_zero, zero_mul,
    zero_add, div_one]
  have hp0 : inst4.price 0 = 0 := rfl
  rw [hp0, round_zero_iff]

private lemma avgTraj_a1_eq_zero {S : Finset (Fin 2)} {a : ℕ → ℝ}
    (h0 : (0 : Fin 2) ∈ S) (ha : AverageTrajectory inst4 16 S a) : a 1 = 0 := by
  have hstep := ha.2 0 (by decide)
  rw [if_pos h0] at hstep
  simp only [Fin.val_zero, prefixSet_zero_empty, Finset.card_empty, Nat.cast_zero, zero_mul,
    zero_add, div_one] at hstep
  have hp0 : inst4.price 0 = 0 := rfl
  rw [hp0, round_zero_iff] at hstep
  exact hstep

private lemma prefixSet_univ_two : prefixSet (Finset.univ : Finset (Fin 2)) 2 = Finset.univ := by
  ext j
  simp [prefixSet]
  omega

private lemma coeff_univ_one :
    coefficient (roundedUtility inst4 16) Finset.univ 1 = 1 / 2 := by
  unfold coefficient gapSum
  have hval : (1 : Fin 2).val + 1 = 2 := rfl
  rw [hval, prefixSet_univ_two]
  simp [roundedUtility_inst4]

private lemma score_univ_eq {a : ℕ → ℝ} (ha0 : a 0 = 0) (ha1 : a 1 = 0) :
    score inst4 (roundedUtility inst4 16) Finset.univ a = 1 / 2 := by
  unfold score
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, ha0, ha1, sub_zero]
  have hp0 : inst4.price 0 = 0 := rfl
  have hp1 : inst4.price 1 = 1 := rfl
  rw [hp0, hp1, mul_zero, zero_add, mul_one, coeff_univ_one]

private lemma score_le_half {S : Finset (Fin 2)} {a : ℕ → ℝ}
    (h0 : (0 : Fin 2) ∈ S) (ha : AverageTrajectory inst4 16 S a) :
    score inst4 (roundedUtility inst4 16) S a ≤ 1 / 2 := by
  have ha0 : a 0 = 0 := ha.1
  have ha1 : a 1 = 0 := avgTraj_a1_eq_zero h0 ha
  by_cases h1 : (1 : Fin 2) ∈ S
  · have hSu : S = Finset.univ := by
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
    rw [hSu, score_univ_eq ha0 ha1]
  · have hS0 : S = {0} := by
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
    rw [hS0]
    unfold score
    rw [Finset.sum_singleton]
    have hp0 : inst4.price 0 = 0 := rfl
    simp [hp0, ha0]

private lemma roundedOptimal_inst4 :
    RoundedOptimal inst4 2 16 true Finset.univ (1 / 2) := by
  refine ⟨⟨Finset.mem_univ _, by simp⟩, ?_, ?_⟩
  · refine ⟨fun _ => 0, avgTraj_zero Finset.univ (Finset.mem_univ _), ?_⟩
    simp only [↓reduceIte]
    exact (score_univ_eq rfl rfl).symm
  · rintro S w ⟨h0S, _⟩ ⟨a, ha, rfl⟩
    simp only [↓reduceIte]
    exact score_le_half h0S ha

private lemma bestSingle_inst4 : bestSingle inst4 16 1 := by
  refine ⟨by decide, ?_⟩
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · exact le_rfl

private lemma firstProduct_inst4 : firstProduct inst4 Finset.univ 1 := by
  refine ⟨Finset.mem_univ _, by decide, ?_⟩
  intro j _ hj
  fin_cases j
  · exact absurd rfl hj
  · exact le_rfl

theorem solution : ¬ (∀ (n : ℕ) (I : Instance n) (_hI : Valid I) (C : ℕ)
    (_hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (_hη : 0 < η) (_hp : ∃ i, 0 < I.price i)
    (l f : Fin n) (_hl : bestSingle I η l)
    (T : Finset (Fin n)) (w : ℝ) (_hT : RoundedOptimal I C η true T w)
    (_hf : firstProduct I T f),
    (∃ S v, PrunedOptimal I C η l f S v) ∧
    ∀ S v, PrunedOptimal I C η l f S v →
      RoundedScore I η true S v ∧ (1 - η) * w ≤ v) := by
  intro hall
  have hC : 1 ≤ (2 : ℕ) ∧ (2 : ℕ) ≤ 2 := ⟨by decide, by decide⟩
  have hη : (0 : ℝ) < 16 := by norm_num
  have hp : ∃ i : Fin 2, 0 < inst4.price i := ⟨1, by simp [inst4]⟩
  rcases (hall 2 inst4 valid_inst4 2 hC 16 hη hp 1 1 bestSingle_inst4
    Finset.univ (1 / 2) roundedOptimal_inst4 firstProduct_inst4).1 with ⟨S, v, hpo⟩
  exact no_prunedOptimal_inst4 S v hpo
