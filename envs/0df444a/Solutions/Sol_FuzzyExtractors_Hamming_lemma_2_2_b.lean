-- Prove2me | solution 1 for FuzzyExtractors.Hamming.lemma_2_2_b
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:38:03.132977+00:00
-- url     : https://prove2.me/submissions/af860191-7357-409e-9fcf-4eac25ab294a

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace Lemma22bProof

noncomputable def guessingMass {M I : Type*} (P : PMF (M × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ w, P (w, i)

noncomputable def guessing {M I : Type*} (P : PMF (M × I)) : ℝ :=
  (guessingMass P).toReal

noncomputable def maxMass {M : Type*} (P : PMF M) : ℝ≥0∞ :=
  ⨆ w, P w

noncomputable def maxProb {M : Type*} (P : PMF M) : ℝ :=
  (maxMass P).toReal

theorem guessingMass_le_one {M I : Type*} (P : PMF (M × I)) : guessingMass P ≤ 1 := by
  calc
    guessingMass P ≤ ∑' i, ∑' w, P (w, i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact iSup_le fun w => ENNReal.le_tsum w
    _ = ∑' p, P p := by rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    _ = 1 := P.tsum_coe

theorem guessingMass_ne_top {M I : Type*} (P : PMF (M × I)) : guessingMass P ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (guessingMass_le_one P) ENNReal.one_lt_top)

theorem guessing_pos {M I : Type*} (P : PMF (M × I)) : 0 < guessing P := by
  obtain ⟨⟨w, i⟩, hp⟩ := P.support_nonempty
  have hpos : 0 < guessingMass P := by
    apply lt_of_lt_of_le (P.apply_pos_iff _ |>.mpr hp)
    exact (le_iSup (fun w => P (w, i)) w).trans (ENNReal.le_tsum i)
  exact ENNReal.toReal_pos hpos.ne' (guessingMass_ne_top P)

theorem maxMass_le_one {M : Type*} (P : PMF M) : maxMass P ≤ 1 :=
  iSup_le fun w => P.coe_le_one w

theorem maxMass_ne_top {M : Type*} (P : PMF M) : maxMass P ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (maxMass_le_one P) ENNReal.one_lt_top)

theorem maxProb_pos {M : Type*} (P : PMF M) : 0 < maxProb P := by
  obtain ⟨w, hw⟩ := P.support_nonempty
  have hpos : 0 < maxMass P :=
    lt_of_lt_of_le (P.apply_pos_iff w |>.mpr hw) (le_iSup (fun w => P w) w)
  exact ENNReal.toReal_pos hpos.ne' (maxMass_ne_top P)

theorem pmf_le_map_apply {X Y : Type*} (P : PMF X) (f : X → Y) (x : X) :
    P x ≤ (P.map f) (f x) := by
  rw [PMF.map_apply]
  exact le_trans (by simp) (ENNReal.le_tsum x)

theorem map_assoc_apply {α β γ : Type*} (ABC : PMF (α × β × γ)) (a : α) (b : β) (c : γ) :
    (ABC.map fun x => ((x.1, x.2.1), x.2.2)) ((a, b), c) = ABC (a, (b, c)) := by
  rw [PMF.map_apply, tsum_eq_single (a, (b, c))]
  · simp
  · rintro ⟨a', b', c'⟩ hne
    have h : ((a, b), c) ≠ ((a', b'), c') := by
      intro heq
      apply hne
      rcases Prod.mk.inj heq with ⟨hab, rfl⟩
      rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
      rfl
    simp [h]

theorem sum_ite_mem_finset {β : Type*} (T : Finset β) :
    (∑' b : β, if b ∈ T then (1 : ℝ≥0∞) else 0) = T.card := by
  rw [tsum_eq_sum (s := T)]
  · simp
  · intro b hb
    simp [hb]

theorem neg_logb_ge_sub_of_le {x y c : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hle : x ≤ (2 : ℝ) ^ c * y) :
    -Real.logb 2 x ≥ -Real.logb 2 y - c := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hpow : 0 < (2 : ℝ) ^ c := Real.rpow_pos_of_pos htwo c
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hx (mul_pos hpow hy)).mpr hle
  rw [Real.logb_mul hpow.ne' hy.ne', Real.logb_rpow htwo (by norm_num)] at hlog
  linarith

theorem neg_logb_ge_of_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hle : x ≤ y) :
    -Real.logb 2 x ≥ -Real.logb 2 y := by
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hx hy).mpr hle
  linarith

end Lemma22bProof

theorem solution {α β γ : Type} (ABC : PMF (α × β × γ)) (lam : ℝ)
    (hB : ∃ T : Finset β, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ x ∈ ABC.support, x.2.1 ∈ T) :
    (avgMinEntropy ABC ≥ avgMinEntropy (ABC.map fun x => ((x.1, x.2.1), x.2.2)) - lam ∧
      avgMinEntropy (ABC.map fun x => ((x.1, x.2.1), x.2.2)) - lam ≥
        avgMinEntropy (ABC.map fun x => (x.1, x.2.2)) - lam) ∧
    (avgMinEntropy (ABC.map fun x => (x.1, x.2.1)) ≥
        minEntropy (ABC.map fun x => (x.1, x.2.1)) - lam ∧
      minEntropy (ABC.map fun x => (x.1, x.2.1)) - lam ≥
        minEntropy (ABC.map fun x => x.1) - lam) := by
  obtain ⟨T, hTcard, hT⟩ := hB
  let P2 := ABC.map fun x => ((x.1, x.2.1), x.2.2)
  let P3 := ABC.map fun x => (x.1, x.2.2)
  let AB := ABC.map fun x => (x.1, x.2.1)
  let A := ABC.map fun x => x.1
  constructor
  · constructor
    · -- Part 1: avgMinEntropy ABC ≥ avgMinEntropy P2 - lam
      have hpoint (b : β) (c : γ) :
          (⨆ a : α, ABC (a, (b, c))) ≤
            (if b ∈ T then 1 else 0) * (⨆ p : α × β, P2 (p, c)) := by
        refine iSup_le fun a => ?_
        by_cases hb : b ∈ T
        · simp only [hb, if_true, one_mul]
          rw [← Lemma22bProof.map_assoc_apply ABC a b c]
          exact le_iSup (fun p : α × β => P2 (p, c)) (a, b)
        · have hzero : ABC (a, (b, c)) = 0 := by
            by_contra hne
            exact hb (hT (a, (b, c)) ((PMF.mem_support_iff _ _).mpr hne))
          simp [hb, hzero]
      have hmass : Lemma22bProof.guessingMass ABC ≤
          (T.card : ℝ≥0∞) * Lemma22bProof.guessingMass P2 := by
        unfold Lemma22bProof.guessingMass
        rw [ENNReal.tsum_prod']
        calc
          ∑' b : β, ∑' c : γ, ⨆ a : α, ABC (a, (b, c))
            ≤ ∑' b : β, ∑' c : γ, (if b ∈ T then 1 else 0) * (⨆ p : α × β, P2 (p, c)) :=
              ENNReal.tsum_le_tsum fun b => ENNReal.tsum_le_tsum (hpoint b)
          _ = ∑' b : β, (if b ∈ T then 1 else 0) * Lemma22bProof.guessingMass P2 := by
              refine tsum_congr fun b => ENNReal.tsum_mul_left
          _ = (T.card : ℝ≥0∞) * Lemma22bProof.guessingMass P2 := by
              rw [ENNReal.tsum_mul_right, Lemma22bProof.sum_ite_mem_finset]
      have htop : (T.card : ℝ≥0∞) * Lemma22bProof.guessingMass P2 ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (Lemma22bProof.guessingMass_ne_top P2)
      have hreal : Lemma22bProof.guessing ABC ≤ (T.card : ℝ) * Lemma22bProof.guessing P2 := by
        simpa [Lemma22bProof.guessing] using ENNReal.toReal_mono htop hmass
      have hle : Lemma22bProof.guessing ABC ≤ (2 : ℝ) ^ lam * Lemma22bProof.guessing P2 :=
        hreal.trans (mul_le_mul_of_nonneg_right hTcard (Lemma22bProof.guessing_pos P2).le)
      exact Lemma22bProof.neg_logb_ge_sub_of_le
        (Lemma22bProof.guessing_pos ABC) (Lemma22bProof.guessing_pos P2) hle
    · -- Part 2: avgMinEntropy P2 - lam ≥ avgMinEntropy P3 - lam
      have hP3 : P3 = P2.map (fun p => (p.1.1, p.2)) := by
        simp [P2, P3, PMF.map_comp, Function.comp_def]
      have hmass : Lemma22bProof.guessingMass P2 ≤ Lemma22bProof.guessingMass P3 := by
        refine ENNReal.tsum_le_tsum fun c => iSup_le fun ⟨a, b⟩ => ?_
        have hle := Lemma22bProof.pmf_le_map_apply P2 (fun p => (p.1.1, p.2)) ((a, b), c)
        rw [← hP3] at hle
        exact hle.trans (le_iSup (fun a' : α => P3 (a', c)) a)
      have hreal : Lemma22bProof.guessing P2 ≤ Lemma22bProof.guessing P3 :=
        ENNReal.toReal_mono (Lemma22bProof.guessingMass_ne_top P3) hmass
      have hlog := Lemma22bProof.neg_logb_ge_of_le
        (Lemma22bProof.guessing_pos P2) (Lemma22bProof.guessing_pos P3) hreal
      change -Real.logb 2 (Lemma22bProof.guessing P2) - lam ≥
        -Real.logb 2 (Lemma22bProof.guessing P3) - lam
      linarith
  · constructor
    · -- Part 3: avgMinEntropy AB ≥ minEntropy AB - lam
      have hpoint (b : β) :
          (⨆ a : α, AB (a, b)) ≤
            (if b ∈ T then 1 else 0) * Lemma22bProof.maxMass AB := by
        refine iSup_le fun a => ?_
        by_cases hb : b ∈ T
        · simp only [hb, if_true, one_mul]
          exact le_iSup (fun p : α × β => AB p) (a, b)
        · have hzero : AB (a, b) = 0 := by
            by_contra hne
            have hmem := (PMF.mem_support_iff _ _).mpr hne
            obtain ⟨x, hx, hxeq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
            have hb' : x.2.1 = b := congrArg Prod.snd hxeq
            exact hb (hb' ▸ hT x hx)
          simp [hb, hzero]
      have hmass : Lemma22bProof.guessingMass AB ≤
          (T.card : ℝ≥0∞) * Lemma22bProof.maxMass AB := by
        calc
          Lemma22bProof.guessingMass AB
            ≤ ∑' b : β, (if b ∈ T then 1 else 0) * Lemma22bProof.maxMass AB :=
              ENNReal.tsum_le_tsum hpoint
          _ = (T.card : ℝ≥0∞) * Lemma22bProof.maxMass AB := by
              rw [ENNReal.tsum_mul_right, Lemma22bProof.sum_ite_mem_finset]
      have htop : (T.card : ℝ≥0∞) * Lemma22bProof.maxMass AB ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (Lemma22bProof.maxMass_ne_top AB)
      have hreal : Lemma22bProof.guessing AB ≤ (T.card : ℝ) * Lemma22bProof.maxProb AB := by
        simpa [Lemma22bProof.guessing, Lemma22bProof.maxProb] using ENNReal.toReal_mono htop hmass
      have hle : Lemma22bProof.guessing AB ≤ (2 : ℝ) ^ lam * Lemma22bProof.maxProb AB :=
        hreal.trans (mul_le_mul_of_nonneg_right hTcard (Lemma22bProof.maxProb_pos AB).le)
      exact Lemma22bProof.neg_logb_ge_sub_of_le
        (Lemma22bProof.guessing_pos AB) (Lemma22bProof.maxProb_pos AB) hle
    · -- Part 4: minEntropy AB - lam ≥ minEntropy A - lam
      have hA : A = AB.map Prod.fst := by
        simp [AB, A, PMF.map_comp, Function.comp_def]
      have hmass : Lemma22bProof.maxMass AB ≤ Lemma22bProof.maxMass A := by
        refine iSup_le fun ⟨a, b⟩ => ?_
        have hle := Lemma22bProof.pmf_le_map_apply AB Prod.fst (a, b)
        rw [← hA] at hle
        exact hle.trans (le_iSup (fun a' : α => A a') a)
      have hreal : Lemma22bProof.maxProb AB ≤ Lemma22bProof.maxProb A :=
        ENNReal.toReal_mono (Lemma22bProof.maxMass_ne_top A) hmass
      have hlog := Lemma22bProof.neg_logb_ge_of_le
        (Lemma22bProof.maxProb_pos AB) (Lemma22bProof.maxProb_pos A) hreal
      change -Real.logb 2 (Lemma22bProof.maxProb AB) - lam ≥
        -Real.logb 2 (Lemma22bProof.maxProb A) - lam
      linarith
