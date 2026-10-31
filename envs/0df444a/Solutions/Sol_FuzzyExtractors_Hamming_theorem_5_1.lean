-- Prove2me | solution 1 for FuzzyExtractors.Hamming.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:24:25.327893+00:00
-- url     : https://prove2.me/submissions/c6e5174d-325e-4f3f-8d71-98a14a1611c6

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace Thm51Proof

noncomputable def guessingMass {M I : Type*} (P : PMF (M × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ w, P (w, i)

noncomputable def guessing {M I : Type*} (P : PMF (M × I)) : ℝ :=
  (guessingMass P).toReal

variable {M I : Type*}

theorem guessingMass_le_one (P : PMF (M × I)) : guessingMass P ≤ 1 := by
  calc
    guessingMass P ≤ ∑' i, ∑' w, P (w, i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact iSup_le fun w => ENNReal.le_tsum w
    _ = ∑' p, P p := by rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    _ = 1 := P.tsum_coe

theorem guessingMass_ne_top (P : PMF (M × I)) : guessingMass P ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (guessingMass_le_one P) ENNReal.one_lt_top)

theorem guessing_pos (P : PMF (M × I)) : 0 < guessing P := by
  obtain ⟨⟨w, i⟩, hp⟩ := P.support_nonempty
  have hpos : 0 < guessingMass P := by
    apply lt_of_lt_of_le (P.apply_pos_iff _ |>.mpr hp)
    exact (le_iSup (fun w => P (w, i)) w).trans (ENNReal.le_tsum i)
  exact ENNReal.toReal_pos hpos.ne' (guessingMass_ne_top P)

theorem avgMinEntropy_eq_neg_log_guessing (P : PMF (M × I)) :
    avgMinEntropy P = -Real.logb 2 (guessing P) := rfl

variable {F : Type} [DecidableEq F] [AddCommGroup F] {n : ℕ}

omit [AddCommGroup F] in
theorem code_unique (C : Finset (Fin n → F)) (t : ℕ)
    (hd : MinDistGe C (2 * t + 1)) : IsCode hammingDist C t := by
  intro y c hc c' hc' h h'
  by_contra hne
  have hl := hd c hc c' hc' hne
  have hu := hammingDist_triangle_left c c' y
  omega

theorem decode_eq {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ)
    (hcode : IsCode dis C t) (y c : M) (hc : c ∈ C) (hy : dis y c ≤ t) :
    decodeWithin dis C t y = c := by
  have he : ∃ a ∈ C, dis y a ≤ t := ⟨c, hc, hy⟩
  rw [decodeWithin, dif_pos he]
  exact hcode y _ he.choose_spec.1 c hc he.choose_spec.2 hy

theorem offset_correct (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ)
    (hd : MinDistGe C (2 * t + 1)) :
    SketchCorrect hammingDist t (codeOffsetSS C hC) (codeOffsetRec C t) := by
  intro w w' hw s hs
  obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hs
  have hc' : c ∈ C := (PMF.mem_support_uniformOfFinset_iff hC c).1 hc
  have he : hammingDist (w' - (w - c)) c = hammingDist w' w := by
    rw [hammingDist_eq_hammingNorm, hammingDist_eq_hammingNorm]
    congr 1
    abel
  have hrec := decode_eq hammingDist C t (code_unique C t hd) (w' - (w - c)) c hc'
    (by rw [he]; simpa only [hammingDist_comm] using hw)
  simp only [codeOffsetRec, hrec]
  congr 1
  abel

theorem offset_mass (C : Finset (Fin n → F)) (hC : C.Nonempty) (w s : Fin n → F) :
    codeOffsetSS C hC w s = if w - s ∈ C then (C.card : ℝ≥0∞)⁻¹ else 0 := by
  rw [codeOffsetSS, PMF.map_apply]
  rw [tsum_eq_single (w - s)]
  · simp
  · intro c hc
    have hne : s ≠ w - c := by
      intro h
      apply hc
      rw [h]
      abel
    simp [hne]

theorem offset_joint_mass {I : Type} (C : Finset (Fin n → F)) (hC : C.Nonempty)
    (P : PMF ((Fin n → F) × I)) (w s : Fin n → F) (i : I) :
    withSketchAux (codeOffsetSS C hC) P (w, (s, i)) =
      P (w, i) * (if w - s ∈ C then (C.card : ℝ≥0∞)⁻¹ else 0) := by
  rw [withSketchAux, PMF.bind_apply, tsum_eq_single (w, i)]
  · simp only [PMF.map_apply, Prod.mk.injEq, true_and]
    rw [tsum_eq_single s]
    · simp [offset_mass]
    · intro s' hs'
      simp [Ne.symm hs']
  · rintro ⟨w', i'⟩ hne
    suffices hzero : ((codeOffsetSS C hC w').map fun a => (w', (a, i'))) (w, (s, i)) = 0 by
      simp [hzero]
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    have hn : (w, (s, i)) ≠ (w', (a, i')) := by
      intro h
      apply hne
      exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun x => x.2.2) h).symm
    simp [hn]

theorem offset_guessing [Fintype F] {I : Type} (C : Finset (Fin n → F)) (hC : C.Nonempty)
    (P : PMF ((Fin n → F) × I)) :
    guessing (withSketchAux (codeOffsetSS C hC) P) ≤
      ((Fintype.card (Fin n → F) : ℝ) / C.card) * guessing P := by
  have hpoint (s : Fin n → F) (i : I) :
      (⨆ w, withSketchAux (codeOffsetSS C hC) P (w, (s, i))) ≤
        (⨆ w, P (w, i)) * (C.card : ℝ≥0∞)⁻¹ := by
    refine iSup_le fun w => ?_
    rw [offset_joint_mass]
    split_ifs
    · exact mul_le_mul_left (le_iSup (fun w => P (w, i)) w) _
    · simp
  have hmass : guessingMass (withSketchAux (codeOffsetSS C hC) P) ≤
      (Fintype.card (Fin n → F) : ℝ≥0∞) * (guessingMass P * (C.card : ℝ≥0∞)⁻¹) := by
    unfold guessingMass
    rw [ENNReal.tsum_prod']
    calc
      _ ≤ ∑' s : Fin n → F, ∑' i : I, (⨆ w, P (w, i)) * (C.card : ℝ≥0∞)⁻¹ :=
        ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum (hpoint s)
      _ = _ := by simp only [ENNReal.tsum_mul_right, tsum_fintype, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
  have hK : (C.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have htop : (Fintype.card (Fin n → F) : ℝ≥0∞) *
      (guessingMass P * (C.card : ℝ≥0∞)⁻¹) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (guessingMass_ne_top P)
      (ENNReal.inv_ne_top.mpr hK))
  have hr := ENNReal.toReal_mono htop hmass
  simpa only [guessing, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hr

end Thm51Proof

theorem solution {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F] {n : ℕ}
    (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ) (hdist : MinDistGe C (2 * t + 1)) :
    ∀ m : ℝ, IsAvgSecureSketch hammingDist m
      (m - ((n : ℝ) * Real.logb 2 (Fintype.card F) - Real.logb 2 C.card)) t
      (codeOffsetSS C hC) (codeOffsetRec C t) := by
  intro m
  refine ⟨Thm51Proof.offset_correct C hC t hdist, ?_⟩
  intro ι WI hm
  have hF_pos : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hC_pos : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  have hg_pos : 0 < Thm51Proof.guessing WI := Thm51Proof.guessing_pos WI
  have hg'_pos : 0 < Thm51Proof.guessing (withSketchAux (codeOffsetSS C hC) WI) :=
    Thm51Proof.guessing_pos _
  have hle := Thm51Proof.offset_guessing C hC WI
  have hcard : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := by
    simp [Fintype.card_fin]
  rw [hcard] at hle
  have hlog_le := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hg'_pos
    (mul_pos (div_pos (pow_pos hF_pos n) hC_pos) hg_pos)).mpr hle
  have hlog_rhs :
      Real.logb 2 (((Fintype.card F : ℝ) ^ n / C.card) * Thm51Proof.guessing WI) =
        (n : ℝ) * Real.logb 2 (Fintype.card F) - Real.logb 2 C.card +
          Real.logb 2 (Thm51Proof.guessing WI) := by
    rw [Real.logb_mul (div_ne_zero (pow_ne_zero n hF_pos.ne') hC_pos.ne') hg_pos.ne',
      Real.logb_div (pow_ne_zero n hF_pos.ne') hC_pos.ne', Real.logb_pow]
  rw [hlog_rhs] at hlog_le
  rw [Thm51Proof.avgMinEntropy_eq_neg_log_guessing] at hm ⊢
  linarith
