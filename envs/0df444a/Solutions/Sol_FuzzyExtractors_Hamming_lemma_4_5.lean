-- Prove2me | solution 1 for FuzzyExtractors.Hamming.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:24:26.104988+00:00
-- url     : https://prove2.me/submissions/2baf2366-5abc-4ffe-b95f-0180f6bded99

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace Lemma45Proof

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

theorem decode_eq {M : Type} (dis : M → M → ℕ) (C : Finset M) (t : ℕ)
    (hcode : IsCode dis C t) (y c : M) (hc : c ∈ C) (hy : dis y c ≤ t) :
    decodeWithin dis C t y = c := by
  have he : ∃ a ∈ C, dis y a ≤ t := ⟨c, hc, hy⟩
  rw [decodeWithin, dif_pos he]
  exact hcode y _ he.choose_spec.1 c hc he.choose_spec.2 hy

theorem trans_correct {M Pm : Type} [Fintype Pm] [DecidableEq M]
    (dis : M → M → ℕ) (hsymm : ∀ a b, dis a b = dis b a)
    (C : Finset M) (hC : C.Nonempty) (t : ℕ) (hcode : IsCode dis C t)
    (act : Pm → M ≃ M) (hiso : ∀ π a b, dis (act π a) (act π b) = dis a b)
    (htrans : ∀ a b, ∃ π, act π a = b) :
    SketchCorrect dis t (transSS C hC act htrans) (transRec dis C t act) := by
  intro w w' hw π hπ
  obtain ⟨b, hb, hπb⟩ := (PMF.mem_support_bind_iff _ _ _).1 hπ
  have hbC : b ∈ C := (PMF.mem_support_uniformOfFinset_iff hC b).1 hb
  have hπ_mem : π ∈ Finset.univ.filter (fun π => act π w = b) :=
    (PMF.mem_support_uniformOfFinset_iff _ π).1 hπb
  have hact_eq : act π w = b := (Finset.mem_filter.1 hπ_mem).2
  have hdis : dis (act π w') b ≤ t := by
    rw [← hact_eq, hiso, hsymm]
    exact hw
  have hdec := decode_eq dis C t hcode (act π w') b hbC hdis
  simp only [transRec, hdec, ← hact_eq, Equiv.symm_apply_apply]

theorem trans_mass_le {M Pm : Type} [Fintype Pm] [DecidableEq M]
    (C : Finset M) (hC : C.Nonempty) (act : Pm → M ≃ M) (htrans : ∀ a b, ∃ π, act π a = b)
    (Γ : ℕ) (_hΓpos : 0 < Γ) (hΓ : ∀ w b, Γ ≤ (Finset.univ.filter fun π => act π w = b).card)
    (w : M) (π : Pm) :
    transSS C hC act htrans w π ≤ (C.card : ℝ≥0∞)⁻¹ * (Γ : ℝ≥0∞)⁻¹ := by
  rw [transSS, PMF.bind_apply, tsum_eq_single (act π w)]
  · rw [PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply]
    split_ifs with h1 h2
    · refine mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 ?_)
      exact_mod_cast hΓ w (act π w)
    · simp
    · simp
    · simp
  · intro b hb
    rw [PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply]
    have hnot : π ∉ Finset.univ.filter (fun π' => act π' w = b) := by
      simp [hb.symm]
    simp [hnot]

theorem trans_joint_mass {M Pm I : Type} [Fintype Pm] [DecidableEq M]
    (C : Finset M) (hC : C.Nonempty) (act : Pm → M ≃ M) (htrans : ∀ a b, ∃ π, act π a = b)
    (P : PMF (M × I)) (w : M) (π : Pm) (i : I) :
    withSketchAux (transSS C hC act htrans) P (w, (π, i)) =
      P (w, i) * transSS C hC act htrans w π := by
  rw [withSketchAux, PMF.bind_apply, tsum_eq_single (w, i)]
  · simp only [PMF.map_apply, Prod.mk.injEq, true_and]
    rw [tsum_eq_single π]
    · simp
    · intro π' hπ'
      simp [Ne.symm hπ']
  · rintro ⟨w', i'⟩ hne
    suffices hzero : ((transSS C hC act htrans w').map fun a => (w', (a, i'))) (w, (π, i)) = 0 by
      simp [hzero]
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    have hn : (w, (π, i)) ≠ (w', (a, i')) := by
      intro h
      apply hne
      exact Prod.ext (congrArg Prod.fst h).symm (congrArg (fun x => x.2.2) h).symm
    simp [hn]

theorem trans_guessing {M Pm I : Type} [Fintype Pm] [DecidableEq M]
    (C : Finset M) (hC : C.Nonempty) (act : Pm → M ≃ M) (htrans : ∀ a b, ∃ π, act π a = b)
    (Γ : ℕ) (hΓpos : 0 < Γ) (hΓ : ∀ w b, Γ ≤ (Finset.univ.filter fun π => act π w = b).card)
    (P : PMF (M × I)) :
    guessing (withSketchAux (transSS C hC act htrans) P) ≤
      ((Fintype.card Pm : ℝ) / ((C.card : ℝ) * (Γ : ℝ))) * guessing P := by
  let invCG : ℝ≥0∞ := (C.card : ℝ≥0∞)⁻¹ * (Γ : ℝ≥0∞)⁻¹
  have hpoint (π : Pm) (i : I) :
      (⨆ w, withSketchAux (transSS C hC act htrans) P (w, (π, i))) ≤
        (⨆ w, P (w, i)) * invCG := by
    refine iSup_le fun w => ?_
    rw [trans_joint_mass]
    exact mul_le_mul' (le_iSup (fun w => P (w, i)) w)
      (trans_mass_le C hC act htrans Γ hΓpos hΓ w π)
  have hmass : guessingMass (withSketchAux (transSS C hC act htrans) P) ≤
      (Fintype.card Pm : ℝ≥0∞) * (guessingMass P * invCG) := by
    unfold guessingMass
    rw [ENNReal.tsum_prod']
    calc
      _ ≤ ∑' π : Pm, ∑' i : I, (⨆ w, P (w, i)) * invCG :=
        ENNReal.tsum_le_tsum fun π => ENNReal.tsum_le_tsum (hpoint π)
      _ = _ := by simp only [ENNReal.tsum_mul_right, tsum_fintype, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
  have hK : (C.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  have hG : (Γ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hΓpos.ne'
  have hinv_top : invCG ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hK) (ENNReal.inv_ne_top.mpr hG)
  have htop : (Fintype.card Pm : ℝ≥0∞) * (guessingMass P * invCG) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (guessingMass_ne_top P) hinv_top)
  have hr := ENNReal.toReal_mono htop hmass
  simpa only [guessing, invCG, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm] using hr

end Lemma45Proof

theorem solution {M Pm : Type} [Fintype M] [DecidableEq M] [Fintype Pm]
    (dis : M → M → ℕ) (hsymm : ∀ a b, dis a b = dis b a)
    (C : Finset M) (hC : C.Nonempty) (t : ℕ) (hcode : IsCode dis C t)
    (act : Pm → M ≃ M) (hiso : ∀ π a b, dis (act π a) (act π b) = dis a b)
    (htrans : ∀ a b, ∃ π, act π a = b)
    (Γ : ℕ) (hΓpos : 0 < Γ) (hΓ : ∀ w b, Γ ≤ (Finset.univ.filter fun π => act π w = b).card) :
    ∀ m : ℝ, IsAvgSecureSketch dis m
      (m - Real.logb 2 (Fintype.card Pm) + Real.logb 2 Γ + Real.logb 2 C.card) t
      (transSS C hC act htrans) (transRec dis C t act) := by
  intro m
  refine ⟨Lemma45Proof.trans_correct dis hsymm C hC t hcode act hiso htrans, ?_⟩
  intro ι WI hm
  have ⟨c0, _⟩ := hC
  obtain ⟨π0, _⟩ := htrans c0 c0
  have hPm_pos : (0 : ℝ) < Fintype.card Pm := Nat.cast_pos.mpr (@Fintype.card_pos Pm _ ⟨π0⟩)
  have hC_pos : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  have hG_pos : (0 : ℝ) < Γ := Nat.cast_pos.mpr hΓpos
  have hg_pos : 0 < Lemma45Proof.guessing WI := Lemma45Proof.guessing_pos WI
  have hg'_pos : 0 < Lemma45Proof.guessing (withSketchAux (transSS C hC act htrans) WI) :=
    Lemma45Proof.guessing_pos _
  have hle := Lemma45Proof.trans_guessing C hC act htrans Γ hΓpos hΓ WI
  have hlog_le := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hg'_pos
    (mul_pos (div_pos hPm_pos (mul_pos hC_pos hG_pos)) hg_pos)).mpr hle
  have hlog_rhs :
      Real.logb 2 (((Fintype.card Pm : ℝ) / ((C.card : ℝ) * (Γ : ℝ))) * Lemma45Proof.guessing WI) =
        Real.logb 2 (Fintype.card Pm) - Real.logb 2 C.card - Real.logb 2 Γ +
          Real.logb 2 (Lemma45Proof.guessing WI) := by
    rw [Real.logb_mul (div_ne_zero hPm_pos.ne' (mul_ne_zero hC_pos.ne' hG_pos.ne')) hg_pos.ne',
      Real.logb_div hPm_pos.ne' (mul_ne_zero hC_pos.ne' hG_pos.ne'),
      Real.logb_mul hC_pos.ne' hG_pos.ne']
    ring
  rw [hlog_rhs] at hlog_le
  rw [Lemma45Proof.avgMinEntropy_eq_neg_log_guessing] at hm ⊢
  linarith
