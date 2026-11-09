-- Prove2me | solution 1 for FiniteStateContract.Equivalence.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:21:47.701011+00:00
-- url     : https://prove2.me/submissions/b0a2ef01-457d-4097-93fb-55b2e9dda9cc

import Definitions.Def_FiniteStateContract_Equivalence_Model

open MeasureTheory
open scoped NNReal

open ExtFSMFG.Existence (Omega Xm seminormE)

open FiniteStateContract.Equivalence in
theorem solution {m l : ℕ} {T : ℝ≥0} (D : Data m l T) (a : Feedback m l)
    (hS : Setting D) (h21 : Assumption21 D) (h31 : Assumption31 D a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : Omega m T) (t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (R : ℝ) (p : stdSimplex ℝ (Fin m)) (z z' : Vec m),
        |Hhat D a t (Xm t ω) z p R - Hhat D a t (Xm t ω) z' p R| ≤
          C * seminormE (Xm t ω) (z - z') ∧
        ‖a t (Xm t ω) z p - a t (Xm t ω) z' p‖ ≤
          C * seminormE (Xm t ω) (z - z') := by
  obtain ⟨-, ⟨Cq, hCq, hq⟩, -⟩ := h21
  obtain ⟨hmin, -, ⟨Ca, hCa, ha⟩⟩ := h31
  have hmC : 0 ≤ (m : ℝ) * (Cq + 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  refine ⟨m * (Cq + 1) + Ca, by linarith, fun ω t _ htT R p z z' => ?_⟩
  set i := Xm t ω with hi
  have hs0 : 0 ≤ seminormE i (z - z') := Real.sqrt_nonneg _
  -- key estimate for a fixed action
  have key : ∀ b ∈ D.A, |H D t i z b p R - H D t i z' b p R| ≤
      (m : ℝ) * (Cq + 1) * seminormE i (z - z') := by
    intro b hb
    have e : H D t i z b p R - H D t i z' b p R =
        ∑ j ∈ Finset.univ.erase i, ((z - z') j - (z - z') i) * (D.q t i j b p - 1) := by
      unfold H
      rw [show ∀ x y : ℝ, (D.c t i b p - R + x) - (D.c t i b p - R + y) = x - y from
        fun x y => by ring]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply]
      ring
    rw [e]
    have hterm : ∀ j ∈ Finset.univ.erase i,
        |((z - z') j - (z - z') i) * (D.q t i j b p - 1)| ≤
          seminormE i (z - z') * (Cq + 1) := by
      intro j hj
      rw [abs_mul]
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      obtain ⟨hq0, hq1⟩ := hq t htT i j hji.symm b hb p p.2
      have h1 : |D.q t i j b p - 1| ≤ Cq + 1 := by
        rw [abs_le]; constructor <;> linarith
      have h2 : |(z - z') j - (z - z') i| ≤ seminormE i (z - z') := by
        unfold seminormE
        apply Real.abs_le_sqrt
        exact Finset.single_le_sum (f := fun k => ((z - z') k - (z - z') i) ^ 2)
          (fun k _ => sq_nonneg _) hj
      exact mul_le_mul h2 h1 (abs_nonneg _) hs0
    calc |∑ j ∈ Finset.univ.erase i, ((z - z') j - (z - z') i) * (D.q t i j b p - 1)|
        ≤ ∑ j ∈ Finset.univ.erase i, |((z - z') j - (z - z') i) * (D.q t i j b p - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase i, seminormE i (z - z') * (Cq + 1) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.univ.erase i).card : ℝ) * (seminormE i (z - z') * (Cq + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (seminormE i (z - z') * (Cq + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hs0 (by linarith))
          have : (Finset.univ.erase i).card ≤ m := by
            calc (Finset.univ.erase i).card ≤ (Finset.univ : Finset (Fin m)).card :=
                  Finset.card_erase_le
              _ = m := by simp
          exact_mod_cast this
      _ = (m : ℝ) * (Cq + 1) * seminormE i (z - z') := by ring
  obtain ⟨hA1, hmin1⟩ := hmin t htT i z p p.2
  obtain ⟨hA2, hmin2⟩ := hmin t htT i z' p p.2
  have le1 : H D t i z (a t i z p) p R ≤ H D t i z (a t i z' p) p R := by
    by_cases h : a t i z' p = a t i z p
    · rw [h]
    · exact (hmin1 R _ hA2 h).le
  have le2 : H D t i z' (a t i z' p) p R ≤ H D t i z' (a t i z p) p R := by
    by_cases h : a t i z p = a t i z' p
    · rw [h]
    · exact (hmin2 R _ hA1 h).le
  have k1 := key _ hA2
  have k2 := key _ hA1
  rw [abs_le] at k1 k2
  have hfin : (m : ℝ) * (Cq + 1) * seminormE i (z - z') ≤
      (m * (Cq + 1) + Ca) * seminormE i (z - z') := by
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold Hhat
    rw [abs_le]
    constructor <;> linarith [k1.1, k1.2, k2.1, k2.2]
  · refine (ha t htT i z z' p p.2).trans ?_
    nlinarith
