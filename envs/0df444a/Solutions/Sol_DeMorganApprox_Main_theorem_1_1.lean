-- Prove2me | solution 1 for DeMorganApprox.Main.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:14:26.642695+00:00
-- url     : https://prove2.me/submissions/c09b2186-54dd-4877-8453-95bebd3f4c00

import Theorems.Thm_DeMorganApprox_Main_lemma_5_2
import Theorems.Thm_DeMorganApprox_Main_lemma_5_6
import Theorems.Thm_DeMorganApprox_Main_lemma_5_7
import Theorems.Thm_DeMorganApprox_Main_lemma_5_9
import Theorems.Thm_DeMorganApprox_Main_lemma_4_1

open DeMorganApprox.Main

private theorem chainInduction {m : ℕ} (G : TieRule → Formula m → Prop)
    (base : ∀ tie i b, G tie (.lit i b))
    (step : ∀ tie T, T.isLeaf = false →
      (∀ t ∈ terminals tie T, G t.1 t.2) → G tie T)
    (T : Formula m) (tie : TieRule) : G tie T := by
  suffices strong : ∀ tie, G tie T ∧ ∀ t ∈ terminals tie T, G t.1 t.2 from (strong tie).1
  induction T with
  | lit i b =>
    intro tie
    exact ⟨base tie i b, by simpa [terminals] using base tie i b⟩
  | and l r ihl ihr | or l r ihl ihr =>
    intro tie
    suffices aux : ∀ t ∈ terminals tie _, G t.1 t.2 from ⟨step tie _ rfl aux, aux⟩
    cases hd : heavyDir tie l r <;> simp [terminals, hd, pick, ihl, ihr] <;>
      intro a b h <;> first | exact (ihl _).2 (a,b) h | exact (ihr _).2 (a,b) h

private theorem valid {m : ℕ} (T : Formula m) (tie : TieRule) :
    (program tie T).IsVectorForm ∧ (program tie T).Computes T.eval ∧
      (program tie T).HasBalancedBound (helperBound tie T) := by
  apply chainInduction (fun tie T => (program tie T).IsVectorForm ∧
    (program tie T).Computes T.eval ∧ (program tie T).HasBalancedBound (helperBound tie T))
  · intro tie i b
    obtain ⟨hc,hv,hw,_⟩ := lemma_5_2 tie i b
    exact ⟨hv,hc,hw⟩
  · intro tie U hu h
    obtain ⟨hc,hv,_,hw,_⟩ := lemma_5_6 tie U hu h
    exact ⟨hv,hc,hw⟩

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (φ : Formula m),
      ∃ P : MvPolynomial (Fin m) ℝ, IsMultilinear P ∧
        (∀ x : Fin m → Bool, |MvPolynomial.eval (boolPoint x) P - boolVal (φ.eval x)| ≤ 1 / 3) ∧
        (P.totalDegree : ℝ) ≤ C * Real.sqrt (φ.leaves : ℝ) ∧
        coeffL1 P ≤ (2 : ℝ) ^ (C * Real.sqrt (φ.leaves : ℝ)) := by
  obtain ⟨k,hk⟩ := lemma_5_9
  let K := max k 0
  obtain ⟨D,hD,hpoly⟩ := lemma_4_1 K (le_max_right _ _)
  refine ⟨D * 100, by positivity, ?_⟩
  intro m φ
  let tie : TieRule := fun _ => false
  obtain ⟨hv,hc,hw⟩ := valid φ tie
  have hnorm : AbsNormLE (program tie φ).vec K :=
    fun y => (hk m tie φ y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨Q,hm,ha,hd,hq⟩ := hpoly m (program tie φ) _ _ hw.1 hv hc hw hnorm
  have he : D * helperBound tie φ ≤ D * 100 * Real.sqrt (φ.leaves : ℝ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((lemma_5_7.2 m tie φ).2) hD.le
  exact ⟨Q,hm,ha,hd.trans he,hq.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)⟩
