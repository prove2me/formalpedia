-- Prove2me | solution 1 for BosonicLearn.gammaFock_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:12:56.295652+00:00
-- url     : https://prove2.me/submissions/279cca9f-565d-4793-afa6-bc654006efd7

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-- A positive semidefinite matrix is of the form `Sᴴ * S`. -/
private lemma exists_conjTranspose_mul_self {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosSemidef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, R = Sᴴ * S := by
  open scoped MatrixOrder in
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  exact ⟨S, by rw [hS, Matrix.star_eq_conjTranspose]⟩

/-- `Γ(Sᴴ S) = Γ(S)ᴴ Γ(S)` entrywise, with the intermediate sum over any finite set containing the
photon-number sector of `u`. -/
private lemma gammaFock_conjTranspose_mul_self {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (u v : Occupation (Fin n)) (W : Finset (Occupation (Fin n)))
    (hW : (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
      (fun w => ∑ i, w i = ∑ i, u i) ⊆ W) :
    gammaFock (Sᴴ * S) u v = ∑ w ∈ W, star (gammaFock S w u) * gammaFock S w v := by
  rw [gammaFock_mul, Finset.sum_subset hW]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [(gammaFock_basic S u w).2.1]
  · intro w _ hw
    have hne : ∑ i, u i ≠ ∑ i, w i := by
      intro h
      apply hw
      rw [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun k => ?_, h.symm⟩
      rw [Finset.mem_range, h]
      have h2 : w k ≤ ∑ i, w i :=
        Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    rw [(gammaFock_basic Sᴴ u w).1 hne, zero_mul]

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (s : Finset (Occupation (Fin n))) (z : Occupation (Fin n) → ℂ) :
    (∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock R u v * z v).im = 0 ∧
    0 ≤ (∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock R u v * z v).re := by
  obtain ⟨S, rfl⟩ := exists_conjTranspose_mul_self R hR
  obtain ⟨W, hW⟩ : ∃ W : Finset (Occupation (Fin n)), ∀ u ∈ s,
      (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
        (fun w => ∑ i, w i = ∑ i, u i) ⊆ W := by
    refine ⟨Fintype.piFinset fun _ : Fin n => Finset.range (s.sup (fun u => ∑ i, u i) + 1), ?_⟩
    intro u hu w hw
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hw
    rw [Fintype.mem_piFinset]
    intro k
    have h1 := hw.1 k
    rw [Finset.mem_range] at h1 ⊢
    have h2 : ∑ i, u i ≤ s.sup (fun u => ∑ i, u i) :=
      Finset.le_sup (f := fun u : Occupation (Fin n) => ∑ i, u i) hu
    omega
  have step1 : ∀ u ∈ s, ∀ v, star (z u) * gammaFock (Sᴴ * S) u v * z v =
      ∑ w ∈ W, star (gammaFock S w u * z u) * (gammaFock S w v * z v) := by
    intro u hu v
    rw [gammaFock_conjTranspose_mul_self S u v W (hW u hu), Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [star_mul']
    ring
  have step3 : ∀ w, ∑ u ∈ s, ∑ v ∈ s, star (gammaFock S w u * z u) * (gammaFock S w v * z v) =
      ((Complex.normSq (∑ v ∈ s, gammaFock S w v * z v) : ℝ) : ℂ) := by
    intro w
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
  have key : ∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock (Sᴴ * S) u v * z v =
      ∑ w ∈ W, ((Complex.normSq (∑ v ∈ s, gammaFock S w v * z v) : ℝ) : ℂ) := by
    calc ∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock (Sᴴ * S) u v * z v
        = ∑ u ∈ s, ∑ v ∈ s, ∑ w ∈ W,
            star (gammaFock S w u * z u) * (gammaFock S w v * z v) :=
          Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v _ => step1 u hu v
      _ = ∑ u ∈ s, ∑ w ∈ W, ∑ v ∈ s,
            star (gammaFock S w u * z u) * (gammaFock S w v * z v) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ w ∈ W, ∑ u ∈ s, ∑ v ∈ s,
            star (gammaFock S w u * z u) * (gammaFock S w v * z v) := Finset.sum_comm
      _ = ∑ w ∈ W, ((Complex.normSq (∑ v ∈ s, gammaFock S w v * z v) : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun w _ => step3 w
  rw [key, ← Complex.ofReal_sum]
  exact ⟨Complex.ofReal_im _, by
    rw [Complex.ofReal_re]
    exact Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _⟩
