-- Prove2me | solution 1 for CoherenceUncertainty.Qubit.cmax_eq_one_sub_cmin
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:25:57.186+00:00
-- url     : https://prove2.me/submissions/4454743a-9e16-4137-be8d-fdfcee02fc0f

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

open CoherenceUncertainty.Qubit in
theorem solution (U V : MBasis) :
    cmax U V = 1 - cmin U V ∧ 1 / 2 ≤ cmax U V := by
  obtain ⟨M, hMdef⟩ : ∃ M : Mat2, M = star (U : Mat2) * (V : Mat2) := ⟨_, rfl⟩
  have hMu : M ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [hMdef]
    exact Submonoid.mul_mem _ (Unitary.star_mem U.2) V.2
  have hov : ∀ i j, overlap U V i j = ‖M i j‖ ^ 2 := by
    intro i j; rw [hMdef]; rfl
  have h1 : M * star M = 1 := Unitary.mul_star_self_of_mem hMu
  have h2 : star M * M = 1 := Unitary.star_mul_self_of_mem hMu
  have hrow : ∀ i, ‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2 = 1 := by
    intro i
    have := congrFun (congrFun h1 i) i
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  have hcol : ∀ j, ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 = 1 := by
    intro j
    have := congrFun (congrFun h2 j) j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_mul', Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  have r0 := hrow 0
  have r1 := hrow 1
  have c0 := hcol 0
  obtain ⟨a, ha⟩ : ∃ a, a = ‖M 0 0‖ ^ 2 := ⟨_, rfl⟩
  have hval : ∀ ij : Fin 2 × Fin 2, overlap U V ij.1 ij.2 = a ∨ overlap U V ij.1 ij.2 = 1 - a := by
    intro ij
    rw [hov]
    fin_cases ij
    · left; exact ha.symm
    · right; simp; linarith
    · right; simp; linarith
    · left; simp; linarith
  have h00 : overlap U V 0 0 = a := by rw [hov, ha]
  have h01 : overlap U V 0 1 = 1 - a := by rw [hov]; linarith
  have hmem00 : ((0 : Fin 2), (0 : Fin 2)) ∈ (Finset.univ : Finset (Fin 2 × Fin 2)) :=
    Finset.mem_univ _
  have hmem01 : ((0 : Fin 2), (1 : Fin 2)) ∈ (Finset.univ : Finset (Fin 2 × Fin 2)) :=
    Finset.mem_univ _
  have hmax : cmax U V = max a (1 - a) := by
    apply le_antisymm
    · unfold cmax
      apply Finset.sup'_le
      intro ij _
      rcases hval ij with h | h <;> rw [h]
      · exact le_max_left _ _
      · exact le_max_right _ _
    · apply max_le
      · have := Finset.le_sup' (s := (Finset.univ : Finset (Fin 2 × Fin 2)))
          (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2) hmem00
        have h' : overlap U V 0 0 ≤ cmax U V := this
        linarith
      · have := Finset.le_sup' (s := (Finset.univ : Finset (Fin 2 × Fin 2)))
          (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2) hmem01
        have h' : overlap U V 0 1 ≤ cmax U V := this
        linarith
  have hmin : cmin U V = min a (1 - a) := by
    apply le_antisymm
    · apply le_min
      · have := Finset.inf'_le (s := (Finset.univ : Finset (Fin 2 × Fin 2)))
          (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2) hmem00
        have h' : cmin U V ≤ overlap U V 0 0 := this
        linarith
      · have := Finset.inf'_le (s := (Finset.univ : Finset (Fin 2 × Fin 2)))
          (fun ij : Fin 2 × Fin 2 => overlap U V ij.1 ij.2) hmem01
        have h' : cmin U V ≤ overlap U V 0 1 := this
        linarith
    · unfold cmin
      apply Finset.le_inf'
      intro ij _
      rcases hval ij with h | h <;> rw [h]
      · exact min_le_left _ _
      · exact min_le_right _ _
  rw [hmax, hmin]
  constructor
  · rcases le_total a (1 - a) with h | h
    · rw [max_eq_right h, min_eq_left h]
    · rw [max_eq_left h, min_eq_right h] <;> ring_nf
  · rcases le_total a (1 - a) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
