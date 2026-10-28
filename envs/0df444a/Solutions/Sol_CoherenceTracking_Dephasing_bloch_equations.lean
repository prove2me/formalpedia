-- Prove2me | solution 1 for CoherenceTracking.Dephasing.bloch_equations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:57:46.692919+00:00
-- url     : https://prove2.me/submissions/5764f939-063a-48c1-99cc-97b71ba8f974

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
open Matrix Complex

lemma pauli0 : pauli 0 = !![0, 1; 1, 0] := rfl
lemma pauli1 : pauli 1 = !![0, -Complex.I; Complex.I, 0] := rfl
lemma pauli2 : pauli 2 = !![1, 0; 0, -1] := rfl

lemma bv0 (ρ : Qmat) : blochVec ρ 0 = (ρ 0 1 + ρ 1 0).re := by
  simp [blochVec, pauli0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
lemma bv1 (ρ : Qmat) : blochVec ρ 1 = (ρ 1 0).im - (ρ 0 1).im := by
  simp [blochVec, pauli1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
lemma bv2 (ρ : Qmat) : blochVec ρ 2 = (ρ 0 0).re - (ρ 1 1).re := by
  simp [blochVec, pauli2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

lemma bs00 (v : BVec) : blochState v 0 0 = (1 + (v 2 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs11 (v : BVec) : blochState v 1 1 = (1 - (v 2 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs01 (v : BVec) : blochState v 0 1 = ((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs10 (v : BVec) : blochState v 1 0 = ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring



lemma herm_bs (v : BVec) : (blochState v)ᴴ = blochState v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, bs00, bs11, bs01, bs10, Complex.ext_iff]

lemma trace_bs (v : BVec) : (blochState v).trace = 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, bs00, bs11]
  ring

lemma trsq_bs (v : BVec) : ((blochState v * blochState v).trace).re = (1 + ∑ α, v α ^ 2) / 2 := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, bs00, bs11, bs01, bs10]
  ring_nf


lemma mr00 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (ρ : Qmat) :
    masterRHS hbar γ ω ρ 0 0 = -(Complex.I / 2) * ((ω 1 + Complex.I * ω 2) * ρ 1 0 - (ω 1 - Complex.I * ω 2) * ρ 0 1) := by
  have : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  conv_lhs => rw [Matrix.eta_fin_two ρ]
  simp [masterRHS, hamiltonian, pauli0, pauli1, pauli2, Matrix.mul_fin_two]
  field_simp
  ring

lemma mr01 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (ρ : Qmat) :
    masterRHS hbar γ ω ρ 0 1 = -(Complex.I / 2) * (2 * ω 0 * ρ 0 1 + (ω 1 + Complex.I * ω 2) * (ρ 1 1 - ρ 0 0)) - γ * ρ 0 1 := by
  have : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  conv_lhs => rw [Matrix.eta_fin_two ρ]
  simp [masterRHS, hamiltonian, pauli0, pauli1, pauli2, Matrix.mul_fin_two]
  field_simp
  ring

lemma mr10 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (ρ : Qmat) :
    masterRHS hbar γ ω ρ 1 0 = -(Complex.I / 2) * ((ω 1 - Complex.I * ω 2) * (ρ 0 0 - ρ 1 1) - 2 * ω 0 * ρ 1 0) - γ * ρ 1 0 := by
  have : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  conv_lhs => rw [Matrix.eta_fin_two ρ]
  simp [masterRHS, hamiltonian, pauli0, pauli1, pauli2, Matrix.mul_fin_two]
  field_simp
  ring

lemma mr11 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (ρ : Qmat) :
    masterRHS hbar γ ω ρ 1 1 = -(Complex.I / 2) * ((ω 1 - Complex.I * ω 2) * ρ 0 1 - (ω 1 + Complex.I * ω 2) * ρ 1 0) := by
  have : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  conv_lhs => rw [Matrix.eta_fin_two ρ]
  simp [masterRHS, hamiltonian, pauli0, pauli1, pauli2, Matrix.mul_fin_two]
  field_simp
  ring

lemma blochVec_rhs (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (ρ : Qmat) :
    blochVec (masterRHS hbar γ ω ρ) = (blochMatrix γ ω).mulVec (blochVec ρ) := by
  funext α
  fin_cases α <;>
  · simp [bv0, bv1, bv2, mr00 hbar γ hh, mr01 hbar γ hh, mr10 hbar γ hh, mr11 hbar γ hh, blochMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring

lemma mrb00 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (v : BVec) :
    masterRHS hbar γ ω (blochState v) 0 0 = (((blochMatrix γ ω).mulVec v 2 : ℝ) : ℂ) / 2 := by
  rw [mr00 hbar γ hh]
  simp only [bs00, bs11, bs01, bs10, blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma mrb01 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (v : BVec) :
    masterRHS hbar γ ω (blochState v) 0 1 =
      ((((blochMatrix γ ω).mulVec v 0 : ℝ) : ℂ) - Complex.I * (((blochMatrix γ ω).mulVec v 1 : ℝ) : ℂ)) / 2 := by
  rw [mr01 hbar γ hh]
  simp only [bs00, bs11, bs01, bs10, blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma mrb10 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (v : BVec) :
    masterRHS hbar γ ω (blochState v) 1 0 =
      ((((blochMatrix γ ω).mulVec v 0 : ℝ) : ℂ) + Complex.I * (((blochMatrix γ ω).mulVec v 1 : ℝ) : ℂ)) / 2 := by
  rw [mr10 hbar γ hh]
  simp only [bs00, bs11, bs01, bs10, blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma mrb11 (hbar γ : ℝ) (hh : 0 < hbar) (ω : Fin 3 → ℝ) (v : BVec) :
    masterRHS hbar γ ω (blochState v) 1 1 = -(((blochMatrix γ ω).mulVec v 2 : ℝ) : ℂ) / 2 := by
  rw [mr11 hbar γ hh]
  simp only [bs00, bs11, bs01, bs10, blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

lemma hd_re {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (h : HasDerivAt z z' t) :
    HasDerivAt (fun s => (z s).re) z'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

lemma hd_im {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (h : HasDerivAt z z' t) :
    HasDerivAt (fun s => (z s).im) z'.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

lemma hd_entry {ρ : ℝ → Qmat} {ρ' : Qmat} {t : ℝ} (h : HasDerivAt ρ ρ' t) (i j : Fin 2) :
    HasDerivAt (fun s => ρ s i j) (ρ' i j) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j

lemma hd_blochVec {ρ : ℝ → Qmat} {ρ' : Qmat} {t : ℝ} (h : HasDerivAt ρ ρ' t) :
    HasDerivAt (fun s => blochVec (ρ s)) (blochVec ρ') t := by
  refine hasDerivAt_pi.2 (fun α => ?_)
  fin_cases α
  · have := hd_re ((hd_entry h 0 1).add (hd_entry h 1 0))
    change HasDerivAt (fun s => blochVec (ρ s) 0) (blochVec ρ' 0) t
    simp only [bv0]
    exact this
  · have := (hd_im (hd_entry h 1 0)).sub (hd_im (hd_entry h 0 1))
    change HasDerivAt (fun s => blochVec (ρ s) 1) (blochVec ρ' 1) t
    simp only [bv1]
    exact this
  · have := (hd_re (hd_entry h 0 0)).sub (hd_re (hd_entry h 1 1))
    change HasDerivAt (fun s => blochVec (ρ s) 2) (blochVec ρ' 2) t
    simp only [bv2]
    exact this

lemma cont_blochVec {ρ : ℝ → Qmat} {S : Set ℝ} (h : ContinuousOn ρ S) :
    ContinuousOn (fun s => blochVec (ρ s)) S := by
  have hc : ∀ i j, ContinuousOn (fun s => ρ s i j) S := fun i j =>
    continuousOn_pi.1 (continuousOn_pi.1 h i) j
  refine continuousOn_pi.2 (fun α => ?_)
  fin_cases α
  · change ContinuousOn (fun s => blochVec (ρ s) 0) S
    simp only [bv0]
    exact Complex.continuous_re.comp_continuousOn ((hc 0 1).add (hc 1 0))
  · change ContinuousOn (fun s => blochVec (ρ s) 1) S
    simp only [bv1]
    exact (Complex.continuous_im.comp_continuousOn (hc 1 0)).sub
      (Complex.continuous_im.comp_continuousOn (hc 0 1))
  · change ContinuousOn (fun s => blochVec (ρ s) 2) S
    simp only [bv2]
    exact (Complex.continuous_re.comp_continuousOn (hc 0 0)).sub
      (Complex.continuous_re.comp_continuousOn (hc 1 1))

lemma cont_blochState {v : ℝ → BVec} {S : Set ℝ} (h : ContinuousOn v S) :
    ContinuousOn (fun s => blochState (v s)) S := by
  have hc : ∀ k, ContinuousOn (fun s => ((v s k : ℝ) : ℂ)) S := fun k =>
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_pi.1 h k)
  refine continuousOn_pi.2 (fun i => continuousOn_pi.2 (fun j => ?_))
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, bs00]
    exact ((continuousOn_const.add (hc 2))).div_const _
  · simp only [Fin.zero_eta, Fin.mk_one, bs01]
    exact ((hc 0).sub (continuousOn_const.mul (hc 1))).div_const _
  · simp only [Fin.zero_eta, Fin.mk_one, bs10]
    exact ((hc 0).add (continuousOn_const.mul (hc 1))).div_const _
  · simp only [Fin.mk_one, bs11]
    exact ((continuousOn_const.sub (hc 2))).div_const _

lemma hd_blochState (hbar γ : ℝ) (hh : 0 < hbar) {ω : Fin 3 → ℝ} {v : ℝ → BVec} {t : ℝ}
    (h : HasDerivAt v ((blochMatrix γ ω).mulVec (v t)) t) :
    HasDerivAt (fun s => blochState (v s)) (masterRHS hbar γ ω (blochState (v t))) t := by
  have hc : ∀ k, HasDerivAt (fun s => ((v s k : ℝ) : ℂ)) ((((blochMatrix γ ω).mulVec (v t) k : ℝ)) : ℂ) t :=
    fun k => (hasDerivAt_pi.1 h k).ofReal_comp
  refine hasDerivAt_pi.2 (fun i => hasDerivAt_pi.2 (fun j => ?_))
  fin_cases i <;> fin_cases j
  · have := ((hasDerivAt_const t (1 : ℂ)).add (hc 2)).div_const 2
    simp only [Fin.zero_eta, bs00]
    rw [mrb00 hbar γ hh]
    simpa using this
  · have := ((hc 0).sub ((hasDerivAt_const t Complex.I).mul (hc 1))).div_const 2
    simp only [Fin.zero_eta, Fin.mk_one, bs01]
    rw [mrb01 hbar γ hh]
    simpa using this
  · have := ((hc 0).add ((hasDerivAt_const t Complex.I).mul (hc 1))).div_const 2
    simp only [Fin.zero_eta, Fin.mk_one, bs10]
    rw [mrb10 hbar γ hh]
    simpa using this
  · have := ((hasDerivAt_const t (1 : ℂ)).sub (hc 2)).div_const 2
    simp only [Fin.mk_one, bs11]
    rw [mrb11 hbar γ hh]
    simpa [neg_div] using this


end CoherenceTracking.Dephasing

open CoherenceTracking.Dephasing

theorem solution (hbar γ : ℝ) (hhbar : 0 < hbar) :
    (∀ (ω : Fin 3 → ℝ) (ρ : Qmat),
        blochVec (masterRHS hbar γ ω ρ) = (blochMatrix γ ω).mulVec (blochVec ρ)) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat) (T : ℝ),
        SolvesMaster hbar γ ω ρ T → SolvesBloch γ ω (fun t => blochVec (ρ t)) T) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ),
        SolvesBloch γ ω v T → SolvesMaster hbar γ ω (fun t => blochState (v t)) T) := by
  refine ⟨fun ω ρ => blochVec_rhs hbar γ hhbar ω ρ, ?_, ?_⟩
  · rintro ω ρ T ⟨hc, hd⟩
    refine ⟨cont_blochVec hc, fun t ht => ?_⟩
    have := hd_blochVec (hd t ht)
    rwa [blochVec_rhs hbar γ hhbar] at this
  · rintro ω v T ⟨hc, hd⟩
    exact ⟨cont_blochState hc, fun t ht => hd_blochState hbar γ hhbar (hd t ht)⟩
