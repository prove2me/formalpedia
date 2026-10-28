-- Prove2me | solution 1 for CoherenceTracking.Dephasing.coherence_tracking_breakdown
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:04:15.005984+00:00
-- url     : https://prove2.me/submissions/1ff852c4-9e43-4d90-b644-b5093b8f87fd

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


theorem bloch_parametrization :
    (∀ ρ : Qmat, IsQubitState ρ →
        blochState (blochVec ρ) = ρ ∧ coherence ρ = 4 * Complex.normSq (ρ 0 1)) ∧
    (∀ v : BVec, blochVec (blochState v) = v) ∧
    (∀ v : BVec, IsQubitState (blochState v) ↔ ∑ α, v α ^ 2 ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ρ ⟨hH, hT, -⟩
    have h00 := congrFun (congrFun hH 0) 0
    have h11 := congrFun (congrFun hH 1) 1
    have h01 := congrFun (congrFun hH 0) 1
    have h10 := congrFun (congrFun hH 1) 0
    simp only [Matrix.conjTranspose_apply] at h00 h11 h01 h10
    have ht : ρ 0 0 + ρ 1 1 = 1 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hT
    rw [Complex.ext_iff] at h00 h11 h01 h10 ht
    simp at h00 h11 h01 h10 ht
    have key : blochState (blochVec ρ) = ρ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [bs00, bs11, bs01, bs10, bv0, bv1, bv2, Complex.ext_iff] <;> constructor <;> nlinarith
    refine ⟨key, ?_⟩
    simp only [coherence, bv0, bv1, Complex.normSq_apply, Complex.add_re]
    rw [h10.1, ← h01.2]
    rw [show (ρ 1 0).im = -(ρ 0 1).im from by linarith [h10.2]]
    ring
  · intro v
    funext α
    fin_cases α
    · simp [bv0, bs01, bs10]
    · simp [bv1, bs01, bs10]; ring
    · simp [bv2, bs00, bs11]; ring
  · intro v
    refine ⟨fun h => ?_, fun h => ⟨herm_bs v, trace_bs v, ?_⟩⟩
    · have := h.2.2
      rw [trsq_bs] at this
      linarith
    · rw [trsq_bs]; linarith



theorem bloch_equations (hbar γ : ℝ) (hhbar : 0 < hbar) :
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

lemma const_of_deriv_zero {g : ℝ → ℝ} {T : ℝ} (hc : ContinuousOn g (Set.Ico 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt g 0 t) : ∀ t ∈ Set.Ico 0 T, g t = g 0 := by
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · rw [← h]
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0:ℝ)) h
      (hc.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩))
      (fun x hx => hd x ⟨hx.1, lt_trans hx.2 ht.2⟩)
    have : (g t - g 0) / (t - 0) = 0 := hc2.symm
    rw [div_eq_zero_iff] at this
    rcases this with h1 | h1
    · linarith
    · exfalso; linarith

lemma part_i (hbar γ : ℝ) (hhbar : 0 < hbar) (hγ : 0 < γ)
    (ρ0 : Qmat) (hc : 0 < coherence ρ0) :
    ∀ (T : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat),
        ρ 0 = ρ0 → SolvesMaster hbar γ ω ρ T →
        (∀ t ∈ Set.Ico 0 T, coherence (ρ t) = coherence ρ0) →
        (∀ t ∈ Set.Ico 0 T,
            blochVec (ρ t) 2 ^ 2 = blochVec ρ0 2 ^ 2 - 2 * γ * coherence ρ0 * t) ∧
        T ≤ breakdownTime γ (blochVec ρ0) := by
  intro T ω ρ h0 hS hcoh
  obtain ⟨hB1, hB2⟩ := (bloch_equations hbar γ hhbar).2.1 ω ρ T hS
  have hz : ∀ i, ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun s => blochVec (ρ s) i)
      ((blochMatrix γ (ω t)).mulVec (blochVec (ρ t)) i) t :=
    fun i t ht => hasDerivAt_pi.1 (hB2 t ht) i
  set c0 := coherence ρ0 with hc0
  set g : ℝ → ℝ := fun t => blochVec (ρ t) 2 ^ 2 + 2 * γ * c0 * t with hg
  have hgc : ContinuousOn g (Set.Ico 0 T) := by
    have h2 := continuousOn_pi.1 hB1 2
    exact (h2.pow 2).add (continuousOn_const.mul continuousOn_id)
  have hgd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt g 0 t := by
    intro t ht
    have hnhds : Set.Ioo 0 T ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
    have hcd : HasDerivAt (fun s => blochVec (ρ s) 0 ^ 2 + blochVec (ρ s) 1 ^ 2)
        (2 * blochVec (ρ t) 0 * ((blochMatrix γ (ω t)).mulVec (blochVec (ρ t)) 0)
          + 2 * blochVec (ρ t) 1 * ((blochMatrix γ (ω t)).mulVec (blochVec (ρ t)) 1)) t := by
      have a0 := (hz 0 t ht).pow 2
      have a1 := (hz 1 t ht).pow 2
      refine HasDerivAt.congr_deriv (a0.add a1) ?_
      norm_num
    have hcc : HasDerivAt (fun s => blochVec (ρ s) 0 ^ 2 + blochVec (ρ s) 1 ^ 2) 0 t := by
      refine (hasDerivAt_const t c0).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with s hs
      exact hcoh s ⟨hs.1.le, hs.2⟩
    have hzero := hcd.unique hcc
    have hct := hcoh t ⟨ht.1.le, ht.2⟩
    have hz2 := ((hz 2 t ht).pow 2).add ((hasDerivAt_id t).const_mul (2 * γ * c0))
    refine HasDerivAt.congr_deriv hz2 ?_
    simp only [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hzero ⊢
    simp [coherence] at hct
    simp at hzero ⊢
    nlinarith [hzero, hct]
  have hconst := const_of_deriv_zero hgc hgd
  have key : ∀ t ∈ Set.Ico 0 T, blochVec (ρ t) 2 ^ 2 = blochVec ρ0 2 ^ 2 - 2 * γ * c0 * t := by
    intro t ht
    have := hconst t ht
    simp only [hg, h0] at this
    linarith
  refine ⟨key, ?_⟩
  by_contra hTb
  push_neg at hTb
  have hic : breakdownTime γ (blochVec ρ0) = blochVec ρ0 2 ^ 2 / (2 * γ * c0) := rfl
  have hpos : 0 < 2 * γ * c0 := by positivity
  have hb0 : 0 ≤ breakdownTime γ (blochVec ρ0) := by rw [hic]; positivity
  set tb := breakdownTime γ (blochVec ρ0)
  have hm : (tb + T) / 2 ∈ Set.Ico 0 T := ⟨by linarith, by linarith⟩
  have := key _ hm
  have h3 : tb * (2 * γ * c0) = blochVec ρ0 2 ^ 2 := by rw [hic]; field_simp
  nlinarith [sq_nonneg (blochVec (ρ ((tb + T) / 2)) 2)]

lemma sign_cases (x : ℝ) (hx : x ≠ 0) : Real.sign x = 1 ∨ Real.sign x = -1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · right; exact Real.sign_of_neg h
  · left; exact Real.sign_of_pos h

lemma track_deriv (γ : ℝ) (v0 : BVec) (ω0 : ℝ → ℝ) (hz0 : v0 2 ≠ 0) (t : ℝ)
    (ht : 0 < v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) :
    HasDerivAt (trackedBloch γ v0)
      ((blochMatrix γ (trackingFields γ v0 ω0 t)).mulVec (trackedBloch γ v0 t)) t := by
  have hf : HasDerivAt (fun s : ℝ => v0 2 ^ 2 - 2 * γ * initCoherence v0 * s)
      (-(2 * γ * initCoherence v0)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * γ * initCoherence v0)).const_sub (v0 2 ^ 2)
  have hsq := (hf.sqrt ht.ne').const_mul (Real.sign (v0 2))
  have hr := Real.sqrt_pos.2 ht
  have hr2 := Real.sq_sqrt ht.le
  refine hasDerivAt_pi.2 (fun i => ?_)
  fin_cases i
  · have e : (fun s => trackedBloch γ v0 s ⟨0, by norm_num⟩) = fun _ => v0 0 := by
      funext s; simp [trackedBloch]
    rw [e]
    refine (hasDerivAt_const t (v0 0)).congr_deriv ?_
    unfold trackedBloch trackingFields
    generalize √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) = r at hsq hr hr2 ⊢
    rcases sign_cases _ hz0 with hs | hs <;>
    · simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hs]
      field_simp
      ring
  · have e : (fun s => trackedBloch γ v0 s ⟨1, by norm_num⟩) = fun _ => v0 1 := by
      funext s; simp [trackedBloch]
    rw [e]
    refine (hasDerivAt_const t (v0 1)).congr_deriv ?_
    unfold trackedBloch trackingFields
    generalize √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) = r at hsq hr hr2 ⊢
    rcases sign_cases _ hz0 with hs | hs <;>
    · simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hs]
      field_simp
      ring
  · have e : (fun s => trackedBloch γ v0 s ⟨2, by norm_num⟩) =
        fun s => Real.sign (v0 2) * √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * s) := by
      funext s; simp [trackedBloch]
    rw [e]
    refine hsq.congr_deriv ?_
    unfold trackedBloch trackingFields
    generalize √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) = r at hsq hr hr2 ⊢
    rcases sign_cases _ hz0 with hs | hs <;>
    · simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hs, initCoherence]
      field_simp
      ring

lemma tracked_zero (γ : ℝ) (v0 : BVec) (hz0 : v0 2 ≠ 0) : trackedBloch γ v0 0 = v0 := by
  funext i
  fin_cases i
  · simp [trackedBloch]
  · simp [trackedBloch]
  · have : trackedBloch γ v0 0 ⟨2, by norm_num⟩ = Real.sign (v0 2) * |v0 2| := by
      simp [trackedBloch, Real.sqrt_sq_eq_abs]
    rw [this]
    show _ = v0 2
    rcases lt_or_gt_of_ne hz0 with h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring

lemma tracked_eq (γ : ℝ) (v0 : BVec) (hz0 : v0 2 ≠ 0) (t : ℝ)
    (ht : 0 < v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) :
    trackedBloch γ v0 t 0 = v0 0 ∧ trackedBloch γ v0 t 1 = v0 1 ∧
      trackedBloch γ v0 t 2 ^ 2 = v0 2 ^ 2 - 2 * γ * initCoherence v0 * t := by
  refine ⟨by simp [trackedBloch], by simp [trackedBloch], ?_⟩
  have : trackedBloch γ v0 t 2 = Real.sign (v0 2) * √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) := by
    simp [trackedBloch]
  rw [this, mul_pow, Real.sq_sqrt ht.le]
  rcases sign_cases _ hz0 with hs | hs <;> rw [hs] <;> ring

lemma part_ii (hbar γ : ℝ) (hhbar : 0 < hbar) (hγ : 0 < γ)
    (ρ0 : Qmat) (hρ0 : IsQubitState ρ0) (hc : 0 < coherence ρ0) :
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        trackedState γ (blochVec ρ0) 0 = ρ0 ∧
        ∀ t ∈ Set.Ico 0 (breakdownTime γ (blochVec ρ0)),
          IsQubitState (trackedState γ (blochVec ρ0) t) ∧
          coherence (trackedState γ (blochVec ρ0) t) = coherence ρ0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 0 = blochVec ρ0 0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 1 = blochVec ρ0 1 ∧
          HasDerivAt (trackedState γ (blochVec ρ0))
            (masterRHS hbar γ (trackingFields γ (blochVec ρ0) ω0 t)
              (trackedState γ (blochVec ρ0) t)) t) := by
  intro hz0 ω0
  obtain ⟨hP1, hP2, hP3⟩ := bloch_parametrization
  have hic : initCoherence (blochVec ρ0) = coherence ρ0 := rfl
  have hv0 : ∑ α, blochVec ρ0 α ^ 2 ≤ 1 := by
    have := (hP3 (blochVec ρ0)).1 (by rw [(hP1 ρ0 hρ0).1]; exact hρ0)
    exact this
  refine ⟨?_, ?_⟩
  · unfold trackedState
    rw [tracked_zero γ _ hz0]
    exact (hP1 ρ0 hρ0).1
  · intro t ht
    have hpos : 0 < 2 * γ * coherence ρ0 := by positivity
    have ha : 0 < blochVec ρ0 2 ^ 2 - 2 * γ * initCoherence (blochVec ρ0) * t := by
      rw [hic]
      have h1 : t < breakdownTime γ (blochVec ρ0) := ht.2
      have h2 : breakdownTime γ (blochVec ρ0) = blochVec ρ0 2 ^ 2 / (2 * γ * coherence ρ0) := rfl
      rw [h2, lt_div_iff₀ hpos] at h1
      linarith
    obtain ⟨e0, e1, e2⟩ := tracked_eq γ _ hz0 t ha
    have hb : ∀ α, blochVec (trackedState γ (blochVec ρ0) t) α = trackedBloch γ (blochVec ρ0) t α :=
      fun α => by unfold trackedState; rw [hP2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold trackedState
      rw [hP3]
      rw [Fin.sum_univ_three, e2, e0, e1]
      rw [Fin.sum_univ_three] at hv0
      simp only [initCoherence] at ha ⊢
      nlinarith [mul_pos hpos (lt_of_le_of_lt ht.1 ht.2 |> fun h => h), ht.1, hc, hγ,
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ.le) (mul_nonneg hc.le ht.1)]
    · simp only [coherence, hb, e0, e1]
    · rw [hb, e0]
    · rw [hb, e1]
    · exact hd_blochState hbar γ hhbar (track_deriv γ _ ω0 hz0 t ha)

lemma part_iii (γ : ℝ) (hγ : 0 < γ) (ρ0 : Qmat) (hc : 0 < coherence ρ0) :
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        Filter.Tendsto
          (fun t => trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 +
            trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2)
          (nhdsWithin (breakdownTime γ (blochVec ρ0)) (Set.Iio (breakdownTime γ (blochVec ρ0))))
          Filter.atTop) := by
  intro hz0 ω0
  set c0 := coherence ρ0 with hc0
  set tb := breakdownTime γ (blochVec ρ0) with htb
  have hpos : 0 < 2 * γ * c0 := by positivity
  have h3 : tb * (2 * γ * c0) = blochVec ρ0 2 ^ 2 := by
    rw [htb]; show blochVec ρ0 2 ^ 2 / (2 * γ * c0) * (2 * γ * c0) = _; field_simp
  have hlow : ∀ t < tb, γ / (2 * (tb - t)) ≤
      trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 + trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2 := by
    intro t ht
    have ha : 0 < blochVec ρ0 2 ^ 2 - 2 * γ * initCoherence (blochVec ρ0) * t := by
      have : initCoherence (blochVec ρ0) = c0 := rfl
      rw [this]; nlinarith
    have hr := Real.sqrt_pos.2 ha
    have hr2 := Real.sq_sqrt ha.le
    have hic : initCoherence (blochVec ρ0) = c0 := rfl
    have hs := sign_cases _ hz0
    have hsq : Real.sign (blochVec ρ0 2) ^ 2 = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
    have heq : trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 + trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2
        = (γ ^ 2 + ω0 t ^ 2) * c0 / (blochVec ρ0 2 ^ 2 - 2 * γ * initCoherence (blochVec ρ0) * t) := by
      unfold trackingFields
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, Matrix.head_cons]
      rw [div_pow, div_pow, mul_pow, mul_pow, hr2, hsq]
      simp only [hc0, coherence, initCoherence]
      field_simp
      ring
    rw [heq, hic]
    have hd : 0 < tb - t := by linarith
    have ha' : blochVec ρ0 2 ^ 2 - 2 * γ * c0 * t = 2 * γ * c0 * (tb - t) := by rw [← h3]; ring
    rw [ha']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ ω0 t ^ 2 := sq_nonneg _
    have hh : 0 ≤ ω0 t ^ 2 * c0 * (2 * (tb - t)) := by positivity
    nlinarith [hh]
  have hg : Filter.Tendsto (fun t => γ / (2 * (tb - t))) (nhdsWithin tb (Set.Iio tb)) Filter.atTop := by
    have h1 : Filter.Tendsto (fun t : ℝ => tb - t) (nhdsWithin tb (Set.Iio tb)) (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Filter.Tendsto (fun t : ℝ => tb - t) (nhds tb) (nhds (tb - tb)) :=
          (continuous_const.sub continuous_id).tendsto tb
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact sub_pos.2 (show t < tb from ht)
    have h2 := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h1
    have h3' := h2.const_mul_atTop (show 0 < γ / 2 by positivity)
    refine h3'.congr (fun t => ?_)
    simp only [Function.comp]
    rw [div_mul_eq_mul_div, mul_comm 2 (tb - t), div_mul_eq_div_div]
    ring
  refine Filter.tendsto_atTop_mono' _ ?_ hg
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hlow t (show t < tb from ht)

end CoherenceTracking.Dephasing

open CoherenceTracking.Dephasing

theorem solution (hbar γ : ℝ) (hhbar : 0 < hbar) (hγ : 0 < γ)
    (ρ0 : Qmat) (hρ0 : IsQubitState ρ0) (hc : 0 < coherence ρ0) :
    -- (i) no-go, (36)–(38): any controls, any constant-coherence solution of (32)
    (∀ (T : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat),
        ρ 0 = ρ0 → SolvesMaster hbar γ ω ρ T →
        (∀ t ∈ Set.Ico 0 T, coherence (ρ t) = coherence ρ0) →
        (∀ t ∈ Set.Ico 0 T,
            blochVec (ρ t) 2 ^ 2 = blochVec ρ0 2 ^ 2 - 2 * γ * coherence ρ0 * t) ∧
        T ≤ breakdownTime γ (blochVec ρ0)) ∧
    -- (ii) achievability, (37), (41)–(42): the tracked state solves (32) and keeps c on [0, t_b)
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        trackedState γ (blochVec ρ0) 0 = ρ0 ∧
        ∀ t ∈ Set.Ico 0 (breakdownTime γ (blochVec ρ0)),
          IsQubitState (trackedState γ (blochVec ρ0) t) ∧
          coherence (trackedState γ (blochVec ρ0) t) = coherence ρ0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 0 = blochVec ρ0 0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 1 = blochVec ρ0 1 ∧
          HasDerivAt (trackedState γ (blochVec ρ0))
            (masterRHS hbar γ (trackingFields γ (blochVec ρ0) ω0 t)
              (trackedState γ (blochVec ρ0) t)) t) ∧
    -- (iii) divergence of the control fields at t_b
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        Filter.Tendsto
          (fun t => trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 +
            trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2)
          (nhdsWithin (breakdownTime γ (blochVec ρ0)) (Set.Iio (breakdownTime γ (blochVec ρ0))))
          Filter.atTop) :=
  ⟨part_i hbar γ hhbar hγ ρ0 hc, part_ii hbar γ hhbar hγ ρ0 hρ0 hc, part_iii γ hγ ρ0 hc⟩
