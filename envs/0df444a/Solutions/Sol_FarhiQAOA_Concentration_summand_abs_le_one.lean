-- Prove2me | solution 1 for FarhiQAOA.Concentration.summand_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:15:01.908549+00:00
-- url     : https://prove2.me/submissions/c6126a96-ed07-450e-bdea-8e3bd285320f

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace Aux_FQ_sum1

open QAlgorithms Matrix

lemma pauliX_herm : (pauliX : Matrix Bool Bool ℂ).IsHermitian := by
  ext a b
  cases a <;> cases b <;> simp [pauliX, conjTranspose_apply]

lemma embedOp_herm {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : M.IsHermitian)
    (w : Fin k ↪ Fin n) : (embedOp M w).IsHermitian := by
  ext y z
  simp only [conjTranspose_apply, embedOp, Matrix.of_apply]
  have hC : (∀ a : Fin n, a ∉ Set.range w → z a = y a) ↔
      (∀ a : Fin n, a ∉ Set.range w → y a = z a) :=
    forall_congr' (fun a => imp_congr_right (fun _ => eq_comm))
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos (hC.mpr h), if_pos h]
    have := congrFun (congrFun hM (y ∘ w)) (z ∘ w)
    rw [conjTranspose_apply] at this
    exact this
  · rw [if_neg (fun h' => h (hC.mp h')), if_neg h, star_zero]

lemma mixer_herm (n : ℕ) : (qaoaMixer n).IsHermitian := by
  unfold qaoaMixer
  apply Finset.sum_induction _ (fun A : Matrix (Qubits n) (Qubits n) ℂ => A.IsHermitian)
  · intro a b ha hb; exact ha.add hb
  · exact isHermitian_zero
  · intro j _
    show (embedOp (Gate.ofMatrix1 pauliX).mat (Stabilizer.wire1 j)).IsHermitian
    apply embedOp_herm
    exact pauliX_herm.submatrix _

lemma ham_herm {n : ℕ} (h : Qubits n → ℝ) : (problemHamiltonian h).IsHermitian := by
  rw [problemHamiltonian, Matrix.isHermitian_diagonal_iff]
  intro z; simp [IsSelfAdjoint]

lemma exp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp (-(Complex.I * (t : ℂ)) • H) ∈ Matrix.unitaryGroup ι ℂ := by
  set A := -(Complex.I * (t : ℂ)) • H with hA
  have hAs : Aᴴ = -A := by
    rw [hA, conjTranspose_smul, hH.eq, ← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hAs,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel,
    NormedSpace.exp_zero]

lemma unitary_qaoa {n : ℕ} (f : Qubits n → ℝ) (p : ℕ) (β θ : Fin p → ℝ) :
    qaoaUnitary f p β θ ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  unfold qaoaUnitary orderedProd
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  exact Submonoid.mul_mem _ (exp_unitary _ (mixer_herm n) _) (exp_unitary _ (ham_herm f) _)

lemma uniform_norm (ι : Type*) [Fintype ι] [Nonempty ι] : ‖uniformState ι‖ = 1 := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsq : ‖uniformState ι‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold uniformState
    simp only [PiLp.toLp_apply]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : ‖((Real.sqrt (Fintype.card ι))⁻¹ : ℂ)‖ = (Real.sqrt (Fintype.card ι))⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [this, inv_pow, Real.sq_sqrt hN.le, mul_inv_cancel₀ hN.ne']
  have h0 := norm_nonneg (uniformState ι)
  nlinarith

lemma sum_prob {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ∑ z, prob ψ z = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro z _
  unfold prob ket
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

end Aux_FQ_sum1

open FarhiQAOA.Concentration in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (j k j' k' : Fin n) :
    |edgeCov G p γ β j k j' k'| ≤ 1 := by
  set ψ := FarhiQAOA.Cubic.qaoaState G p γ β with hψ
  have hS : ∑ z, QAlgorithms.prob ψ z = 1 := by
    rw [Aux_FQ_sum1.sum_prob, hψ]
    unfold FarhiQAOA.Cubic.qaoaState
    rw [QAlgorithms.act_norm_of_mem_unitaryGroup (Aux_FQ_sum1.unitary_qaoa _ _ _ _),
      Aux_FQ_sum1.uniform_norm]
    norm_num
  have hP : ∀ z, 0 ≤ QAlgorithms.prob ψ z := fun z => by unfold QAlgorithms.prob; positivity
  have hc : ∀ (a b : Fin n) (z : QAlgorithms.Qubits n), 0 ≤ FarhiQAOA.Cubic.edgeCut a b z ∧ FarhiQAOA.Cubic.edgeCut a b z ≤ 1 := by
    intro a b z
    unfold FarhiQAOA.Cubic.edgeCut
    split_ifs <;> norm_num
  have hbound : ∀ g : QAlgorithms.Qubits n → ℝ, (∀ z, 0 ≤ g z ∧ g z ≤ 1) →
      0 ≤ ∑ z, QAlgorithms.prob ψ z * g z ∧ ∑ z, QAlgorithms.prob ψ z * g z ≤ 1 := by
    intro g hg
    constructor
    · exact Finset.sum_nonneg (fun z _ => mul_nonneg (hP z) (hg z).1)
    · calc ∑ z, QAlgorithms.prob ψ z * g z ≤ ∑ z, QAlgorithms.prob ψ z :=
            Finset.sum_le_sum (fun z _ => by nlinarith [hP z, (hg z).1, (hg z).2])
        _ = 1 := hS
  have h1 := hbound (fun z => FarhiQAOA.Cubic.edgeCut j k z * FarhiQAOA.Cubic.edgeCut j' k' z)
    (fun z => ⟨mul_nonneg (hc j k z).1 (hc j' k' z).1,
      by nlinarith [(hc j k z).1, (hc j k z).2, (hc j' k' z).1, (hc j' k' z).2]⟩)
  have h2 := hbound (fun z => FarhiQAOA.Cubic.edgeCut j k z) (fun z => hc j k z)
  have h3 := hbound (fun z => FarhiQAOA.Cubic.edgeCut j' k' z) (fun z => hc j' k' z)
  unfold edgeCov edgePairTerm FarhiQAOA.Cubic.edgeTerm
  rw [← hψ]
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    mul_nonneg h2.1 h3.1, mul_le_one₀ h2.2 h3.1 h3.2]
