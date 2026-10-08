-- Prove2me | solution 1 for BlackwellDiscreteDP.Stationary.composition_rule
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:49:05.938138+00:00
-- url     : https://prove2.me/submissions/6e89d753-d300-47b6-802d-f12a342c40ea

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

set_option autoImplicit false

namespace BlackwellCompRuleAux

open BlackwellDiscreteDP.Stationary

variable {St Act : Type} [Fintype St] [DecidableEq St]

lemma Qn_cons (M : Model St Act) (f : St → Act) (π : Policy St Act) (n : ℕ) :
    M.Qn (Policy.cons f π) (n + 1) = M.Q f * M.Qn π n := by
  induction n with
  | zero =>
    show (1 : Matrix St St ℝ) * M.Q f = M.Q f * 1
    rw [one_mul, mul_one]
  | succ n ih =>
    have h1 : M.Qn (Policy.cons f π) (n + 1 + 1)
        = M.Qn (Policy.cons f π) (n + 1) * M.Q (π n) := rfl
    have h2 : M.Qn π (n + 1) = M.Qn π n * M.Q (π n) := rfl
    rw [h1, h2, ih, mul_assoc]

lemma norm_Q_mulVec_le (M : Model St Act) (f : St → Act) (v : St → ℝ) :
    ‖(M.Q f).mulVec v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun s => ?_
  have hk := M.law_kernel s (f s)
  have hv : ∀ s', |v s'| ≤ ‖v‖ := fun s' => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v s'
  have hexp : (M.Q f).mulVec v s = ∑ s', M.law s (f s) s' * v s' := rfl
  rw [Real.norm_eq_abs, hexp]
  calc |∑ s', M.law s (f s) s' * v s'| ≤ ∑ s', |M.law s (f s) s' * v s'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', M.law s (f s) s' * ‖v‖ := by
        apply Finset.sum_le_sum
        intro s' _
        rw [abs_mul, abs_of_nonneg (hk.1 s')]
        exact mul_le_mul_of_nonneg_left (hv s') (hk.1 s')
    _ = ‖v‖ := by rw [← Finset.sum_mul, hk.2, one_mul]

lemma norm_Qn_mulVec_le (M : Model St Act) (π : Policy St Act) (n : ℕ) (v : St → ℝ) :
    ‖(M.Qn π n).mulVec v‖ ≤ ‖v‖ := by
  induction n generalizing v with
  | zero =>
    show ‖(1 : Matrix St St ℝ).mulVec v‖ ≤ ‖v‖
    rw [Matrix.one_mulVec]
  | succ n ih =>
    show ‖(M.Qn π n * M.Q (π n)).mulVec v‖ ≤ ‖v‖
    rw [← Matrix.mulVec_mulVec]
    exact (ih _).trans (norm_Q_mulVec_le M _ v)

lemma norm_r_le [Fintype Act] (M : Model St Act) (f : St → Act) :
    ‖M.r f‖ ≤ ∑ s, ∑ a, |M.income s a| := by
  have hnn : 0 ≤ ∑ s, ∑ a, |M.income s a| :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun s => ?_
  rw [Real.norm_eq_abs]
  calc |M.r f s| = |M.income s (f s)| := rfl
    _ ≤ ∑ a, |M.income s a| :=
        Finset.single_le_sum (f := fun a => |M.income s a|) (fun a _ => abs_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ s, ∑ a, |M.income s a| :=
        Finset.single_le_sum (f := fun s => ∑ a, |M.income s a|)
          (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ s)

lemma summable_V [Fintype Act] (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (π : Policy St Act) :
    Summable (fun n : ℕ => β ^ n • (M.Qn π n).mulVec (M.r (π n))) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (∑ s, ∑ a, |M.income s a|)) fun n => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right ((norm_Qn_mulVec_le M π n _).trans (norm_r_le M _))
    (pow_nonneg hβ0 n)

lemma V_cons [Fintype Act] (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (f : St → Act) (π : Policy St Act) :
    M.V β (Policy.cons f π) = M.L β f (M.V β π) := by
  let T : (St → ℝ) →L[ℝ] (St → ℝ) :=
    LinearMap.toContinuousLinearMap (β • Matrix.mulVecLin (M.Q f))
  have hT : ∀ v, T v = β • (M.Q f).mulVec v := fun v => rfl
  have hs := summable_V M β hβ0 hβ1 (Policy.cons f π)
  have hsπ := summable_V M β hβ0 hβ1 π
  have h0 : β ^ 0 • (M.Qn (Policy.cons f π) 0).mulVec (M.r (Policy.cons f π 0)) = M.r f := by
    show β ^ 0 • (1 : Matrix St St ℝ).mulVec (M.r f) = M.r f
    rw [pow_zero, one_smul, Matrix.one_mulVec]
  have key : ∀ n : ℕ,
      β ^ (n + 1) • (M.Qn (Policy.cons f π) (n + 1)).mulVec (M.r (Policy.cons f π (n + 1)))
        = T (β ^ n • (M.Qn π n).mulVec (M.r (π n))) := by
    intro n
    rw [hT, Qn_cons, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, smul_smul, pow_succ, mul_comm]
    rfl
  have e : M.V β (Policy.cons f π)
      = ∑' n : ℕ, β ^ n • (M.Qn (Policy.cons f π) n).mulVec (M.r (Policy.cons f π n)) := rfl
  rw [e, hs.tsum_eq_zero_add, h0, tsum_congr key, ← T.map_tsum hsπ, hT]
  rfl

end BlackwellCompRuleAux

open BlackwellDiscreteDP.Stationary in
theorem solution {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ (f : St → Act) (π : Policy St Act),
        M.V β (Policy.cons f π) = M.L β f (M.V β π)) ∧
    (∀ (fs : List (St → Act)) (π : Policy St Act),
        M.V β (Policy.prepend fs π) = fs.foldr (fun f w => M.L β f w) (M.V β π)) := by
  refine ⟨fun f π => BlackwellCompRuleAux.V_cons M β hβ0 hβ1 f π, fun fs π => ?_⟩
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    show M.V β (Policy.cons f (Policy.prepend fs π)) = M.L β f (fs.foldr (fun f w => M.L β f w) (M.V β π))
    rw [BlackwellCompRuleAux.V_cons M β hβ0 hβ1, ih]
