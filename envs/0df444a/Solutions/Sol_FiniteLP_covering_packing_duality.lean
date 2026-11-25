-- Prove2me | solution 1 for FiniteLP.covering_packing_duality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:25.150813+00:00
-- url     : https://prove2.me/submissions/6ab9189c-7471-4830-a388-6da38d085e0e

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_FiniteLP_farkas_ge
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (r : ι → ℝ)
    (hA : ∀ e t, 0 ≤ A e t) (hr : ∀ e, 0 ≤ r e)
    (hcol : ∀ t, ∃ e, 0 < A e t) :
    ∃ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, (∑ t, A e t * w t) ≤ r e) ∧
      (∑ t, w t) = sInf {v : ℝ | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧
        (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
  by_contra h_no_wstar;
  -- By definition of $P$, we know that for any $w \in Q$, $\sum t, w t \leq Mr$.
  have hP_le_Mr : ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    intro w hw;
    refine' le_csInf _ _;
    · refine' ⟨ _, ⟨ fun e => ∑ t, 1 / A e t, _, _, rfl ⟩ ⟩;
      · exact fun e => Finset.sum_nonneg fun t _ => one_div_nonneg.2 ( hA e t );
      · intro t; obtain ⟨ e, he ⟩ := hcol t; refine' le_trans _ ( Finset.single_le_sum ( fun e _ => mul_nonneg ( hA e t ) ( Finset.sum_nonneg fun t _ => one_div_nonneg.mpr ( hA e t ) ) ) ( Finset.mem_univ e ) ) ; simp +decide [ he.ne', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
        exact le_trans ( by norm_num [ he.ne' ] ) ( Finset.single_le_sum ( fun i _ => mul_nonneg he.le ( inv_nonneg.2 ( hA e i ) ) ) ( Finset.mem_univ t ) );
    · rintro _ ⟨ x, hx₁, hx₂, rfl ⟩;
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ t, w t * (∑ e, A e t * x e) = ∑ e, (∑ t, A e t * w t) * x e := by
        simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm;
      exact le_trans ( Finset.sum_le_sum fun t _ => le_mul_of_one_le_right ( hw.1 t ) ( hx₂ t ) ) ( h_fubini.le.trans ( Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right ( hw.2 e ) ( hx₁ e ) ) );
  -- By definition of $P$, we know that there exists a maximum packing $w^* \in Q$ such that $\sum t, w^* t = P$.
  obtain ⟨w_star, hw_star⟩ : ∃ w_star : κ → ℝ, (∀ t, 0 ≤ w_star t) ∧ (∀ e, ∑ t, A e t * w_star t ≤ r e) ∧ ∀ w : κ → ℝ, (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e) → ∑ t, w t ≤ ∑ t, w_star t := by
    have h_compact : IsCompact {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)} := by
      refine' CompactIccSpace.isCompact_Icc.of_isClosed_subset _ _;
      exact fun t => 0;
      exact fun t => sInf { v | ∃ x : ι → ℝ, ( ∀ e, 0 ≤ x e ) ∧ ( ∀ t, 1 ≤ ∑ e, A e t * x e ) ∧ v = ∑ e, r e * x e };
      · simp +decide only [Set.ofPred_and, Set.ofPred_forall];
        exact IsClosed.inter ( isClosed_iInter fun _ => isClosed_le continuous_const <| continuous_apply _ ) ( isClosed_iInter fun _ => isClosed_le ( continuous_finsetSum _ fun _ _ => continuous_const.mul <| continuous_apply _ ) continuous_const );
      · exact fun w hw => ⟨ hw.1, fun t => le_trans ( Finset.single_le_sum ( fun a _ => hw.1 a ) ( Finset.mem_univ t ) ) ( hP_le_Mr w hw ) ⟩;
    have h_nonempty : {w : κ → ℝ | (∀ t, 0 ≤ w t) ∧ (∀ e, ∑ t, A e t * w t ≤ r e)}.Nonempty := by
      exact ⟨ fun _ => 0, fun _ => le_rfl, fun _ => by simp +decide [ hr ] ⟩;
    have := h_compact.exists_isMaxOn h_nonempty ( show ContinuousOn ( fun w : κ → ℝ => ∑ t, w t ) _ from Continuous.continuousOn <| continuous_finsetSum _ fun _ _ => continuous_apply _ );
    exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.1.2, fun w hw => this.choose_spec.2 hw ⟩;
  -- By definition of $P$, we know that $P < Mr$.
  have hP_lt_Mr : ∑ t, w_star t < sInf {v | ∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ v = ∑ e, r e * x e} := by
    exact lt_of_le_of_ne ( hP_le_Mr w_star ⟨ hw_star.1, hw_star.2.1 ⟩ ) fun h => h_no_wstar ⟨ w_star, hw_star.1, hw_star.2.1, h ⟩;
  -- By definition of $P$, we know that there exists a Farkas certificate $y$ such that $y \geq 0$, $\sum_{e} N'_{ie} y_i \leq 0$ for all $e$, and $\sum_{i} c'_i y_i > 0$.
  obtain ⟨y, hy_nonneg, hy_row, hy_obj⟩ : ∃ y : κ ⊕ Unit → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ e, ∑ i, (Sum.elim (fun t e => A e t) (fun _ e => -r e) i e) * y i ≤ 0) ∧ 0 < ∑ i, (Sum.elim (fun _ => 1) (fun _ => -∑ t, w_star t) i) * y i := by
    have h_farkas : ¬∃ x : ι → ℝ, (∀ e, 0 ≤ x e) ∧ (∀ t, 1 ≤ ∑ e, A e t * x e) ∧ ∑ e, r e * x e ≤ ∑ t, w_star t := by
      contrapose! hP_lt_Mr;
      exact le_trans ( csInf_le ⟨ 0, by rintro v ⟨ x, hx₁, hx₂, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hr _ ) ( hx₁ _ ) ⟩ ⟨ hP_lt_Mr.choose, hP_lt_Mr.choose_spec.1, hP_lt_Mr.choose_spec.2.1, rfl ⟩ ) hP_lt_Mr.choose_spec.2.2;
    convert farkas_ge ( fun i e => Sum.elim ( fun t e => A e t ) ( fun _ e => -r e ) i e ) ( fun i => Sum.elim ( fun _ => 1 ) ( fun _ => -∑ t, w_star t ) i ) _ using 1;
    simp +zetaDelta at *;
    exact h_farkas;
  -- Let $lam t = y (Sum.inl t)$ and $mu = y (Sum.inr ())$.
  set lam : κ → ℝ := fun t => y (Sum.inl t)
  set mu : ℝ := y (Sum.inr ());
  -- By definition of $lam$ and $mu$, we have $\sum_{t} A_{et} lam_t \leq mu r_e$ for all $e$ and $\sum_{t} lam_t > mu P$.
  have hlam_mu : ∀ e, ∑ t, A e t * lam t ≤ mu * r e := by
    intro e; specialize hy_row e; simp +decide [ Finset.sum_add_distrib, mul_comm ] at hy_row ⊢;
    exact hy_row
  have hlam_mu_P : ∑ t, lam t > mu * ∑ t, w_star t := by
    simp +zetaDelta at *;
    linarith;
  -- If $mu = 0$, then from $hlam_mu$, we have $\sum_{t} A_{et} lam_t \leq 0$ for all $e$, which implies $lam_t = 0$ for all $t$.
  by_cases hmu_zero : mu = 0;
  · simp +zetaDelta at *;
    simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_nonneg ];
    exact hy_obj.ne' ( Finset.sum_eq_zero fun t ht => le_antisymm ( le_of_not_gt fun h => by have := hy_row ( Classical.choose ( hcol t ) ) ; exact not_le_of_gt ( lt_of_lt_of_le ( mul_pos ( Classical.choose_spec ( hcol t ) ) h ) ( Finset.single_le_sum ( fun a _ => mul_nonneg ( hA _ a ) ( hy_nonneg a ) ) ht ) ) this ) ( hy_nonneg t ) );
  · -- Since $mu > 0$, we can divide both sides of $hlam_mu$ by $mu$ to get $\sum_{t} A_{et} (lam_t / mu) \leq r_e$ for all $e$.
    have hlam_mu_div : ∀ e, ∑ t, A e t * (lam t / mu) ≤ r e := by
      simp +decide only [← mul_div_assoc, ← sum_div];
      exact fun e => div_le_iff₀' ( lt_of_le_of_ne ( hy_nonneg _ ) ( Ne.symm hmu_zero ) ) |>.2 ( hlam_mu e );
    -- Since $mu > 0$, we can divide both sides of $hlam_mu_P$ by $mu$ to get $\sum_{t} (lam_t / mu) > \sum_{t} w_star t$.
    have hlam_mu_div_P : ∑ t, (lam t / mu) > ∑ t, w_star t := by
      rw [ ← Finset.sum_div _ _ _, gt_iff_lt, lt_div_iff₀ ] <;> cases lt_or_gt_of_ne hmu_zero <;> nlinarith [ hy_nonneg ( Sum.inr () ) ];
    exact not_le_of_gt hlam_mu_div_P ( hw_star.2.2 _ ⟨ fun t => div_nonneg ( hy_nonneg _ ) ( hy_nonneg _ ), hlam_mu_div ⟩ )
end FiniteLP
