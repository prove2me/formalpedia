-- Prove2me | solution 1 for BoundedParamMDP.IntervalEval.theorem13b_contraction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:24:58.130679+00:00
-- url     : https://prove2.me/submissions/caf7be71-9a67-4d34-a771-4798d20e01b6

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalValueIteration
set_option autoImplicit false
open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval

theorem ll_sumF {Q : Type*} [Fintype Q] (F : Q → ℝ) (h0 : ∀ q, 0 ≤ F q) (h1 : ∑ q, F q = 1)
    (w : Q → ℝ) : |∑ q, F q * w q| ≤ ‖w‖ := by
  calc |∑ q, F q * w q| ≤ ∑ q, |F q * w q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, F q * ‖w‖ := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        rw [abs_mul, abs_of_nonneg (h0 q)]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm w q) (h0 q)
    _ = ‖w‖ := by rw [← Finset.sum_mul, h1, one_mul]

theorem ll_vipol_diff {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) (u v : Q → ℝ)
    (p : Q) : |VIpol M π v p - VIpol M π u p| ≤ M.γ * ‖v - u‖ := by
  have : VIpol M π v p - VIpol M π u p = M.γ * ∑ q, M.F p (π p) q * (v - u) q := by
    simp only [VIpol, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
  rw [this, abs_mul, abs_of_nonneg M.γ_nonneg]
  exact mul_le_mul_of_nonneg_left (ll_sumF _ (M.F_nonneg p (π p)) (M.F_sum p (π p)) _) M.γ_nonneg

theorem ll_vipol_bnd {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A) (v : Q → ℝ)
    (p : Q) : |VIpol M π v p - M.R p| ≤ M.γ * ‖v‖ := by
  have : VIpol M π v p - M.R p = M.γ * ∑ q, M.F p (π p) q * v q := by
    simp only [VIpol]; ring
  rw [this, abs_mul, abs_of_nonneg M.γ_nonneg]
  exact mul_le_mul_of_nonneg_left (ll_sumF _ (M.F_nonneg p (π p)) (M.F_sum p (π p)) _) M.γ_nonneg

theorem ll_iInf_dist {ι : Type*} (a b : ι → ℝ) (ha : BddBelow (Set.range a))
    (hb : BddBelow (Set.range b)) (d : ℝ) (hd0 : 0 ≤ d) (h : ∀ i, |a i - b i| ≤ d) :
    |(⨅ i, a i) - ⨅ i, b i| ≤ d := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iInf_of_isEmpty, sub_self, abs_zero]
    exact hd0
  · have h1 : (⨅ i, a i) - d ≤ ⨅ i, b i := by
      refine le_ciInf (fun i => ?_)
      have := (abs_le.mp (h i)).2
      have := ciInf_le ha i
      linarith
    have h2 : (⨅ i, b i) - d ≤ ⨅ i, a i := by
      refine le_ciInf (fun i => ?_)
      have := (abs_le.mp (h i)).1
      have := ciInf_le hb i
      linarith
    rw [abs_le]; constructor <;> linarith

theorem ll_iSup_dist {ι : Type*} (a b : ι → ℝ) (ha : BddAbove (Set.range a))
    (hb : BddAbove (Set.range b)) (d : ℝ) (hd0 : 0 ≤ d) (h : ∀ i, |a i - b i| ≤ d) :
    |(⨆ i, a i) - ⨆ i, b i| ≤ d := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty, sub_self, abs_zero]
    exact hd0
  · have h1 : (⨆ i, a i) ≤ (⨆ i, b i) + d := by
      refine ciSup_le (fun i => ?_)
      have := (abs_le.mp (h i)).2
      have := le_ciSup hb i
      linarith
    have h2 : (⨆ i, b i) ≤ (⨆ i, a i) + d := by
      refine ciSup_le (fun i => ?_)
      have := (abs_le.mp (h i)).1
      have := le_ciSup ha i
      linarith
    rw [abs_le]; constructor <;> linarith


theorem ll_lex {A : Type*} [Fintype A] [Nonempty A] (a b : A → ℝ) :
    IsGreatest (Set.range a) (ofLex (Finset.univ.sup' Finset.univ_nonempty
        (fun α : A => toLex (a α, b α)))).1 ∧
    IsGreatest (b '' {α | ∀ β, a β ≤ a α}) (ofLex (Finset.univ.sup' Finset.univ_nonempty
        (fun α : A => toLex (a α, b α)))).2 := by
  obtain ⟨α0, -, h0⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset A))
    Finset.univ_nonempty (fun α : A => toLex (a α, b α))
  rw [h0]
  simp only [ofLex_toLex]
  have hle : ∀ α, toLex (a α, b α) ≤ toLex (a α0, b α0) := by
    intro α
    rw [← h0]
    exact Finset.le_sup' (fun α : A => toLex (a α, b α)) (Finset.mem_univ α)
  have ha : ∀ α, a α ≤ a α0 := by
    intro α
    have := hle α
    rw [Prod.Lex.le_iff] at this
    rcases this with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  refine ⟨⟨⟨α0, rfl⟩, ?_⟩, ⟨⟨α0, fun β => ha β, rfl⟩, ?_⟩⟩
  · rintro _ ⟨α, rfl⟩; exact ha α
  · rintro _ ⟨α, hα, rfl⟩
    have h1 : a α = a α0 := le_antisymm (ha α) (hα α0)
    have := hle α
    rw [Prod.Lex.le_iff] at this
    rcases this with h | ⟨_, h⟩
    · exact absurd h (by simp [h1])
    · exact h

theorem ll_max_dist {A : Type*} (S : Set A) (g h : A → ℝ) (m1 m2 : ℝ)
    (h1 : IsGreatest (g '' S) m1) (h2 : IsGreatest (h '' S) m2) (d : ℝ)
    (hd : ∀ α, |g α - h α| ≤ d) : |m1 - m2| ≤ d := by
  obtain ⟨⟨α1, hα1, rfl⟩, hu1⟩ := h1
  obtain ⟨⟨α2, hα2, rfl⟩, hu2⟩ := h2
  have a1 := hu1 ⟨α2, hα2, rfl⟩
  have a2 := hu2 ⟨α1, hα1, rfl⟩
  have b1 := abs_le.mp (hd α1)
  have b2 := abs_le.mp (hd α2)
  rw [abs_le]; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

theorem ll_viact_diff {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (α : A)
    (u v : Q → ℝ) (p : Q) (M : Member B) :
    |VIact M.1 α v p - VIact M.1 α u p| ≤ B.γ * ‖v - u‖ := by
  have := ll_vipol_diff M.1 (fun _ => α) u v p
  rw [M.2.2.1] at this
  exact this

theorem ll_viact_bnd {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (α : A)
    (v : Q → ℝ) (p : Q) (M : Member B) :
    |VIact M.1 α v p - B.R p| ≤ B.γ * ‖v‖ := by
  have := ll_vipol_bnd M.1 (fun _ => α) v p
  rw [M.2.1, M.2.2.1] at this
  exact this

theorem ll_inf_act {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (α : A)
    (u v : Q → ℝ) (p : Q) :
    |(⨅ M : Member B, VIact M.1 α v p) - ⨅ M : Member B, VIact M.1 α u p| ≤ B.γ * ‖v - u‖ := by
  refine ll_iInf_dist _ _ ?_ ?_ _ (mul_nonneg B.γ_nonneg (norm_nonneg _))
    (fun M => ll_viact_diff B α u v p M)
  · refine ⟨B.R p - B.γ * ‖v‖, ?_⟩
    rintro _ ⟨M, rfl⟩
    have := (abs_le.mp (ll_viact_bnd B α v p M)).1; linarith
  · refine ⟨B.R p - B.γ * ‖u‖, ?_⟩
    rintro _ ⟨M, rfl⟩
    have := (abs_le.mp (ll_viact_bnd B α u p M)).1; linarith

theorem ll_sup_act {Q A : Type*} [Fintype Q] (B : BoundedParamMDP.Optimal.BMDP Q A) (α : A)
    (u v : Q → ℝ) (p : Q) :
    |(⨆ M : Member B, VIact M.1 α v p) - ⨆ M : Member B, VIact M.1 α u p| ≤ B.γ * ‖v - u‖ := by
  refine ll_iSup_dist _ _ ?_ ?_ _ (mul_nonneg B.γ_nonneg (norm_nonneg _))
    (fun M => ll_viact_diff B α u v p M)
  · refine ⟨B.R p + B.γ * ‖v‖, ?_⟩
    rintro _ ⟨M, rfl⟩
    have := (abs_le.mp (ll_viact_bnd B α v p M)).2; linarith
  · refine ⟨B.R p + B.γ * ‖u‖, ?_⟩
    rintro _ ⟨M, rfl⟩
    have := (abs_le.mp (ll_viact_bnd B α u p M)).2; linarith

theorem solution {Q A : Type*} [Fintype Q] [Fintype A] [Nonempty A]
    (B : BoundedParamMDP.Optimal.BMDP Q A) (V : Q → ℝ) :
    IsContraction (IVIloOptV B V) ∧ IsContraction (IVIhiPesV B V) := by
  have hg : 0 ≤ B.γ := B.γ_nonneg
  refine ⟨⟨B.γ, hg, B.γ_lt_one, fun u v => ?_⟩, ⟨B.γ, hg, B.γ_lt_one, fun u v => ?_⟩⟩
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hg (norm_nonneg _))]
    intro p
    rw [Real.norm_eq_abs, Pi.sub_apply]
    have h1 := (ll_lex (fun α => (candInterval B (v, V) p α).2)
      (fun α => (candInterval B (v, V) p α).1)).2
    have h2 := (ll_lex (fun α => (candInterval B (u, V) p α).2)
      (fun α => (candInterval B (u, V) p α).1)).2
    exact ll_max_dist _ _ _ _ _ h1 h2 _ (fun α => ll_inf_act B α u v p)
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hg (norm_nonneg _))]
    intro p
    rw [Real.norm_eq_abs, Pi.sub_apply]
    have h1 := (ll_lex (fun α => (candInterval B (V, v) p α).1)
      (fun α => (candInterval B (V, v) p α).2)).2
    have h2 := (ll_lex (fun α => (candInterval B (V, u) p α).1)
      (fun α => (candInterval B (V, u) p α).2)).2
    exact ll_max_dist _ _ _ _ _ h1 h2 _ (fun α => ll_sup_act B α u v p)
