-- Prove2me | solution 1 for EkelandVP.Constraints.ekeland_point_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:34:03.775084+00:00
-- url     : https://prove2.me/submissions/fc292c16-b14e-4e55-a1d8-7a84d9134647

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet

set_option autoImplicit false

/-! The Bishop-Phelps-type lemma `lemma_1_2_x` below (with `bpLEx`, `bpLEx_refl_x`,
`bpLEx_trans_x`) is reused verbatim from the accepted solution of
`EkelandVP.General.ekeland_variational_principle` by @mrfancypants
(https://prove2.me/submissions/cac7bea7-ee68-4eff-8a2c-c3069a0eb6db).
The rest of this file is my own derivation of the statement. -/

namespace EkelandVP.General

def bpLEx {V : Type*} [MetricSpace V] (α : ℝ) (p q : V × ℝ) : Prop :=
  (q.2 - p.2) + α * dist p.1 q.1 ≤ 0

theorem bpLEx_refl_x {V : Type*} [MetricSpace V] (α : ℝ) (p : V × ℝ) : bpLEx α p p := by
  unfold bpLEx; simp

theorem bpLEx_trans_x {V : Type*} [MetricSpace V] (α : ℝ) (hα : 0 < α) {p q r : V × ℝ}
    (h1 : bpLEx α p q) (h2 : bpLEx α q r) : bpLEx α p r := by
  unfold bpLEx at *
  have := dist_triangle p.1 q.1 r.1
  nlinarith

theorem lemma_1_2_x {V : Type*} [MetricSpace V] [CompleteSpace V] (α : ℝ) (hα : 0 < α)
    (S : Set (V × ℝ)) (hS : IsClosed S) (hm : ∃ m : ℝ, ∀ p ∈ S, m ≤ p.2)
    (p₁ : V × ℝ) (hp₁ : p₁ ∈ S) :
    ∃ q ∈ S, bpLEx α p₁ q ∧ ∀ r ∈ S, bpLEx α q r → r = q := by
  classical
  obtain ⟨m, hm⟩ := hm
  let T : V × ℝ → Set (V × ℝ) := fun p => {r | r ∈ S ∧ bpLEx α p r}
  have hTc : ∀ p, IsClosed (T p) := by
    intro p
    refine hS.inter (isClosed_le (f := fun r : V × ℝ => (r.2 - p.2) + α * dist p.1 r.1) ?_ continuous_const)
    fun_prop
  let I : V × ℝ → ℝ := fun p => sInf (Prod.snd '' T p)
  let step : V × ℝ → ℕ → V × ℝ := fun p n =>
    if h : ∃ r ∈ T p, r.2 < I p + 1 / ((n:ℝ) + 1) then h.choose else p
  have hstep : ∀ p ∈ S, ∀ n, step p n ∈ T p ∧ (step p n).2 < I p + 1 / ((n:ℝ) + 1) := by
    intro p hp n
    have hex : ∃ r ∈ T p, r.2 < I p + 1 / ((n:ℝ) + 1) := by
      have hne : (Prod.snd '' T p).Nonempty := ⟨p.2, p, ⟨hp, bpLEx_refl_x α p⟩, rfl⟩
      have := exists_lt_of_csInf_lt hne
        (show I p < I p + 1 / ((n:ℝ) + 1) by
          have : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
          linarith)
      obtain ⟨_, ⟨r, hr, rfl⟩, hlt⟩ := this
      exact ⟨r, hr, hlt⟩
    simp only [step, dif_pos hex]
    exact hex.choose_spec
  have hIle : ∀ p r, r ∈ T p → I p ≤ r.2 := by
    intro p r hr
    exact csInf_le ⟨m, by rintro _ ⟨x, hx, rfl⟩; exact hm x hx.1⟩ ⟨r, hr, rfl⟩
  let P : ℕ → V × ℝ := fun n => Nat.rec p₁ (fun k pk => step pk k) n
  have hP0 : P 0 = p₁ := rfl
  have hPs : ∀ n, P (n+1) = step (P n) n := fun n => rfl
  have hPS : ∀ n, P n ∈ S := by
    intro n
    induction n with
    | zero => exact hp₁
    | succ k ih => rw [hPs]; exact (hstep _ ih k).1.1
  have hTsub : ∀ n, T (P (n+1)) ⊆ T (P n) := by
    intro n r hr
    exact ⟨hr.1, bpLEx_trans_x α hα (hstep _ (hPS n) n).1.2 hr.2⟩
  have hTanti : ∀ n k, n ≤ k → T (P k) ⊆ T (P n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hTsub k).trans ih
  have hmemT : ∀ n, P n ∈ T (P n) := fun n => ⟨hPS n, bpLEx_refl_x α _⟩
  -- key bound
  have hbound : ∀ n, ∀ r ∈ T (P (n+1)), dist r (P (n+1)) ≤ (1/α + 1) * (1 / ((n:ℝ) + 1)) := by
    intro n r hr
    have h1 := hstep _ (hPS n) n
    rw [← hPs] at h1
    have hrn : r ∈ T (P n) := hTsub n hr
    have hI := hIle _ _ hrn
    have hb := hr.2
    unfold bpLEx at hb
    have hd := dist_nonneg (x := (P (n+1)).1) (y := r.1)
    have hε : (0:ℝ) < 1 / ((n:ℝ)+1) := by positivity
    rw [Prod.dist_eq, Real.dist_eq, dist_comm]
    have hαd : dist (P (n+1)).1 r.1 ≤ 1/α * (1 / ((n:ℝ) + 1)) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hα]
      nlinarith
    have hy : |r.2 - (P (n+1)).2| ≤ 1 / ((n:ℝ) + 1) := by
      rw [abs_le]; constructor <;> nlinarith
    have : 0 ≤ 1/α * (1 / ((n:ℝ) + 1)) := by positivity
    apply max_le <;> nlinarith
  have hδ : Filter.Tendsto (fun n : ℕ => (1/α + 1) * (1 / ((n:ℝ) + 1))) Filter.atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this.const_mul (1/α + 1)
  have hcau : CauchySeq P := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ) ε hε
    refine ⟨N+1, fun k hk => ?_⟩
    have := hbound N (P k) (hTanti (N+1) k hk (hmemT k))
    have h2 := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at h2
    exact lt_of_le_of_lt this (lt_of_le_of_lt (le_abs_self _) h2)
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hcau
  have hqT : ∀ n, q ∈ T (P n) := by
    intro n
    apply (hTc (P n)).mem_of_tendsto hq
    rw [Filter.eventually_atTop]
    exact ⟨n, fun k hk => hTanti n k hk (hmemT k)⟩
  refine ⟨q, (hqT 0).1, (hqT 0).2, fun r hr hqr => ?_⟩
  have hrT : ∀ n, r ∈ T (P n) := fun n => ⟨hr, bpLEx_trans_x α hα (hqT n).2 hqr⟩
  apply dist_le_zero.1
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ) (ε/2) (by linarith)
  have h2 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h2
  have a1 := hbound N r (hrT (N+1))
  have a2 := hbound N q (hqT (N+1))
  have := dist_triangle_right r q (P (N+1))
  have := le_abs_self ((1/α + 1) * (1 / ((N:ℝ) + 1)))
  linarith

end EkelandVP.General

open EkelandVP.General EkelandVP.Constraints

lemma ekv_feasible_closed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ} (p : ℕ)
    (G : Fin m → V → ℝ) (hG : ∀ i, Continuous (G i)) : IsClosed (feasibleSet p G) := by
  have : feasibleSet p G = ⋂ i : Fin m, {v | (i.val < p → G i v = 0) ∧ (p ≤ i.val → 0 ≤ G i v)} := by
    ext v; simp [feasibleSet]
  rw [this]
  refine isClosed_iInter fun i => ?_
  by_cases h : i.val < p
  · have h' : ¬ p ≤ i.val := not_le.2 h
    simp only [h, h', true_implies, false_implies, and_true]
    exact isClosed_eq (hG i) continuous_const
  · have h' : p ≤ i.val := not_lt.1 h
    simp only [h, h', false_implies, true_implies, true_and]
    exact isClosed_le continuous_const (hG i)

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {m : ℕ} (p : ℕ) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∀ w ∈ feasibleSet p G, F v - ε * ‖w - v‖ ≤ F w := by
  set C := feasibleSet p G with hC
  have hFc : Continuous F := hF.continuous
  have hCc : IsClosed C := ekv_feasible_closed p G (fun i => (hG i).continuous)
  obtain ⟨m0, hm0⟩ := hbdd
  set I := sInf (F '' C) with hI
  have hne' : (F '' C).Nonempty := hne.image F
  have hIle : ∀ w ∈ C, I ≤ F w := fun w hw => csInf_le ⟨m0, hm0⟩ ⟨w, hw, rfl⟩
  have hε2 : 0 < ε ^ 2 := by positivity
  have hIlt : I < I + ε ^ 2 := by linarith
  obtain ⟨_, ⟨u, huC, rfl⟩, hu⟩ := exists_lt_of_csInf_lt hne' hIlt
  let S : Set (V × ℝ) := {q | q.1 ∈ C ∧ F q.1 ≤ q.2}
  have hS : IsClosed S := by
    refine IsClosed.inter (hCc.preimage continuous_fst) ?_
    exact isClosed_le (hFc.comp continuous_fst) continuous_snd
  have hmS : ∃ m' : ℝ, ∀ q ∈ S, m' ≤ q.2 := ⟨m0, fun q hq => (hm0 ⟨q.1, hq.1, rfl⟩).trans hq.2⟩
  have hp₁ : (u, F u) ∈ S := ⟨huC, le_rfl⟩
  obtain ⟨q, hqS, hpq, hmax⟩ := lemma_1_2_x ε hε S hS hmS (u, F u) hp₁
  have hq2 : q.2 = F q.1 := by
    have := hmax (q.1, F q.1) ⟨hqS.1, le_rfl⟩ (by unfold bpLEx; simp; linarith [hqS.2])
    rw [← this]
  unfold bpLEx at hpq
  simp only at hpq
  rw [hq2] at hpq
  have hd0 := dist_nonneg (x := u) (y := q.1)
  refine ⟨q.1, hqS.1, fun w hw => ?_, fun w hw => ?_⟩
  · have := hIle w hw
    nlinarith
  · by_contra hcon
    push_neg at hcon
    have := hmax (w, F w) ⟨hw, le_rfl⟩ (by
      have hd : dist q.1 w = ‖w - q.1‖ := by rw [dist_comm, dist_eq_norm]
      unfold bpLEx; simp only; rw [hq2, hd]
      linarith [hcon])
    have hw' : w = q.1 := congrArg Prod.fst this
    rw [hw', sub_self, norm_zero] at hcon
    linarith
