-- Prove2me | solution 1 for EkelandVP.General.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:06:15.514543+00:00
-- url     : https://prove2.me/submissions/51295cd8-ec9e-4353-8794-1bf34190919c

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE



namespace EkelandVP.General

theorem bpLE_refl_x {V : Type*} [MetricSpace V] (α : ℝ) (p : V × ℝ) : bpLE α p p := by
  unfold bpLE; simp

theorem bpLE_trans_x {V : Type*} [MetricSpace V] (α : ℝ) (hα : 0 < α) {p q r : V × ℝ}
    (h1 : bpLE α p q) (h2 : bpLE α q r) : bpLE α p r := by
  unfold bpLE at *
  have := dist_triangle p.1 q.1 r.1
  nlinarith

theorem lemma_1_2_core {V : Type*} [MetricSpace V] [CompleteSpace V] (α : ℝ) (hα : 0 < α)
    (S : Set (V × ℝ)) (hS : IsClosed S) (hm : ∃ m : ℝ, ∀ p ∈ S, m ≤ p.2)
    (p₁ : V × ℝ) (hp₁ : p₁ ∈ S) :
    ∃ q ∈ S, bpLE α p₁ q ∧ ∀ r ∈ S, bpLE α q r → r = q := by
  classical
  obtain ⟨m, hm⟩ := hm
  let T : V × ℝ → Set (V × ℝ) := fun p => {r | r ∈ S ∧ bpLE α p r}
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
      have hne : (Prod.snd '' T p).Nonempty := ⟨p.2, p, ⟨hp, bpLE_refl_x α p⟩, rfl⟩
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
    exact ⟨hr.1, bpLE_trans_x α hα (hstep _ (hPS n) n).1.2 hr.2⟩
  have hTanti : ∀ n k, n ≤ k → T (P k) ⊆ T (P n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hTsub k).trans ih
  have hmemT : ∀ n, P n ∈ T (P n) := fun n => ⟨hPS n, bpLE_refl_x α _⟩
  -- key bound
  have hbound : ∀ n, ∀ r ∈ T (P (n+1)), dist r (P (n+1)) ≤ (1/α + 1) * (1 / ((n:ℝ) + 1)) := by
    intro n r hr
    have h1 := hstep _ (hPS n) n
    rw [← hPs] at h1
    have hrn : r ∈ T (P n) := hTsub n hr
    have hI := hIle _ _ hrn
    have hb := hr.2
    unfold bpLE at hb
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
  have hrT : ∀ n, r ∈ T (P n) := fun n => ⟨hr, bpLE_trans_x α hα (hqT n).2 hqr⟩
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

open EkelandVP.General


theorem solution {V : Type*} [MetricSpace V] [CompleteSpace V] (α : ℝ) (hα : 0 < α)
    (S : Set (V × ℝ)) (hS : IsClosed S) (hm : ∃ m : ℝ, ∀ p ∈ S, m ≤ p.2)
    (p₁ : V × ℝ) (hp₁ : p₁ ∈ S) :
    ∃ q ∈ S, bpLE α p₁ q ∧ ∀ r ∈ S, bpLE α q r → r = q := by
  exact lemma_1_2_core α hα S hS hm p₁ hp₁
