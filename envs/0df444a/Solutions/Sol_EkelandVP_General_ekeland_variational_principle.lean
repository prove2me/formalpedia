-- Prove2me | solution 1 for EkelandVP.General.ekeland_variational_principle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:07:36.540925+00:00
-- url     : https://prove2.me/submissions/cac7bea7-ee68-4eff-8a2c-c3069a0eb6db

import Mathlib



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

theorem ekeland_core {V : Type*} [MetricSpace V] [CompleteSpace V]
    (F : V → EReal) (hF : LowerSemicontinuous F) (hne : ∃ v₀ : V, F v₀ ≠ ⊤)
    (hbdd : ⊥ < ⨅ v, F v) (ε : ℝ) (hε : 0 < ε) (u : V)
    (hu : F u ≤ (⨅ v, F v) + (ε : EReal)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ v : V, F v ≤ F u ∧ dist u v ≤ lam ∧
      ∀ w : V, w ≠ v → F v - ((ε / lam * dist v w : ℝ) : EReal) < F w := by
  have hα : 0 < ε / lam := div_pos hε hlam
  obtain ⟨v₀, hv₀⟩ := hne
  have hi_top : (⨅ v, F v) ≠ ⊤ := ne_top_of_le_ne_top hv₀ (iInf_le _ _)
  have hi_bot : (⨅ v, F v) ≠ ⊥ := hbdd.ne'
  set m := (⨅ v, F v).toReal with hmdef
  have hm : (m : EReal) = ⨅ v, F v := EReal.coe_toReal hi_top hi_bot
  have hFge : ∀ v, (m : EReal) ≤ F v := fun v => hm ▸ iInf_le F v
  have hFbot : ∀ v, F v ≠ ⊥ := by
    intro v h
    have := hFge v
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  rw [← hm, ← EReal.coe_add] at hu
  have hFu_top : F u ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  set fu := (F u).toReal with hfudef
  have hfu : (fu : EReal) = F u := EReal.coe_toReal hFu_top (hFbot u)
  rw [← hfu, EReal.coe_le_coe_iff] at hu
  let S : Set (V × ℝ) := {p | F p.1 ≤ (p.2 : EReal)}
  have hS : IsClosed S := by
    have h1 := hF.isClosed_epigraph
    have hc : Continuous (fun p : V × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h1.preimage hc
  have hmS : ∃ m' : ℝ, ∀ p ∈ S, m' ≤ p.2 :=
    ⟨m, fun p hp => EReal.coe_le_coe_iff.1 ((hFge p.1).trans hp)⟩
  have hp₁ : (u, fu) ∈ S := by
    show F u ≤ (fu : EReal)
    rw [hfu]
  obtain ⟨q, hqS, hpq, hmax⟩ := lemma_1_2_x (ε / lam) hα S hS hmS (u, fu) hp₁
  have hq_top : F q.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hqS
  set fv := (F q.1).toReal with hfvdef
  have hfv : (fv : EReal) = F q.1 := EReal.coe_toReal hq_top (hFbot q.1)
  have hfvq : fv ≤ q.2 := by
    have : F q.1 ≤ (q.2 : EReal) := hqS
    rw [← hfv, EReal.coe_le_coe_iff] at this
    exact this
  have hq2 : q.2 = fv := by
    have := hmax (q.1, fv) (show F q.1 ≤ (fv : EReal) by rw [hfv])
      (by unfold bpLEx; simp; linarith)
    rw [← this]
  have hfvm : m ≤ fv := by
    have := hFge q.1
    rw [← hfv, EReal.coe_le_coe_iff] at this
    exact this
  unfold bpLEx at hpq
  simp only at hpq
  rw [hq2] at hpq
  have hd0 := dist_nonneg (x := u) (y := q.1)
  refine ⟨q.1, ?_, ?_, ?_⟩
  · rw [← hfv, ← hfu, EReal.coe_le_coe_iff]
    nlinarith
  · have h : ε / lam * dist u q.1 ≤ ε := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hlam] at h
    nlinarith
  · intro w hw
    by_cases hwt : F w = ⊤
    · rw [hwt, ← hfv, ← EReal.coe_sub]
      exact EReal.coe_lt_top _
    · set fw := (F w).toReal with hfwdef
      have hfw : (fw : EReal) = F w := EReal.coe_toReal hwt (hFbot w)
      rw [← hfv, ← EReal.coe_sub, ← hfw, EReal.coe_lt_coe_iff]
      by_contra hcon
      push_neg at hcon
      have := hmax (w, fw) (show F w ≤ (fw : EReal) by rw [hfw])
        (by unfold bpLEx; simp only; rw [hq2]; linarith)
      exact hw (congrArg Prod.fst this)

end EkelandVP.General

open EkelandVP.General


theorem solution {V : Type*} [MetricSpace V] [CompleteSpace V]
    (F : V → EReal) (hF : LowerSemicontinuous F) (hne : ∃ v₀ : V, F v₀ ≠ ⊤)
    (hbdd : ⊥ < ⨅ v, F v) (ε : ℝ) (hε : 0 < ε) (u : V)
    (hu : F u ≤ (⨅ v, F v) + (ε : EReal)) (lam : ℝ) (hlam : 0 < lam) :
    ∃ v : V, F v ≤ F u ∧ dist u v ≤ lam ∧
      ∀ w : V, w ≠ v → F v - ((ε / lam * dist v w : ℝ) : EReal) < F w := by
  exact ekeland_core F hF hne hbdd ε hε u hu lam hlam
