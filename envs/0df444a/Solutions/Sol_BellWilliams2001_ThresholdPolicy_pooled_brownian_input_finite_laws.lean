-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.pooled_brownian_input_finite_laws
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:08:14.359527+00:00
-- url     : https://prove2.me/submissions/2572daaa-48de-413b-a1b7-9028a96ddb05

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_normalized_finite_brownian_sum
import Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling
open scoped ENNReal NNReal

private theorem compare_weighted_laws {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {k q : ℕ} (C : Fin k → ℝ≥0 → Ω → ℝ) (hC : ∀ i, IsBrownianReal (C i) P)
    (hCm : ∀ i, AEMeasurable (fun ω t => C i t ω) P)
    (hCI : iIndepFun (fun i ω t => C i t ω) P)
    (B : Fin 2 → ℝ≥0 → Ω' → ℝ) (hB : IsBrownianPair P' B)
    (d : Fin k → ℝ) (a b : ℝ) (he : (∑ i, d i^2) = a^2+b^2) (τ : Fin q → ℝ≥0) :
    IdentDistrib (fun ω j => ∑ i, d i*C i (τ j) ω)
      (fun ω j => a*B 0 (τ j) ω+b*B 1 (τ j) ω) P P' := by
  let v := ∑ i, d i^2
  have hv : 0 ≤ v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rcases hv.eq_or_lt with hzero | hpos
  · have hd (i : Fin k) : d i = 0 := by
      have hi := Finset.single_le_sum (f := fun j => d j^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      change d i^2 ≤ v at hi
      nlinarith only [hi,hzero]
    have hc : a^2+b^2 = 0 := he.symm.trans hzero.symm
    have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp only [hd,ha,hb,zero_mul,add_zero,Finset.sum_const_zero]
    exact ⟨aemeasurable_const,aemeasurable_const,by simp [Measure.map_const]⟩
  let s := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  let D (t : ℝ≥0) (ω : Ω) := (∑ i, d i*C i t ω)/s
  let E (t : ℝ≥0) (ω : Ω') := a/s*B 0 t ω+b/s*B 1 t ω
  have hD : IsBrownianReal D P := normalized_finite_brownian_sum C hC hCm hCI d Finset.univ hpos
  have hWeights : (a/s)^2+(b/s)^2=1 := by
    simp only [div_pow,←add_div,s,Real.sq_sqrt hv,←he]
    exact div_self hpos.ne'
  have hE : IsBrownianReal E P' := independent_brownian_normalized_linear_combination
    (B 0) (B 1) (hB.brownian 0) (hB.brownian 1) hB.indep _ _ hWeights
  have h := brownian_weighted_finite_observation_law hD.toIsPreBrownianReal hE.toIsPreBrownianReal
    τ (fun _ => s)
  have h₁ (ω : Ω) : (fun j => s*D (τ j) ω) = fun j => ∑ i, d i*C i (τ j) ω := by
    funext j
    dsimp [D]
    field_simp [hs.ne']
  have h₂ (ω : Ω') : (fun j => s*E (τ j) ω) =
      fun j => a*B 0 (τ j) ω+b*B 1 (τ j) ω := by
    funext j
    dsimp [E]
    field_simp [hs.ne']
    <;> ring
  exact (IdentDistrib.of_ae_eq h.aemeasurable_fst (ae_of_all _ h₁)).symm.trans
    (h.trans (.of_ae_eq h.aemeasurable_snd (ae_of_all _ h₂)))

set_option maxHeartbeats 3300000 in
theorem solution {Ω Ω₁ Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M : SystemSequence Ω) (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (C : Fin 5 → ℝ≥0 → Ω₁ → ℝ) (hC : ∀ i, IsBrownianReal (C i) P₁)
    (hCm : ∀ i t, Measurable (C i t)) (hCI : iIndepFun (fun i ω t => C i t ω) P₁)
    (P₂ : Measure Ω₂) (B : Fin 2 → ℝ≥0 → Ω₂ → ℝ) (hB : IsBrownianPair P₂ B)
    (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    let ρ : Fin 5 → ℝ := ![1,1,1,(M.lam 0-M.mu 0)/M.mu 1,M.lam 1/M.mu 2]
    let y := M.yvec 1
    let a : Fin 5 → ℝ := ![1,y,-1,-1,-y]
    let C₀ := Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
      (fun j => Real.sqrt (M.mu j*M.betaSq j))
    IdentDistrib (fun ω j => ![(∑ i, a i*C₀ i*C i (ρ i*τ j).toNNReal ω) +
      (M.theta 0+y*M.theta 1)*τ j])
      (fun ω j => ![∑ i,M.yvec i*M.Xtilde B ω (τ j) i]) P₁ P₂ := by
  intro ρ y a C₀
  letI : IsProbabilityMeasure P₂ := hB.isProb
  let ρpos (i : Fin 5) := (ρ i).toNNReal
  have hr₀ : 0 < (M.lam 0-M.mu 0)/M.mu 1 := div_pos (sub_pos.2 M.a31_i) (M.mu_pos 1)
  have hr₁ : 0 < M.lam 1/M.mu 2 := div_pos (M.lam_pos 1) (M.mu_pos 2)
  have hp (i : Fin 5) : 0 < ρ i := by
    fin_cases i <;> simp [ρ,hr₀,hr₁]
  have hρ (i : Fin 5) : (ρpos i:ℝ) = ρ i := Real.coe_toNNReal _ (hp i).le
  have hρne (i : Fin 5) : ρpos i ≠ 0 := by
    intro h
    have he := hρ i
    rw [h,NNReal.coe_zero] at he
    exact (hp i).ne' he.symm
  let D (i : Fin 5) (t : ℝ≥0) (ω : Ω₁) := (Real.sqrt (ρpos i:ℝ))⁻¹ * C i (ρpos i*t) ω
  have hD (i : Fin 5) : IsBrownianReal (D i) P₁ := (hC i).smul (hρne i)
  have hDm (i : Fin 5) : AEMeasurable (fun ω t => D i t ω) P₁ :=
    (measurable_pi_lambda _ fun t => (hCm i (ρpos i*t)).const_mul _).aemeasurable
  have hDI : iIndepFun (fun i ω t => D i t ω) P₁ := hCI.comp
    (fun i (f : ℝ≥0 → ℝ) t => (Real.sqrt (ρpos i:ℝ))⁻¹ * f (ρpos i*t))
    (fun i => measurable_pi_lambda _ fun t =>
      (show Measurable (fun f : ℝ≥0 → ℝ => f (ρpos i*t)) from measurable_pi_apply _).const_mul _)
  let w (i : Fin 5) := a i*C₀ i*Real.sqrt (ρpos i:ℝ)
  let b₀ := Real.sqrt (M.sigmaSq 0)
  let b₁ := y*Real.sqrt (M.sigmaSq 1)
  have hu (k : Fin 2) : 0 ≤ M.alphaSq k := variance_nonneg _ _
  have hv (k : Fin 3) : 0 ≤ M.betaSq k := variance_nonneg _ _
  have hσ (k : Fin 2) : 0 ≤ M.sigmaSq k := by
    by_cases hk : k = 0
    · subst k
      simp only [SystemSequence.sigmaSq,if_true]
      have h₁ := mul_nonneg (M.lam_pos 0).le (hu 0)
      have h₂ := mul_nonneg (M.mu_pos 0).le (hv 0)
      have h₃ := mul_nonneg (hv 1) (sub_nonneg.2 M.a31_i.le)
      linarith
    · simpa only [SystemSequence.sigmaSq,if_neg hk] using
        mul_nonneg (M.lam_pos 1).le (add_nonneg (hu 1) (hv 2))
  have hQ (i : Fin 5) : (C₀ i)^2 =
      (Fin.append (fun k => M.lam k*M.alphaSq k) (fun j => M.mu j*M.betaSq j)) i := by
    obtain ⟨j,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases j with j | j
    · simp only [C₀,finSumFinEquiv_apply_left,Fin.append_left]
      exact Real.sq_sqrt (mul_nonneg (M.lam_pos j).le (hu j))
    · simp only [C₀,finSumFinEquiv_apply_right,Fin.append_right]
      exact Real.sq_sqrt (mul_nonneg (M.mu_pos j).le (hv j))
  have hW (i : Fin 5) : w i^2 = (a i)^2 *
      (Fin.append (fun k => M.lam k*M.alphaSq k) (fun j => M.mu j*M.betaSq j)) i * ρ i := by
    simp only [w,mul_pow,hQ,Real.sq_sqrt (ρpos i).2]
    rw [hρ, Real.sq_sqrt (hp i).le]
  have he : (∑ i, w i^2) = b₀^2+b₁^2 := by
    simp only [hW,b₀,b₁,mul_pow]
    rw [Real.sq_sqrt (hσ 0),Real.sq_sqrt (hσ 1)]
    simp only [SystemSequence.sigmaSq,if_true,show (1:Fin 2) ≠ 0 by decide,if_false]
    rw [Fin.sum_univ_add (a := 2) (b := 3),Fin.sum_univ_two,Fin.sum_univ_three]
    simp only [Fin.append_left,Fin.append_right]
    change (1^2*(M.lam 0*M.alphaSq 0)*1 + y^2*(M.lam 1*M.alphaSq 1)*1) +
      ((-1)^2*(M.mu 0*M.betaSq 0)*1 + (-1)^2*(M.mu 1*M.betaSq 1)*((M.lam 0-M.mu 0)/M.mu 1) +
      (-y)^2*(M.mu 2*M.betaSq 2)*(M.lam 1/M.mu 2)) =
      M.lam 0*M.alphaSq 0+M.mu 0*M.betaSq 0+M.betaSq 1*(M.lam 0-M.mu 0)+
        y^2*(M.lam 1*(M.alphaSq 1+M.betaSq 2))
    field_simp [(M.mu_pos 1).ne',(M.mu_pos 2).ne']
    <;> ring
  have hComp := compare_weighted_laws D hD hDm hDI B hB w b₀ b₁ he (fun j => (τ j).toNNReal)
  let F (f : Fin q → ℝ) (j : Fin q) : Fin 1 → ℝ := ![f j+(M.theta 0+y*M.theta 1)*τ j]
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro j
    apply measurable_pi_lambda
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact (measurable_pi_apply j).add_const _
  have h := hComp.comp hF
  have h₁ (ω : Ω₁) :
      (F fun j => ∑ i, w i*D i (τ j).toNNReal ω) =
       fun j => ![(∑ i, a i*C₀ i*C i (ρ i*τ j).toNNReal ω) + (M.theta 0+y*M.theta 1)*τ j] := by
    funext j
    have hh (i : Fin 5) : w i*D i (τ j).toNNReal ω = a i*C₀ i*C i (ρ i*τ j).toNNReal ω := by
      have htime : ρpos i*(τ j).toNNReal = (ρ i*τ j).toNNReal := by
        exact (Real.toNNReal_mul (hp i).le).symm
      dsimp [w,D]
      rw [htime]
      have hn := (Real.sqrt_pos.2 (show 0 < (ρpos i:ℝ) from by rw [hρ]; exact hp i)).ne'
      field_simp [hn]
    simp only [F,hh]
  have h₂ (ω : Ω₂) :
      (F fun j => b₀*B 0 (τ j).toNNReal ω+b₁*B 1 (τ j).toNNReal ω) =
        fun j => ![∑ i,M.yvec i*M.Xtilde B ω (τ j) i] := by
    funext j i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [F,Matrix.cons_val_zero,Fin.sum_univ_two,SystemSequence.Xtilde,
      show M.yvec 0 = 1 from rfl,b₀,b₁,y,one_mul]
    ring
  exact (IdentDistrib.of_ae_eq h.aemeasurable_fst (ae_of_all _ h₁)).symm.trans
    (h.trans (.of_ae_eq h.aemeasurable_snd (ae_of_all _ h₂)))
