-- Prove2me | solution 1 for FarmerInfoProvision.proposition_2_optimal_information_provision
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T04:59:05.25375+00:00
-- url     : https://prove2.me/submissions/7a7c8f96-4df4-49c1-8d6e-4346009c4a3d

import Mathlib
import Definitions.Def_FarmerInfoProvision_GaussianPrimitives
import Definitions.Def_FarmerInfoProvision_IsBNE
import Definitions.Def_FarmerInfoProvision_welfare
import Definitions.Def_FarmerInfoProvision_provisionIndex
import Definitions.Def_FarmerInfoProvision_optimalCount

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision.B6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

lemma int_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P :=
  hf.integrable_mul hg

lemma memLp_Z (M : GaussianPrimitives P n) (k : Shock n) : MemLp (M.Z k) 2 P := by
  have h : MemLp (id : ℝ → ℝ) 2 (P.map (M.Z k)) := by
    rw [M.law k]; simpa using memLp_id_gaussianReal (μ := 0) (v := 1) 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id (M.measurable k).aemeasurable).1 h

lemma memLp_demand (M : GaussianPrimitives P n) (α : ℝ) : MemLp (demandShock M α) 2 P := by
  have := (memLp_Z M Shock.demand).mul_const (Real.sqrt α)⁻¹
  unfold demandShock
  simpa [div_eq_mul_inv] using this

/-- (F1) the quadratic identity for a deviation `q + t d`. -/
lemma quad_identity (b t : ℝ) {R q d : Ω → ℝ} (hR : MemLp R 2 P) (hq : MemLp q 2 P)
    (hd : MemLp d 2 P) :
    ∫ ω, (R ω - b * (q ω + t * d ω)) * (q ω + t * d ω) ∂P - ∫ ω, (R ω - b * q ω) * q ω ∂P
      = t * ∫ ω, (R ω - 2 * b * q ω) * d ω ∂P - b * t ^ 2 * ∫ ω, d ω * d ω ∂P := by
  have hqd : MemLp (fun ω => q ω + t * d ω) 2 P := hq.add (hd.const_mul t)
  have h1 : Integrable (fun ω => (R ω - b * (q ω + t * d ω)) * (q ω + t * d ω)) P :=
    int_mul (hR.sub (hqd.const_mul b)) hqd
  have h2 : Integrable (fun ω => (R ω - b * q ω) * q ω) P := int_mul (hR.sub (hq.const_mul b)) hq
  have h3 : Integrable (fun ω => (R ω - 2 * b * q ω) * d ω) P :=
    int_mul (hR.sub (hq.const_mul (2 * b))) hd
  have h4 : Integrable (fun ω => d ω * d ω) P := int_mul hd hd
  have key : ∫ ω, (R ω - b * (q ω + t * d ω)) * (q ω + t * d ω) ∂P
      - ∫ ω, (R ω - b * q ω) * q ω ∂P
      = ∫ ω, (t * ((R ω - 2 * b * q ω) * d ω) - (b * t ^ 2) * (d ω * d ω)) ∂P := by
    rw [← integral_sub h1 h2]
    congr 1; funext ω; ring
  rw [key, integral_sub (h3.const_mul t) (h4.const_mul _), integral_const_mul, integral_const_mul]

lemma sum_update (σ : Fin n → ℝ × ℝ → ℝ) (i : Fin n) (g : ℝ × ℝ → ℝ) (x : Fin n → ℝ × ℝ) :
    ∑ k, Function.update σ i g k (x k) = ∑ k, σ k (x k) - σ i (x i) + g (x i) := by
  have h : ∀ k, Function.update σ i g k (x k) =
      σ k (x k) + if k = i then g (x i) - σ i (x i) else 0 := by
    intro k
    by_cases hk : k = i
    · rw [hk]; simp
    · simp [hk]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma ep_update (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) (i : Fin n) (g : ℝ × ℝ → ℝ) :
    expectedProfit M a b c α β γ I (Function.update σ i g) i =
      ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
        + demandShock M α ω - c - b * g (obs M α β γ I i ω)) * g (obs M α β γ I i ω) ∂P := by
  unfold expectedProfit
  congr 1; funext ω
  rw [sum_update σ i g (fun k => obs M α β γ I k ω), Function.update_self]
  ring

lemma ep_self (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) (i : Fin n) :
    expectedProfit M a b c α β γ I σ i =
      ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
        + demandShock M α ω - c - b * σ i (obs M α β γ I i ω)) * σ i (obs M α β γ I i ω) ∂P := by
  have := ep_update M a b c α β γ I σ i (σ i)
  rwa [Function.update_eq_self] at this

lemma memLp_resid (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) (hσ : ∀ k, Admissible M α β γ I k (σ k)) (i : Fin n) :
    MemLp (fun ω => a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c
      - b * σ i (obs M α β γ I i ω)) 2 P := by
  have hS : MemLp (fun ω => ∑ k, σ k (obs M α β γ I k ω)) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ => (hσ k).2)
  exact ((((memLp_const a).sub (hS.const_mul b)).add (memLp_demand M α)).sub
    (memLp_const c)).sub ((hσ i).2.const_mul b)

/-- (C2) first-order condition of a Bayesian Nash equilibrium. -/
theorem bne_foc (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (σ : Fin n → ℝ × ℝ → ℝ) (hσ : IsBNE M a b c α β γ I σ) (i : Fin n)
    {d : ℝ × ℝ → ℝ} (hd : Admissible M α β γ I i d) :
    ∫ ω, (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c
      - b * σ i (obs M α β γ I i ω)) * d (obs M α β γ I i ω) ∂P = 0 := by
  have hX : MemLp (fun ω => σ i (obs M α β γ I i ω)) 2 P := (hσ.1 i).2
  have hS : MemLp (fun ω => ∑ k, σ k (obs M α β γ I k ω)) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ => (hσ.1 k).2)
  have hR : MemLp (fun ω => a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
      + demandShock M α ω - c) 2 P :=
    (((memLp_const a).sub ((hS.sub hX).const_mul b)).add (memLp_demand M α)).sub (memLp_const c)
  have hD : MemLp (fun ω => d (obs M α β γ I i ω)) 2 P := hd.2
  set A := ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
      + demandShock M α ω - c - 2 * b * σ i (obs M α β γ I i ω)) * d (obs M α β γ I i ω) ∂P
    with hA
  set B := ∫ ω, d (obs M α β γ I i ω) * d (obs M α β γ I i ω) ∂P with hBdef
  have hB : 0 ≤ B := integral_nonneg fun ω => mul_self_nonneg _
  set t := A / (b * (B + 1)) with ht
  have hadm : Admissible M α β γ I i (fun x => σ i x + t * d x) :=
    ⟨(hσ.1 i).1.add (hd.1.const_mul t), hX.add (hD.const_mul t)⟩
  have hle := hσ.2 i _ hadm
  rw [ep_update, ep_self] at hle
  have hq := quad_identity b t hR hX hD
  have h0 : t * A - b * t ^ 2 * B ≤ 0 := by linarith
  have hpos : 0 < b * (B + 1) ^ 2 := by positivity
  have e : t * A - b * t ^ 2 * B = A ^ 2 / (b * (B + 1) ^ 2) := by
    rw [ht]; field_simp; ring
  have h3 : A ^ 2 ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg (e ▸ h0) hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this
  have hA0 : A = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h3 (sq_nonneg A))
  rw [← hA0, hA]
  congr 1; funext ω; ring

/-- (C3a) two equilibria for the same informed set agree almost surely. -/
theorem bne_ae_eq (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (σ τ : Fin n → ℝ × ℝ → ℝ) (hσ : IsBNE M a b c α β γ I σ)
    (hτ : IsBNE M a b c α β γ I τ) :
    ∀ᵐ ω ∂P, ∀ i, σ i (obs M α β γ I i ω) = τ i (obs M α β γ I i ω) := by
  have hadm : ∀ i, Admissible M α β γ I i (fun x => σ i x - τ i x) :=
    fun i => ⟨(hσ.1 i).1.sub (hτ.1 i).1, (hσ.1 i).2.sub (hτ.1 i).2⟩
  have hDm : ∀ i, MemLp (fun ω => σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)) 2 P :=
    fun i => (hadm i).2
  have hT : MemLp (fun ω => ∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ => hDm k)
  have key : ∀ i, ∫ ω, (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))
      + (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)))
      * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)) ∂P = 0 := by
    intro i
    have h1 := bne_foc M hb I σ hσ i (hadm i)
    have h2 := bne_foc M hb I τ hτ i (hadm i)
    have i1 := int_mul (memLp_resid M a b c α β γ I σ hσ.1 i) (hDm i)
    have i2 := int_mul (memLp_resid M a b c α β γ I τ hτ.1 i) (hDm i)
    have h12 := integral_sub i1 i2
    rw [h1, h2, sub_zero] at h12
    have e : ∀ ω, (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c
        - b * σ i (obs M α β γ I i ω)) * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        - (a - b * ∑ k, τ k (obs M α β γ I k ω) + demandShock M α ω - c
        - b * τ i (obs M α β γ I i ω)) * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        = (-b) * ((∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))
          + (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)))
          * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))) := by
      intro ω; rw [Finset.sum_sub_distrib]; ring
    rw [integral_congr_ae (ae_of_all _ e), integral_const_mul] at h12
    exact (mul_eq_zero.1 h12).resolve_left (neg_ne_zero.2 hb.ne')
  have hint : ∀ i, Integrable (fun ω => (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))
      + (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)))
      * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))) P :=
    fun i => int_mul (hT.add (hDm i)) (hDm i)
  have efun : (fun ω => (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))) ^ 2
      + ∑ i, (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)))
      = fun ω => ∑ i, (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))
      + (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)))
      * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)) := by
    funext ω
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hsum : ∫ ω, ((∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))) ^ 2
      + ∑ i, (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))) ∂P = 0 := by
    rw [efun, integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_eq_zero (fun i _ => key i)
  have hint2 : Integrable (fun ω => (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))) ^ 2
      + ∑ i, (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))) P := by
    rw [efun]; exact integrable_finsetSum _ (fun i _ => hint i)
  have hnn : 0 ≤ (fun ω => (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω))) ^ 2
      + ∑ i, (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
        * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))) :=
    fun ω => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint2).1 hsum
  filter_upwards [hae] with ω hω
  intro i
  simp only [Pi.zero_apply] at hω
  have hs : ∑ i, (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
      * (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω)) = 0 := by
    have := Finset.sum_nonneg (s := Finset.univ) fun i (_ : i ∈ Finset.univ) =>
      mul_self_nonneg (σ i (obs M α β γ I i ω) - τ i (obs M α β γ I i ω))
    nlinarith [sq_nonneg (∑ k, (σ k (obs M α β γ I k ω) - τ k (obs M α β γ I k ω)))]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg _)).1 hs i
    (Finset.mem_univ i)
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

/-- (C3) equilibrium welfare does not depend on the equilibrium. -/
theorem bne_welfare_eq (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (σ τ : Fin n → ℝ × ℝ → ℝ) (hσ : IsBNE M a b c α β γ I σ)
    (hτ : IsBNE M a b c α β γ I τ) :
    welfare M a b c α β γ I σ = welfare M a b c α β γ I τ := by
  have h := bne_ae_eq M hb I σ τ hσ hτ
  unfold welfare expectedProfit
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards [h] with ω hω
  simp only [hω]

lemma integral_Z (M : GaussianPrimitives P n) (k : Shock n) : ∫ ω, M.Z k ω ∂P = 0 := by
  have h1 : ∫ x, id x ∂(P.map (M.Z k)) = ∫ ω, M.Z k ω ∂P :=
    integral_map (M.measurable k).aemeasurable aestronglyMeasurable_id
  rw [M.law k] at h1
  rw [← h1]; simp [integral_id_gaussianReal]

lemma cov_Z (M : GaussianPrimitives P n) (k l : Shock n) :
    cov[M.Z k, M.Z l; P] = if k = l then 1 else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, covariance_self (M.measurable k).aemeasurable,
      ← variance_id_map (M.measurable k).aemeasurable, M.law k, variance_id_gaussianReal]
    simp
  · rw [if_neg hkl]
    exact (M.indep.indepFun hkl).covariance_eq_zero (memLp_Z M k) (memLp_Z M l)

lemma hasGaussianLaw_Z (M : GaussianPrimitives P n) :
    HasGaussianLaw (fun ω k => M.Z k ω) P :=
  iIndepFun.hasGaussianLaw (fun k => ⟨by rw [M.law k]; infer_instance⟩) M.indep

/-- (C1) a linear combination of the shocks that is uncorrelated with two linear observations
is orthogonal to every square integrable function of them. -/
theorem lin_orth (M : GaussianPrimitives P n) (c : Shock n → ℝ) (e : Fin 2 → Shock n → ℝ)
    (hce : ∀ j, ∑ k, c k * e j k = 0) {h : (Fin 2 → ℝ) → ℝ} (hh : Measurable h)
    (hL2 : MemLp (fun ω => h (fun j => ∑ k, e j k * M.Z k ω)) 2 P) :
    ∫ ω, (∑ k, c k * M.Z k ω) * h (fun j => ∑ k, e j k * M.Z k ω) ∂P = 0 := by
  let L : (Shock n → ℝ) →L[ℝ] ((Unit → ℝ) × (Fin 2 → ℝ)) :=
    (ContinuousLinearMap.pi fun _ => ∑ k, c k • ContinuousLinearMap.proj k).prod
      (ContinuousLinearMap.pi fun j => ∑ k, e j k • ContinuousLinearMap.proj k)
  have hpair : HasGaussianLaw (fun ω => (fun (_ : Unit) => ∑ k, c k * M.Z k ω,
      fun j => ∑ k, e j k * M.Z k ω)) P := by
    refine ((hasGaussianLaw_Z M).map_fun L).congr (ae_of_all _ fun ω => ?_)
    refine Prod.ext (funext fun _ => ?_) (funext fun j => ?_) <;> simp [L]
  have hind := hpair.indepFun_of_covariance_eval
    (X := fun (_ : Unit) ω => ∑ k, c k * M.Z k ω) (Y := fun j ω => ∑ k, e j k * M.Z k ω)
    (fun _ j => by
      rw [covariance_fun_sum_fun_sum (fun k => (memLp_Z M k).const_mul (c k))
        (fun l => (memLp_Z M l).const_mul (e j l))]
      simp only [covariance_const_mul_left, covariance_const_mul_right, cov_Z, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hce j]
      exact Finset.sum_congr rfl fun k _ => by ring)
  have hc : IndepFun (fun ω => ∑ k, c k * M.Z k ω) (fun ω => h (fun j => ∑ k, e j k * M.Z k ω)) P :=
    hind.comp (φ := fun v : Unit → ℝ => v ()) (ψ := h)
      (by fun_prop : Measurable fun v : Unit → ℝ => v ()) hh
  have hW : MemLp (fun ω => ∑ k, c k * M.Z k ω) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ => (memLp_Z M k).const_mul (c k))
  have hEW : ∫ ω, ∑ k, c k * M.Z k ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun k _ => ((memLp_Z M k).const_mul (c k)).integrable one_le_two)]
    simp [integral_const_mul, integral_Z]
  rw [hc.integral_fun_mul_eq_mul_integral hW.1 hL2.1, hEW, zero_mul]

/-- (C2') the first-order condition for every farmer implies equilibrium. -/
theorem foc_imp_bne (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (σ : Fin n → ℝ × ℝ → ℝ) (hadm : ∀ i, Admissible M α β γ I i (σ i))
    (hfoc : ∀ i (d : ℝ × ℝ → ℝ), Admissible M α β γ I i d →
      ∫ ω, (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c
        - b * σ i (obs M α β γ I i ω)) * d (obs M α β γ I i ω) ∂P = 0) :
    IsBNE M a b c α β γ I σ := by
  refine ⟨hadm, fun i g hg => ?_⟩
  have hX : MemLp (fun ω => σ i (obs M α β γ I i ω)) 2 P := (hadm i).2
  have hS : MemLp (fun ω => ∑ k, σ k (obs M α β γ I k ω)) 2 P :=
    memLp_finsetSum Finset.univ (fun k _ => (hadm k).2)
  have hR : MemLp (fun ω => a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
      + demandShock M α ω - c) 2 P :=
    (((memLp_const a).sub ((hS.sub hX).const_mul b)).add (memLp_demand M α)).sub (memLp_const c)
  have hdadm : Admissible M α β γ I i (fun x => g x - σ i x) := ⟨hg.1.sub (hadm i).1, hg.2.sub hX⟩
  have hq := quad_identity b 1 hR hX hdadm.2
  have hA := hfoc i _ hdadm
  have hB : 0 ≤ ∫ ω, (g (obs M α β γ I i ω) - σ i (obs M α β γ I i ω))
      * (g (obs M α β γ I i ω) - σ i (obs M α β γ I i ω)) ∂P :=
    integral_nonneg fun ω => mul_self_nonneg _
  rw [ep_update, ep_self]
  have e1 : ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
        + demandShock M α ω - c - b * g (obs M α β γ I i ω)) * g (obs M α β γ I i ω) ∂P
      = ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
        + demandShock M α ω - c - b * (σ i (obs M α β γ I i ω) + 1 * (g (obs M α β γ I i ω)
        - σ i (obs M α β γ I i ω)))) * (σ i (obs M α β γ I i ω) + 1 * (g (obs M α β γ I i ω)
        - σ i (obs M α β γ I i ω))) ∂P := by
    congr 1; funext ω; ring
  have e2 : ∫ ω, (a - b * (∑ k, σ k (obs M α β γ I k ω) - σ i (obs M α β γ I i ω))
        + demandShock M α ω - c - 2 * b * σ i (obs M α β γ I i ω))
        * (g (obs M α β γ I i ω) - σ i (obs M α β γ I i ω)) ∂P
      = ∫ ω, (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c
        - b * σ i (obs M α β γ I i ω)) * (g (obs M α β γ I i ω) - σ i (obs M α β γ I i ω)) ∂P := by
    congr 1; funext ω; ring
  rw [e1]
  nlinarith [mul_nonneg hb.le hB]


/-! ## C4: the linear equilibrium -/

lemma sum_shock (f : Shock n → ℝ) :
    ∑ s, f s = f Shock.demand + f Shock.publicNoise + ∑ i, f (Shock.privateNoise i) := by
  let e : Option (Option (Fin n)) ≃ Shock n :=
    { toFun := fun o => match o with
        | none => Shock.demand
        | some none => Shock.publicNoise
        | some (some i) => Shock.privateNoise i
      invFun := fun s => match s with
        | Shock.demand => none
        | Shock.publicNoise => some none
        | Shock.privateNoise i => some (some i)
      left_inv := fun o => by rcases o with _ | _ | i <;> rfl
      right_inv := fun s => by cases s <;> rfl }
  rw [← e.sum_comp f, Fintype.sum_option, Fintype.sum_option]
  simp only [e, Equiv.coe_fn_mk]
  ring

noncomputable def Df (m n r B : ℝ) : ℝ :=
  (m + 1 + (r * (m + 1) + B) * (m + 1)) * (1 + r * (n - m + 1))
    - (r * (m + 1) + B) * r * m * (n - m)

lemma Df_pos {m n r B : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    0 < Df m n r B := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, 0 ≤ k ∧ n = m + k := ⟨n - m, by linarith, by ring⟩
  have e : Df m (m + k) r B
      = (m + 1) * (1 + r * (k + 1) + (r * (m + 1) + B)) + (r * (m + 1) + B) * r * (m + k + 1) := by
    unfold Df; ring
  rw [e]; positivity

noncomputable def thI (m n r B : ℝ) : ℝ := (m + 1) * (1 + r) / Df m n r B
noncomputable def thJ (m n r B : ℝ) : ℝ := (m + 1 + (r * (m + 1) + B)) / Df m n r B

lemma th_eqs {m n r B : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    thI m n r B * (1 + (m + 1) * r + B) + (n - m) * r * thJ m n r B = 1 ∧
    m * (r + B / (m + 1)) * thI m n r B + (1 + (n - m + 1) * r) * thJ m n r B = 1 := by
  have hD := (Df_pos hm hmn hr hB).ne'
  have hm1 : m + 1 ≠ 0 := by positivity
  unfold thI thJ
  constructor
  · field_simp; unfold Df; ring
  · field_simp; unfold Df; ring

noncomputable def cA0 (n a b c : ℝ) : ℝ := (a - c) / (b * (n + 1))
noncomputable def cA1 (m n α β γ b : ℝ) : ℝ :=
  Real.sqrt γ * thI m n (γ / (2 * α)) (β / α) / (2 * α * b)
noncomputable def cA2 (m n α β γ b : ℝ) : ℝ :=
  β * thI m n (γ / (2 * α)) (β / α) / (α * b * (m + 1))
noncomputable def cB1 (m n α β γ b : ℝ) : ℝ :=
  Real.sqrt γ * thJ m n (γ / (2 * α)) (β / α) / (2 * α * b)

/-- the explicit linear equilibrium profile -/
noncomputable def linProfile (n : ℕ) (a b c α β γ : ℝ) (I : Finset (Fin n)) :
    Fin n → ℝ × ℝ → ℝ :=
  fun k p => cA0 (n : ℝ) a b c
    + (if k ∈ I then cA1 (I.card : ℝ) n α β γ b else cB1 (I.card : ℝ) n α β γ b) * p.1
    + cA2 (I.card : ℝ) n α β γ b * p.2

lemma coef_K {m n α β γ b : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (hb : 0 < b) :
    1 - b * ((m * cA1 m n α β γ b + (n - m) * cB1 m n α β γ b + cA1 m n α β γ b) * Real.sqrt γ
        + (m + 1) * cA2 m n α β γ b) = thI m n (γ / (2 * α)) (β / α) ∧
    1 - b * ((m * cA1 m n α β γ b + (n - m) * cB1 m n α β γ b + cB1 m n α β γ b) * Real.sqrt γ
        + m * cA2 m n α β γ b) = thJ m n (γ / (2 * α)) (β / α) := by
  obtain ⟨g, hg0, rfl⟩ : ∃ g, 0 ≤ g ∧ γ = g ^ 2 := ⟨Real.sqrt γ, Real.sqrt_nonneg _,
    (Real.sq_sqrt hγ).symm⟩
  obtain ⟨e1, e2⟩ := th_eqs (r := g ^ 2 / (2 * α)) (B := β / α) hm hmn (by positivity)
    (by positivity)
  unfold cA1 cA2 cB1
  rw [Real.sqrt_sq hg0]
  set T := thI m n (g ^ 2 / (2 * α)) (β / α)
  set T' := thJ m n (g ^ 2 / (2 * α)) (β / α)
  have hm1 : m + 1 ≠ 0 := by positivity
  constructor
  · have k : b * ((m * (g * T / (2 * α * b)) + (n - m) * (g * T' / (2 * α * b))
        + g * T / (2 * α * b)) * g + (m + 1) * (β * T / (α * b * (m + 1))))
        = (m + 1) * (g ^ 2 / (2 * α)) * T + (n - m) * (g ^ 2 / (2 * α)) * T' + β / α * T := by
      field_simp; ring
    rw [k]; linear_combination (-1 : ℝ) * e1
  · have k : b * ((m * (g * T / (2 * α * b)) + (n - m) * (g * T' / (2 * α * b))
        + g * T' / (2 * α * b)) * g + m * (β * T / (α * b * (m + 1))))
        = m * (g ^ 2 / (2 * α) + β / α / (m + 1)) * T + (n - m + 1) * (g ^ 2 / (2 * α)) * T' := by
      field_simp; ring
    rw [k]; linear_combination (-1 : ℝ) * e2

/-- coefficient vector of the private observation of farmer `i` -/
noncomputable def eP (α γ : ℝ) (i : Fin n) : Shock n → ℝ
  | .demand => Real.sqrt γ / Real.sqrt α
  | .publicNoise => 0
  | .privateNoise k => if k = i then 1 else 0

/-- coefficient vector of the second observation of farmer `i` -/
noncomputable def eY (α β : ℝ) (I : Finset (Fin n)) (i : Fin n) : Shock n → ℝ
  | .demand => if i ∈ I then 1 / Real.sqrt α else 0
  | .publicNoise => if i ∈ I then 1 / Real.sqrt β else 0
  | .privateNoise _ => 0

lemma obs_repr (M : GaussianPrimitives P n) (α β γ : ℝ) (I : Finset (Fin n)) (i : Fin n)
    (ω : Ω) : obs M α β γ I i ω =
      (∑ s, eP α γ i s * M.Z s ω, ∑ s, eY α β I i s * M.Z s ω) := by
  rw [sum_shock, sum_shock]
  simp only [eP, eY, obs, privateObs, publicSignal, demandShock, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  refine Prod.ext ?_ ?_
  · simp only; ring
  · simp only; split_ifs <;> ring

lemma memLp_lin (M : GaussianPrimitives P n) (e : Shock n → ℝ) :
    MemLp (fun ω => ∑ s, e s * M.Z s ω) 2 P :=
  memLp_finsetSum Finset.univ (fun k _ => (memLp_Z M k).const_mul (e k))

lemma memLp_aff (M : GaussianPrimitives P n) (x y z : ℝ) (e e' : Shock n → ℝ) :
    MemLp (fun ω => x + y * (∑ s, e s * M.Z s ω) + z * (∑ s, e' s * M.Z s ω)) 2 P :=
  ((memLp_const x).add ((memLp_lin M e).const_mul y)).add ((memLp_lin M e').const_mul z)

lemma linProfile_adm (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (k : Fin n) : Admissible M α β γ I k (linProfile n a b c α β γ I k) := by
  refine ⟨by unfold linProfile; fun_prop, ?_⟩
  have e : (fun ω => linProfile n a b c α β γ I k (obs M α β γ I k ω)) = fun ω =>
      cA0 (n : ℝ) a b c
      + (if k ∈ I then cA1 (I.card : ℝ) n α β γ b else cB1 (I.card : ℝ) n α β γ b)
        * (∑ s, eP α γ k s * M.Z s ω) + cA2 (I.card : ℝ) n α β γ b * (∑ s, eY α β I k s * M.Z s ω) := by
    funext ω; rw [obs_repr]; rfl
  rw [e]
  exact memLp_aff M _ _ _ _ _

/-- residual coefficients -/
noncomputable def cR (I : Finset (Fin n)) (i : Fin n) (α β γ b A1 A2 B1 : ℝ) : Shock n → ℝ
  | .demand => (1 - b * (((I.card : ℝ) * A1 + ((n : ℝ) - I.card) * B1
      + (if i ∈ I then A1 else B1)) * Real.sqrt γ
      + ((I.card : ℝ) + if i ∈ I then 1 else 0) * A2)) / Real.sqrt α
  | .publicNoise => -(b * ((I.card : ℝ) + if i ∈ I then 1 else 0) * A2) / Real.sqrt β
  | .privateNoise k => -(b * (if k ∈ I then A1 else B1)) - (if k = i then b * (if i ∈ I then A1 else B1) else 0)

lemma sum_C (I : Finset (Fin n)) (A1 B1 : ℝ) :
    ∑ k : Fin n, (if k ∈ I then A1 else B1) = (I.card : ℝ) * A1 + ((n : ℝ) - I.card) * B1 := by
  have h : ∀ k : Fin n, (if k ∈ I then A1 else B1) = B1 + (if k ∈ I then A1 - B1 else 0) := by
    intro k; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma resid_repr (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (i : Fin n) (ω : Ω) :
    a - b * ∑ k, linProfile n a b c α β γ I k (obs M α β γ I k ω) + demandShock M α ω - c
      - b * linProfile n a b c α β γ I i (obs M α β γ I i ω)
    = ∑ s, cR I i α β γ b (cA1 (I.card : ℝ) n α β γ b) (cA2 (I.card : ℝ) n α β γ b)
        (cB1 (I.card : ℝ) n α β γ b) s * M.Z s ω := by
  set A0 := cA0 (n : ℝ) a b c
  set A1 := cA1 (I.card : ℝ) n α β γ b
  set A2 := cA2 (I.card : ℝ) n α β γ b
  set B1 := cB1 (I.card : ℝ) n α β γ b
  set Y := M.Z Shock.demand ω / Real.sqrt α + M.Z Shock.publicNoise ω / Real.sqrt β
  have hA0 : b * ((n : ℝ) + 1) * A0 = a - c := by
    simp only [A0, cA0]; field_simp
  have hq : ∀ k, linProfile n a b c α β γ I k (obs M α β γ I k ω) =
      A0 + (if k ∈ I then A1 else B1) * (Real.sqrt γ * (M.Z Shock.demand ω / Real.sqrt α))
        + (if k ∈ I then A1 else B1) * M.Z (Shock.privateNoise k) ω
        + (if k ∈ I then A2 * Y else 0) := by
    intro k
    simp only [linProfile, obs, privateObs, publicSignal, demandShock, Y]
    split_ifs <;> ring
  have hS : ∑ k, linProfile n a b c α β γ I k (obs M α β γ I k ω) =
      (n : ℝ) * A0 + ((I.card : ℝ) * A1 + ((n : ℝ) - I.card) * B1)
        * (Real.sqrt γ * (M.Z Shock.demand ω / Real.sqrt α))
      + ∑ k, (if k ∈ I then A1 else B1) * M.Z (Shock.privateNoise k) ω + I.card * (A2 * Y) := by
    rw [Finset.sum_congr rfl (fun k _ => hq k), ← sum_C I A1 B1]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
  set SZ := ∑ k : Fin n, (if k ∈ I then A1 else B1) * M.Z (Shock.privateNoise k) ω with hSZ
  have hpriv : ∑ k : Fin n, b * (if k ∈ I then A1 else B1) * M.Z (Shock.privateNoise k) ω
      = b * SZ := by
    rw [hSZ, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hS, hq i, sum_shock]
  simp only [cR, sub_mul, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, demandShock]
  by_cases hi : i ∈ I
  · simp only [hi, if_true, Y]
    rw [hpriv]
    linear_combination (-1 : ℝ) * hA0
  · simp only [hi, if_false, Y]
    rw [hpriv]
    linear_combination (-1 : ℝ) * hA0

lemma cross_zero {n : ℕ} {b α β γ : ℝ} (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (I : Finset (Fin n)) (i : Fin n) :
    (∑ s, cR I i α β γ b (cA1 (I.card : ℝ) n α β γ b) (cA2 (I.card : ℝ) n α β γ b)
        (cB1 (I.card : ℝ) n α β γ b) s * eP α γ i s = 0) ∧
    (∑ s, cR I i α β γ b (cA1 (I.card : ℝ) n α β γ b) (cA2 (I.card : ℝ) n α β γ b)
        (cB1 (I.card : ℝ) n α β γ b) s * eY α β I i s = 0) := by
  have hm : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have hmn : (I.card : ℝ) ≤ n := by
    have := Finset.card_le_univ I; rw [Fintype.card_fin] at this; exact_mod_cast this
  obtain ⟨K1, K2⟩ := coef_K (b := b) hm hmn hα hβ hγ hb
  have ha : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have hbb : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ.le
  have hsa : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hsb : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  have hm1 : (I.card : ℝ) + 1 ≠ 0 := by positivity
  rw [sum_shock, sum_shock]
  simp only [cR, eP, eY, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_const_zero, add_zero]
  by_cases hi : i ∈ I
  · simp only [hi, if_true] at K1 ⊢
    constructor
    · rw [K1]; unfold cA1
      field_simp
      rw [Real.sq_sqrt hα.le]; ring
    · rw [K1]; unfold cA2
      field_simp
      rw [Real.sq_sqrt hα.le, Real.sq_sqrt hβ.le]; ring
  · simp only [hi, if_false, add_zero] at K2 ⊢
    refine ⟨?_, by simp⟩
    rw [K2]; unfold cB1
    field_simp
    rw [Real.sq_sqrt hα.le]; ring

/-- (C4) the linear profile is a Bayesian Nash equilibrium. -/
theorem linear_isBNE (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b) (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (I : Finset (Fin n)) :
    IsBNE M a b c α β γ I (linProfile n a b c α β γ I) := by
  refine foc_imp_bne M hb I _ (linProfile_adm M a b c α β γ I) fun i d hd => ?_
  obtain ⟨hP, hY⟩ := cross_zero (n := n) hb hα hβ hγ I i
  set cc := cR I i α β γ b (cA1 (I.card : ℝ) n α β γ b) (cA2 (I.card : ℝ) n α β γ b)
        (cB1 (I.card : ℝ) n α β γ b)
  let e : Fin 2 → Shock n → ℝ := fun j => if j = 0 then eP α γ i else eY α β I i
  have hce : ∀ j, ∑ k, cc k * e j k = 0 := by
    intro j; fin_cases j
    · simpa [e] using hP
    · simpa [e] using hY
  have hobs : ∀ ω, obs M α β γ I i ω = (fun v : Fin 2 → ℝ => (v 0, v 1))
      (fun j => ∑ k, e j k * M.Z k ω) := by
    intro ω; rw [obs_repr]; simp [e]
  have hh : Measurable fun v : Fin 2 → ℝ => d (v 0, v 1) :=
    hd.1.comp (by fun_prop)
  have hL2 : MemLp (fun ω => d ((fun j => ∑ k, e j k * M.Z k ω) 0,
      (fun j => ∑ k, e j k * M.Z k ω) 1)) 2 P := by
    have := hd.2
    simp only [hobs] at this
    exact this
  have key := lin_orth M cc e hce hh hL2
  rw [← key]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only
  rw [resid_repr M hb I i ω, hobs ω] <;> rfl


/-! ## C5: welfare of the linear equilibrium -/

noncomputable def Nf (m n r B : ℝ) : ℝ :=
  m * (1 + r) ^ 2 * (2 * (r * (m + 1) + B) ^ 2 + r * (m + 1) ^ 2 + 2 * B)
    + (n - m) * (m + 1 + (r * (m + 1) + B)) ^ 2 * r * (2 * r + 1)

/-- at an equilibrium, profit equals `b E[q_i^2]` -/
theorem profit_bne (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b)
    (I : Finset (Fin n)) (σ : Fin n → ℝ × ℝ → ℝ) (hσ : IsBNE M a b c α β γ I σ) (i : Fin n) :
    expectedProfit M a b c α β γ I σ i = b * ∫ ω, (σ i (obs M α β γ I i ω)) ^ 2 ∂P := by
  have h := bne_foc M hb I σ hσ i (hσ.1 i)
  have hR := memLp_resid M a b c α β γ I σ hσ.1 i
  have hX := (hσ.1 i).2
  unfold expectedProfit
  have e : (fun ω => (a - b * ∑ k, σ k (obs M α β γ I k ω) + demandShock M α ω - c)
      * σ i (obs M α β γ I i ω)) = fun ω => (a - b * ∑ k, σ k (obs M α β γ I k ω)
        + demandShock M α ω - c - b * σ i (obs M α β γ I i ω)) * σ i (obs M α β γ I i ω)
        + b * (σ i (obs M α β γ I i ω)) ^ 2 := by
    funext ω; ring
  rw [e, integral_add (int_mul hR hX) (hX.integrable_sq.const_mul b), h, integral_const_mul,
    zero_add]

lemma int_sq_lin (M : GaussianPrimitives P n) (x : ℝ) (w : Shock n → ℝ) :
    ∫ ω, (x + ∑ s, w s * M.Z s ω) ^ 2 ∂P = x ^ 2 + ∑ s, w s ^ 2 := by
  have hW := memLp_lin M w
  have hEW : ∫ ω, ∑ s, w s * M.Z s ω ∂P = 0 := by
    rw [integral_finsetSum _ (fun k _ => ((memLp_Z M k).const_mul (w k)).integrable one_le_two)]
    simp [integral_const_mul, integral_Z]
  have hcov : cov[fun ω => ∑ s, w s * M.Z s ω, fun ω => ∑ s, w s * M.Z s ω; P]
      = ∑ s, w s ^ 2 := by
    rw [covariance_fun_sum_fun_sum (fun k => (memLp_Z M k).const_mul (w k))
      (fun l => (memLp_Z M l).const_mul (w l))]
    simp only [covariance_const_mul_left, covariance_const_mul_right, cov_Z, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hW2 : ∫ ω, (∑ s, w s * M.Z s ω) ^ 2 ∂P = ∑ s, w s ^ 2 := by
    rw [← hcov, covariance, hEW]
    congr 1; funext ω; ring
  have e : (fun ω => (x + ∑ s, w s * M.Z s ω) ^ 2) = fun ω =>
      (x ^ 2 + 2 * x * ∑ s, w s * M.Z s ω) + (∑ s, w s * M.Z s ω) ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => x ^ 2 + 2 * x * ∑ s, w s * M.Z s ω) P :=
    (integrable_const _).add ((hW.integrable one_le_two).const_mul _)
  have i2 : Integrable (fun ω => 2 * x * ∑ s, w s * M.Z s ω) P :=
    (hW.integrable one_le_two).const_mul _
  rw [e, integral_add i1 hW.integrable_sq, integral_add (integrable_const _) i2,
    integral_const, integral_const_mul, hEW, hW2]
  simp

lemma wv_step_a {m n sa sb g b T T' : ℝ} (hm : 0 ≤ m) (hsa : 0 < sa) (hsb : 0 < sb)
    (hb : 0 < b) :
    b * (m * ((g * T / (2 * sa ^ 2 * b) * (g / sa) + sb ^ 2 * T / (sa ^ 2 * b * (m + 1)) * (1 / sa)) ^ 2
        + (sb ^ 2 * T / (sa ^ 2 * b * (m + 1)) * (1 / sb)) ^ 2 + (g * T / (2 * sa ^ 2 * b)) ^ 2)
      + (n - m) * ((g * T' / (2 * sa ^ 2 * b) * (g / sa)) ^ 2 + (g * T' / (2 * sa ^ 2 * b)) ^ 2))
    = (m * T ^ 2 * ((g ^ 2 / (2 * sa ^ 2) + sb ^ 2 / sa ^ 2 / (m + 1)) ^ 2
          + sb ^ 2 / sa ^ 2 / (m + 1) ^ 2 + g ^ 2 / (2 * sa ^ 2) / 2)
        + (n - m) * T' ^ 2 * ((g ^ 2 / (2 * sa ^ 2)) ^ 2 + g ^ 2 / (2 * sa ^ 2) / 2))
      / (sa ^ 2 * b) := by
  have hm1 : m + 1 ≠ 0 := by positivity
  field_simp
  try ring

lemma wv_step_b {m n r B : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    m * thI m n r B ^ 2 * ((r + B / (m + 1)) ^ 2 + B / (m + 1) ^ 2 + r / 2)
      + (n - m) * thJ m n r B ^ 2 * (r ^ 2 + r / 2) = Nf m n r B / (2 * Df m n r B ^ 2) := by
  have hD := (Df_pos hm hmn hr hB).ne'
  have hm1 : m + 1 ≠ 0 := by positivity
  unfold thI thJ Nf
  field_simp
  ring

/-- closed form of the variance part -/
lemma wv_closed {m n α β γ b : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n) (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (hb : 0 < b) :
    b * (m * ((cA1 m n α β γ b * (Real.sqrt γ / Real.sqrt α) + cA2 m n α β γ b * (1 / Real.sqrt α)) ^ 2
        + (cA2 m n α β γ b * (1 / Real.sqrt β)) ^ 2 + cA1 m n α β γ b ^ 2)
      + (n - m) * ((cB1 m n α β γ b * (Real.sqrt γ / Real.sqrt α)) ^ 2 + cB1 m n α β γ b ^ 2))
    = Nf m n (γ / (2 * α)) (β / α) / (2 * α * b * Df m n (γ / (2 * α)) (β / α) ^ 2) := by
  have hb' := wv_step_b (r := γ / (2 * α)) (B := β / α) hm hmn (by positivity) (by positivity)
  obtain ⟨g, hg0, rfl⟩ : ∃ g, 0 ≤ g ∧ γ = g ^ 2 := ⟨Real.sqrt γ, Real.sqrt_nonneg _,
    (Real.sq_sqrt hγ).symm⟩
  obtain ⟨sa, hsa, rfl⟩ : ∃ s, 0 < s ∧ α = s ^ 2 := ⟨Real.sqrt α, Real.sqrt_pos.2 hα,
    (Real.sq_sqrt hα.le).symm⟩
  obtain ⟨sb, hsb, rfl⟩ : ∃ s, 0 < s ∧ β = s ^ 2 := ⟨Real.sqrt β, Real.sqrt_pos.2 hβ,
    (Real.sq_sqrt hβ.le).symm⟩
  unfold cA1 cA2 cB1
  rw [Real.sqrt_sq hg0, Real.sqrt_sq hsa.le, Real.sqrt_sq hsb.le,
    wv_step_a (n := n) hm hsa hsb hb]
  have hD := (Df_pos (r := g ^ 2 / (2 * sa ^ 2)) (B := sb ^ 2 / sa ^ 2) (n := n) hm hmn
    (by positivity) (by positivity)).ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  rw [eq_div_iff (by positivity)] at hb'
  linear_combination (sa ^ 2 * b) * hb'

/-- (C5) welfare of the linear equilibrium. -/
theorem linear_welfare (M : GaussianPrimitives P n) {a b c α β γ : ℝ} (hb : 0 < b) (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (I : Finset (Fin n)) :
    welfare M a b c α β γ I (linProfile n a b c α β γ I)
      = b * n * cA0 (n : ℝ) a b c ^ 2 + Nf (I.card : ℝ) n (γ / (2 * α)) (β / α)
        / (2 * α * b * Df (I.card : ℝ) n (γ / (2 * α)) (β / α) ^ 2) := by
  have hm : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have hmn : (I.card : ℝ) ≤ n := by
    have := Finset.card_le_univ I; rw [Fintype.card_fin] at this; exact_mod_cast this
  have hw := wv_closed (b := b) hm hmn hα hβ hγ hb
  set A0 := cA0 (n : ℝ) a b c
  set A1 := cA1 (I.card : ℝ) n α β γ b
  set A2 := cA2 (I.card : ℝ) n α β γ b
  set B1 := cB1 (I.card : ℝ) n α β γ b
  set VI := (A1 * (Real.sqrt γ / Real.sqrt α) + A2 * (1 / Real.sqrt α)) ^ 2
        + (A2 * (1 / Real.sqrt β)) ^ 2 + A1 ^ 2
  set VJ := (B1 * (Real.sqrt γ / Real.sqrt α)) ^ 2 + B1 ^ 2
  have hq : ∀ i, ∫ ω, (linProfile n a b c α β γ I i (obs M α β γ I i ω)) ^ 2 ∂P
      = A0 ^ 2 + (if i ∈ I then VI else VJ) := by
    intro i
    set w : Shock n → ℝ := fun s => (if i ∈ I then A1 else B1) * eP α γ i s + A2 * eY α β I i s
    have e : (fun ω => (linProfile n a b c α β γ I i (obs M α β γ I i ω)) ^ 2)
        = fun ω => (A0 + ∑ s, w s * M.Z s ω) ^ 2 := by
      funext ω
      rw [obs_repr]
      simp only [linProfile, w, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    rw [e, int_sq_lin, sum_shock]
    have hpr : ∀ k : Fin n, w (Shock.privateNoise k) ^ 2
        = if k = i then (if i ∈ I then A1 else B1) ^ 2 else 0 := by
      intro k; simp only [w, eP, eY]; split_ifs <;> ring
    simp only [hpr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hi : i ∈ I
    · simp only [w, eP, eY, hi, if_true, VI]; ring
    · simp only [w, eP, eY, hi, if_false, VJ]; ring
  unfold welfare
  rw [Finset.sum_congr rfl fun i _ => profit_bne M hb I _ (linear_isBNE M hb hα hβ hγ I) i]
  simp only [hq]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← hw]
  ring


noncomputable def Wf (m n r B : ℝ) : ℝ := Nf m n r B / Df m n r B ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Wf_step {m n r B : ℝ} (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    Wf (m + 1) n r B < Wf m n r B := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ m = 2 + s := ⟨m - 2, by linarith, by ring⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ n = 2 + s + 1 + t := ⟨n - (2 + s) - 1, by linarith, by ring⟩
  have h0 := Df_pos (m := 2 + s) (n := 2 + s + 1 + t) (by linarith) (by linarith) hr hB
  have h1 := Df_pos (m := 2 + s + 1) (n := 2 + s + 1 + t) (by linarith) (by linarith) hr hB
  unfold Wf
  rw [div_lt_div_iff₀ (by positivity) (by positivity), ← sub_pos]
  unfold Nf Df
  ring_nf
  positivity

set_option maxHeartbeats 1000000 in
lemma Wf_two_lt_one {n r B : ℝ} (hn : 4 ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    Wf 2 n r B < Wf 1 n r B := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ n = 4 + t := ⟨n - 4, by linarith, by ring⟩
  have h1 := Df_pos (m := 1) (n := 4 + t) (by norm_num) (by linarith) hr hB
  have h2 := Df_pos (m := 2) (n := 4 + t) (by norm_num) (by linarith) hr hB
  unfold Wf
  rw [div_lt_div_iff₀ (by positivity) (by positivity), ← sub_pos]
  unfold Nf Df
  ring_nf
  positivity

lemma Wf_one_sub_zero (n r B : ℝ) :
    Nf 1 n r B * Df 0 n r B ^ 2 - Nf 0 n r B * Df 1 n r B ^ 2
      = B * (1 + r + B) ^ 2 / 8 * provisionIndex n 1 B (2 * r) := by
  unfold Nf Df provisionIndex; ring

lemma provisionIndex_scale (n : ℝ) {α : ℝ} (hα : α ≠ 0) (β γ : ℝ) :
    provisionIndex n α β γ = α ^ 4 * provisionIndex n 1 (β / α) (2 * (γ / (2 * α))) := by
  unfold provisionIndex; field_simp

lemma Wf_le_two {n r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B) :
    ∀ k : ℕ, (k : ℝ) + 2 ≤ n → Wf ((k : ℝ) + 2) n r B ≤ Wf 2 n r B
  | 0, _ => by simp
  | k + 1, h => by
    have ih := Wf_le_two (n := n) hr hB k (by push_cast at h; linarith)
    have hs := Wf_step (m := (k : ℝ) + 2) (n := n) (by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith) (by push_cast at h; linarith) hr hB
    push_cast
    have e : (k : ℝ) + 1 + 2 = (k : ℝ) + 2 + 1 := by ring
    rw [e]; linarith

lemma Wf_lt_one {n r B : ℝ} (hn : 4 ≤ n) (hr : 0 ≤ r) (hB : 0 < B) (m : ℕ) (hm : 2 ≤ m)
    (hmn : (m : ℝ) ≤ n) : Wf m n r B < Wf 1 n r B := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h := Wf_le_two (n := n) hr hB k (by push_cast at hmn; linarith)
  have h2 := Wf_two_lt_one hn hr hB
  push_cast; linarith

lemma Wf_one_sub_zero_sign {n r B : ℝ} (hn : 1 ≤ n) (hr : 0 ≤ r) (hB : 0 < B) :
    ∃ K > 0, Wf 1 n r B - Wf 0 n r B = K * provisionIndex n 1 B (2 * r) := by
  have h0 := Df_pos (m := 0) (n := n) le_rfl (by linarith) hr hB
  have h1 := Df_pos (m := 1) (n := n) (by norm_num) hn hr hB
  refine ⟨B * (1 + r + B) ^ 2 / 8 / (Df 0 n r B ^ 2 * Df 1 n r B ^ 2), by positivity, ?_⟩
  unfold Wf
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  have e := Wf_one_sub_zero n r B
  have e2 : Nf 1 n r B * Df 0 n r B ^ 2 - Df 1 n r B ^ 2 * Nf 0 n r B
      = B * (1 + r + B) ^ 2 / 8 * provisionIndex n 1 B (2 * r) := by linarith
  rw [e2]; ring

lemma wf_cmp {n : ℕ} (hn : 4 ≤ n) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) (k : ℕ)
    (hk : k ≤ n) :
    Wf (k : ℝ) n (γ / (2 * α)) (β / α)
        ≤ Wf (optimalCount (n : ℝ) α β γ : ℝ) n (γ / (2 * α)) (β / α) ∧
      (k ≠ optimalCount (n : ℝ) α β γ → (2 ≤ k ∨ provisionIndex (n : ℝ) α β γ ≠ 0) →
        Wf (k : ℝ) n (γ / (2 * α)) (β / α)
          < Wf (optimalCount (n : ℝ) α β γ : ℝ) n (γ / (2 * α)) (β / α)) := by
  have hr : 0 ≤ γ / (2 * α) := by positivity
  have hB : 0 < β / α := by positivity
  obtain ⟨K, hK, hd⟩ := Wf_one_sub_zero_sign (n := (n : ℝ))
    (by exact_mod_cast (by omega : 1 ≤ n)) hr hB
  have hsc := provisionIndex_scale (n : ℝ) hα.ne' β γ
  have hα4 : 0 < α ^ 4 := by positivity
  have hlt : ∀ m : ℕ, 2 ≤ m → m ≤ n →
      Wf (m : ℝ) n (γ / (2 * α)) (β / α) < Wf 1 n (γ / (2 * α)) (β / α) :=
    fun m h1 h2 => Wf_lt_one (by exact_mod_cast hn) hr hB m h1 (by exact_mod_cast h2)
  unfold optimalCount
  by_cases hV : 0 < provisionIndex (n : ℝ) α β γ
  · rw [if_pos hV]
    rw [hsc] at hV
    have hV' := pos_of_mul_pos_right hV hα4.le
    have h10 : Wf 0 n (γ / (2 * α)) (β / α) < Wf 1 n (γ / (2 * α)) (β / α) := by
      have := mul_pos hK hV'; linarith
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | h2
    · simp only [Nat.cast_zero, Nat.cast_one]; exact ⟨h10.le, fun _ _ => h10⟩
    · exact ⟨le_rfl, fun h => absurd rfl h⟩
    · simp only [Nat.cast_one]; exact ⟨(hlt k h2 hk).le, fun _ _ => hlt k h2 hk⟩
  · rw [if_neg hV]
    rw [hsc] at hV
    have hV' : provisionIndex (n : ℝ) 1 (β / α) (2 * (γ / (2 * α))) ≤ 0 := by
      by_contra h; exact hV (mul_pos hα4 (lt_of_not_ge h))
    have h10 : Wf 1 n (γ / (2 * α)) (β / α) ≤ Wf 0 n (γ / (2 * α)) (β / α) := by
      have := mul_nonpos_of_nonneg_of_nonpos hK.le hV'; linarith
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | h2
    · exact ⟨le_rfl, fun h => absurd rfl h⟩
    · simp only [Nat.cast_zero, Nat.cast_one]
      refine ⟨h10, fun _ h => ?_⟩
      have hne : provisionIndex (n : ℝ) α β γ ≠ 0 := h.resolve_left (by omega)
      rw [hsc] at hne
      have hlt0 : provisionIndex (n : ℝ) 1 (β / α) (2 * (γ / (2 * α))) < 0 :=
        lt_of_le_of_ne hV' (fun h0 => hne (by rw [h0, mul_zero]))
      have := mul_neg_of_pos_of_neg hK hlt0; linarith
    · simp only [Nat.cast_zero]
      exact ⟨(hlt k h2 hk).le.trans h10, fun _ _ => (hlt k h2 hk).trans_le h10⟩

lemma welfare_term (m n r B x : ℝ) : Nf m n r B / (x * Df m n r B ^ 2) = Wf m n r B / x := by
  unfold Wf; rw [div_div, mul_comm (Df m n r B ^ 2)]

end FarmerInfoProvision.B6

open FarmerInfoProvision MeasureTheory ProbabilityTheory in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 4 ≤ n) (M : GaussianPrimitives P n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∀ I : Finset (Fin n), ∃ σ : Fin n → ℝ × ℝ → ℝ, IsBNE M a b c α β γ I σ) ∧
    ∀ (I I' : Finset (Fin n)) (σ σ' : Fin n → ℝ × ℝ → ℝ),
      IsBNE M a b c α β γ I σ → IsBNE M a b c α β γ I' σ' →
      I'.card = optimalCount (n : ℝ) α β γ →
      welfare M a b c α β γ I σ ≤ welfare M a b c α β γ I' σ' ∧
      (I.card ≠ I'.card → (2 ≤ I.card ∨ provisionIndex (n : ℝ) α β γ ≠ 0) →
        welfare M a b c α β γ I σ < welfare M a b c α β γ I' σ') := by
  refine ⟨fun I => ⟨_, B6.linear_isBNE M hb hα hβ hγ I⟩, ?_⟩
  intro I I' σ σ' hσ hσ' hcard
  rw [B6.bne_welfare_eq M hb I σ _ hσ (B6.linear_isBNE M hb hα hβ hγ I),
    B6.bne_welfare_eq M hb I' σ' _ hσ' (B6.linear_isBNE M hb hα hβ hγ I'),
    B6.linear_welfare M hb hα hβ hγ I, B6.linear_welfare M hb hα hβ hγ I',
    B6.welfare_term, B6.welfare_term]
  have hk : I.card ≤ n := by simpa using Finset.card_le_univ I
  obtain ⟨h1, h2⟩ := B6.wf_cmp hn hα hβ hγ I.card hk
  rw [← hcard] at h1 h2
  have hpos : 0 < 2 * α * b := by positivity
  constructor
  · have := div_le_div_of_nonneg_right h1 hpos.le; linarith
  · intro hne hcond
    have := div_lt_div_of_pos_right (h2 hne hcond) hpos; linarith
