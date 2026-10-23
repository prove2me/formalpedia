-- Prove2me | solution 1 for CorrelatedTrials.Consistency.posterior_mean_consistency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:25:03.497367+00:00
-- url     : https://prove2.me/submissions/d3dcfbf7-da0f-4142-90f7-f4a735915d75

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess
import Theorems.Thm_CorrelatedTrials_Consistency_posterior_moments

open MeasureTheory ProbabilityTheory Filter Topology CorrelatedTrials.Consistency

namespace CtMat
open Matrix

variable {M : ℕ}

noncomputable def Step (lam : Fin M → ℝ) (S : Matrix (Fin M) (Fin M) ℝ) (u : Fin M) :
    Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun j k => S j k - S j u * S u k / (lam u + S u u)

noncomputable def bf (S : Matrix (Fin M) (Fin M) ℝ) (x y : Fin M → ℝ) : ℝ := x ⬝ᵥ (S *ᵥ y)

lemma bf_symm {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (x y : Fin M → ℝ) :
    bf S x y = bf S y x := by
  unfold bf
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have : S.transpose = S := by simpa using hS.eq
  rw [this]

lemma bf_nonneg {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x : Fin M → ℝ) : 0 ≤ bf S x x := by
  have := hS.posSemidef.dotProduct_mulVec_nonneg x
  simpa [bf] using this

lemma bf_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (x y : Fin M → ℝ) :
    (bf S x y) ^ 2 ≤ bf S x x * bf S y y := by
  have hq : ∀ t : ℝ, 0 ≤ bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
    intro t
    have h := bf_nonneg hS (x + t • y)
    have e : bf S (x + t • y) (x + t • y) =
        bf S y y * (t * t) + (2 * bf S x y) * t + bf S x x := by
      have hs := bf_symm hS.1 y x
      simp only [bf, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct,
        dotProduct_smul, smul_eq_mul] at hs ⊢
      rw [hs]; ring
    rw [← e]; exact h
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith


lemma bf_single {S : Matrix (Fin M) (Fin M) ℝ} (x : Fin M → ℝ) (u : Fin M) :
    bf S x (Pi.single u 1) = ∑ j, x j * S j u := by
  simp [bf, dotProduct, mulVec, Pi.single_apply]

lemma bf_step {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (lam : Fin M → ℝ) (u : Fin M)
    (x : Fin M → ℝ) :
    bf (Step lam S u) x x = bf S x x - (∑ j, x j * S j u) ^ 2 / (lam u + S u u) := by
  have hsym : ∀ a b, S a b = S b a := fun a b => by
    have := hS.apply b a
    simpa using this
  have h1 : ∀ k, S u k = S k u := fun k => hsym u k
  unfold bf Step
  simp only [dotProduct, mulVec, Matrix.of_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  congr 1
  simp only [h1]
  rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


lemma sym_of {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.IsHermitian) (a b : Fin M) : S a b = S b a := by
  have := hS.apply b a
  simpa using this

lemma step_posDef {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) : (Step lam S u).PosDef := by
  have hsym := sym_of hS.1
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [Step, Matrix.of_apply, star_trivial]
    rw [hsym j i, hsym u j, hsym i u]
    ring
  · intro x hx
    have hpos := hS.dotProduct_mulVec_pos hx
    have hcs := bf_cs hS x (Pi.single u 1)
    rw [bf_single] at hcs
    have hee : bf S (Pi.single u 1) (Pi.single u 1) = S u u := by
      simp [bf, dotProduct, mulVec, Pi.single_apply]
    rw [hee] at hcs
    have hQ : 0 < bf S x x := by simpa [bf] using hpos
    have := bf_step hS.1 lam u x
    simp only [star_trivial]
    show 0 < bf (Step lam S u) x x
    rw [this]
    rw [sub_pos, div_lt_iff₀ hD]
    nlinarith [hcs, hQ, hu, hSuu]

lemma step_diag_le {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) (j : Fin M) : Step lam S u j j ≤ S j j := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  rw [sym_of hS.1 u j, ← sq]
  have : 0 ≤ S j u ^ 2 / (lam u + S u u) := by positivity
  rw [sym_of hS.1 j u] at this ⊢
  linarith [this]

lemma step_diag_self {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (lam : Fin M → ℝ) (u : Fin M)
    (hu : 0 < lam u) :
    1 / Step lam S u u u = 1 / S u u + 1 / lam u := by
  have hSuu : 0 < S u u := hS.diag_pos
  have hD : 0 < lam u + S u u := by linarith
  simp only [Step, Matrix.of_apply]
  have h1 := hu.ne'
  have h2 := hSuu.ne'
  have h3 := hD.ne'
  have e : S u u - S u u * S u u / (lam u + S u u) = S u u * lam u / (lam u + S u u) := by
    field_simp; ring
  rw [e, one_div_div]
  field_simp

lemma step_cs {S : Matrix (Fin M) (Fin M) ℝ} (hS : S.PosDef) (i j : Fin M) :
    (S i j) ^ 2 ≤ S i i * S j j := by
  have := bf_cs hS (Pi.single i 1) (Pi.single j 1)
  simpa [bf, dotProduct, mulVec, Pi.single_apply] using this

end CtMat

namespace CtSeq

variable {M : ℕ} (I : Instance M)

lemma sig_succ (t : ℕ) (ω : TrialSpace M) :
    Sig I (t + 1) ω = CtMat.Step I.lam (Sig I t ω) (alloc I t ω) := by
  simp only [Sig, cpdeState, alloc, update, CtMat.Step]

lemma sig_posDef (t : ℕ) (ω : TrialSpace M) : (Sig I t ω).PosDef := by
  induction t with
  | zero => exact I.posDef
  | succ t ih =>
    rw [sig_succ]
    exact CtMat.step_posDef ih _ _ (I.lam_pos _)

lemma sig_diag_anti (t : ℕ) (ω : TrialSpace M) (j : Fin M) :
    Sig I (t + 1) ω j j ≤ Sig I t ω j j := by
  rw [sig_succ]
  exact CtMat.step_diag_le (sig_posDef I t ω) _ _ (I.lam_pos _) j

lemma sig_diag_le (t : ℕ) (ω : TrialSpace M) (j : Fin M) : Sig I t ω j j ≤ I.Sig0 j j := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (sig_diag_anti I t ω j).trans ih

end CtSeq

namespace PostCons

variable {M : ℕ} (I : Instance M)

noncomputable def obs (T : ℕ) (ω : TrialSpace M) : Fin T → ℝ :=
  fun s => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω

noncomputable def F (T : ℕ) : MeasurableSpace (TrialSpace M) :=
  MeasurableSpace.comap (obs I T) inferInstance

lemma F_le (T : ℕ) : F I T ≤ (inferInstance : MeasurableSpace (TrialSpace M)) :=
  ((posterior_moments I T ⟨0, by have := I.two_le; omega⟩).1).comap_le

lemma F_mono {T T' : ℕ} (h : T ≤ T') : F I T ≤ F I T' := by
  have e : obs I T = (fun y : Fin T' → ℝ => fun s : Fin T => y (Fin.castLE h s)) ∘ obs I T' := by
    funext ω s; rfl
  unfold F
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

noncomputable def filt : Filtration ℕ (inferInstance : MeasurableSpace (TrialSpace M)) where
  seq := F I
  mono' := fun _ _ h => F_mono I h
  le' := F_le I

instance : IsProbabilityMeasure (trialMeasure I) := by
  unfold trialMeasure; infer_instance

lemma theta_integrable (i : Fin M) : Integrable (fun ω => theta ω i) (trialMeasure I) := by
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin M) => x i)
      (multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0) := by
    have := (IsGaussian.integrable_id (μ := multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0))
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp this
  have hfst : (trialMeasure I).map Prod.fst = multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0 := by
    simp [trialMeasure]
  rw [← hfst] at h1
  exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 h1

end PostCons

open PostCons in
theorem solution {M : ℕ} (I : Instance M) (i : Fin M)
    (h : ∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) :
    (∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => mu I T ω i) atTop (𝓝 (theta ω i))) ∧
      (∀ T, MemLp (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I)) ∧
      Tendsto (fun T => eLpNorm (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I))
        atTop (𝓝 0) := by
  set P := trialMeasure I
  have hPM := fun T => posterior_moments I T i
  have hθm : Measurable (fun ω : TrialSpace M => theta ω i) := by unfold theta; fun_prop
  have hθ := theta_integrable I i
  -- measurability of the posterior mean and variance
  have hmu_meas : ∀ T, StronglyMeasurable (fun ω => mu I T ω i) := fun T =>
    (hPM T).2.1.mono (F_le I T)
  have hsig_meas : ∀ T, StronglyMeasurable (fun ω => Sig I T ω i i) := fun T =>
    (hPM T).2.2.1.mono (F_le I T)
  -- square integrability
  have hint : ∀ T, Integrable (fun ω => (theta ω i - mu I T ω i) ^ 2) P := by
    intro T
    by_contra hni
    have h0 := (hPM T).2.2.2.2
    rw [condExp_of_not_integrable hni] at h0
    have hpos : ∀ ω, 0 < Sig I T ω i i := fun ω => (CtSeq.sig_posDef I T ω).diag_pos
    have : ∀ᵐ ω ∂P, False := h0.mono fun ω hω => by
      have := hpos ω; simp only [Pi.zero_apply] at hω; linarith
    have := measure_univ (μ := P)
    rw [ae_iff] at *
    simp_all
  have hmemLp : ∀ T, MemLp (fun ω => mu I T ω i - theta ω i) 2 P := by
    intro T
    refine (memLp_two_iff_integrable_sq ((hmu_meas T).aestronglyMeasurable.sub
      hθm.aestronglyMeasurable)).2 ?_
    refine (hint T).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  -- ∫ (µ^T - θ)^2 = ∫ Σ^T_ii
  have hint_eq : ∀ T, ∫ ω, (mu I T ω i - theta ω i) ^ 2 ∂P = ∫ ω, Sig I T ω i i ∂P := by
    intro T
    have h1 : (fun ω => Sig I T ω i i) =ᵐ[P]
        P[fun ω => (theta ω i - mu I T ω i) ^ 2 | F I T] := (hPM T).2.2.2.2
    rw [integral_congr_ae h1, integral_condExp (F_le I T)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have hsig_lim : Tendsto (fun T => ∫ ω, Sig I T ω i i ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun T ω => Sig I T ω i i) (f := fun _ => (0 : ℝ)) (fun _ => I.Sig0 i i)
      (fun T => (hsig_meas T).aestronglyMeasurable) (integrable_const _)
      (fun T => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (CtSeq.sig_posDef I T ω).diag_pos]
        exact CtSeq.sig_diag_le I T ω i) h
    simpa using this
  have hL2 : Tendsto (fun T => eLpNorm (fun ω => mu I T ω i - theta ω i) 2 P) atTop (𝓝 0) := by
    have e : ∀ T, eLpNorm (fun ω => mu I T ω i - theta ω i) 2 P =
        ENNReal.ofReal ((∫ ω, Sig I T ω i i ∂P) ^ (1 / (2 : ℝ))) := by
      intro T
      rw [(hmemLp T).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ← hint_eq T]
      congr 2
      · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      · simp
    simp_rw [e]
    have : Tendsto (fun T => (∫ ω, Sig I T ω i i ∂P) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := hsig_lim.rpow_const (p := 1 / (2 : ℝ)) (Or.inr (by norm_num))
      simpa [Real.zero_rpow (by norm_num : (1 / (2 : ℝ)) ≠ 0)] using this
    simpa using (ENNReal.tendsto_ofReal this)
  refine ⟨?_, hmemLp, hL2⟩
  -- almost sure convergence: Lévy's upward theorem plus identification of the limit
  have hunif : UniformIntegrable (fun n => P[fun ω => theta ω i | filt I n]) 1 P :=
    hθ.uniformIntegrable_condExp_filtration
  obtain ⟨R, hR⟩ := hunif.2.2
  have hlim := (martingale_condExp (fun ω => theta ω i) (filt I) P).submartingale.ae_tendsto_limitProcess hR
  have hce : ∀ᵐ ω ∂P, ∀ T, mu I T ω i = (P[fun ω => theta ω i | filt I T]) ω :=
    ae_all_iff.2 fun T => (hPM T).2.2.2.1
  have hmeasure : TendstoInMeasure P (fun T ω => mu I T ω i) atTop (fun ω => theta ω i) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun T => (hmu_meas T).aestronglyMeasurable) hθm.aestronglyMeasurable hL2
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hlim, hce, hsub] with ω h1 h2 h3
  have h1' : Tendsto (fun T => mu I T ω i) atTop
      (𝓝 ((filt I).limitProcess (fun n ω => (P[fun ω => theta ω i | filt I n]) ω) P ω)) := by
    refine h1.congr (fun T => ?_)
    exact (h2 T).symm
  have := tendsto_nhds_unique (h1'.comp hns.tendsto_atTop) h3
  rw [this] at h1'
  exact h1'
