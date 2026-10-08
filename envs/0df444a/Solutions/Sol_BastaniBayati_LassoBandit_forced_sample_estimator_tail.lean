-- Prove2me | solution 1 for BastaniBayati.LassoBandit.forced_sample_estimator_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T19:10:16.050259+00:00
-- url     : https://prove2.me/submissions/01841f69-dd8b-45be-951b-8ecce10e4a05

/- Written by Codex.
Weighted-MGF helpers adapted from Nickrobbins95's accepted UCB(delta)
submission 85177580-d961-4a1a-9320-e4e2db2e23e0.
Matrix helpers credited to Nickrobbins95's accepted OFUL submission
028e111f-382d-40d0-8008-127228d5e6cf.
Scalar exponential inequalities adapted from mrfancypants' accepted
Freedman submission 34d450b7-57ec-4923-81fa-627230f83e2a. -/
import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Algorithm
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Constants
import Definitions.Def_BastaniBayati_LassoBandit_Model


/- Weighted-MGF measure comparison adapted from Nickrobbins95, accepted UCB(delta) submission 85177580-d961-4a1a-9320-e4e2db2e23e0. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BastaniBayati.LassoBandit
lemma lb_weighted_mgf {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X)
    (lam c : ℝ) (hint : Integrable (fun ω => Real.exp (lam * X ω)) P)
    (hlecond : P[fun ω => Real.exp (lam * X ω) | m] ≤ᵐ[P] fun _ => c) {W : Ω → ℝ≥0∞} (hW : Measurable[m] W) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * X ω)) ∂P
      ≤ ENNReal.ofReal (c) * ∫⁻ ω, W ω ∂P := by
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (lam * X ω)) with hfdef
  have hf : Measurable f := by
    rw [hfdef]; exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul lam))
  have hle : (P.withDensity f).trim hm
      ≤ (ENNReal.ofReal (c) • P).trim hm := by
    rw [Measure.le_iff]
    intro s hs
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply f (hm s hs),
      Measure.smul_apply, smul_eq_mul]
    rw [hfdef, ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
    rw [← setIntegral_condExp hm hint hs]
    have h1 : ∫ ω in s, (P[fun ω => Real.exp (lam * X ω) | m]) ω ∂P
        ≤ ∫ ω in s, c ∂P := by
      apply setIntegral_mono_ae integrable_condExp.integrableOn (integrableOn_const)
      filter_upwards [hlecond] with ω hω
      simpa using hω
    rw [setIntegral_const, smul_eq_mul] at h1
    calc ENNReal.ofReal (∫ ω in s, (P[fun ω => Real.exp (lam * X ω) | m]) ω ∂P)
        ≤ ENNReal.ofReal (P.real s * c) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (c) * P s := by
        rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top P s), mul_comm]
  calc ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * X ω)) ∂P
      = ∫⁻ ω, W ω ∂(P.withDensity f) := by
        rw [lintegral_withDensity_eq_lintegral_mul P hf (hW.mono hm le_rfl)]
        congr 1; ext ω; simp [hfdef, mul_comm]
    _ = ∫⁻ ω, W ω ∂((P.withDensity f).trim hm) := (lintegral_trim hm hW).symm
    _ ≤ ∫⁻ ω, W ω ∂((ENNReal.ofReal (c) • P).trim hm) :=
        lintegral_mono' hle le_rfl
    _ = ∫⁻ ω, W ω ∂(ENNReal.ofReal (c) • P) := lintegral_trim hm hW
    _ = ENNReal.ofReal (c) * ∫⁻ ω, W ω ∂P := by
        rw [lintegral_smul_measure, smul_eq_mul]


end BastaniBayati.LassoBandit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace BastaniBayati.LassoBandit

lemma lb_exp_chord (s c x e : ℝ) (hc : 0 < c) (hx : |x| ≤ c) :
    Real.exp (s*x*e) ≤ ((c+x)/(2*c))*Real.exp (s*c*e)
      + ((c-x)/(2*c))*Real.exp (-s*c*e) := by
  have hα : 0 ≤ (c+x)/(2*c) := by rw [abs_le] at hx;apply div_nonneg (by linarith) (by positivity)
  have hβ : 0 ≤ (c-x)/(2*c) := by rw [abs_le] at hx;apply div_nonneg (by linarith) (by positivity)
  have hab : (c+x)/(2*c)+(c-x)/(2*c)=1 := by field_simp;ring
  have he : ((c+x)/(2*c))*(s*c*e)+((c-x)/(2*c))*(-s*c*e)=s*x*e := by field_simp;ring
  have h := convexOn_exp.2 (Set.mem_univ (s*c*e)) (Set.mem_univ (-s*c*e)) hα hβ hab
  simpa only [smul_eq_mul,he] using h

lemma lb_predictable_mgf {Ω : Type*} {m mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (X E : Ω → ℝ)
    (hX : Measurable[m] X) (hE : Measurable E) (σ c : ℝ) (hc : 0 < c)
    (hbound : ∀ ω, |X ω| ≤ c)
    (hint : ∀ s : ℝ,Integrable (fun ω => Real.exp (s*E ω)) P)
    (hsg : ∀ s : ℝ,P[fun ω => Real.exp (s*E ω) | m] ≤ᵐ[P] fun _ => Real.exp (σ^2*s^2/2))
    (s : ℝ) :
    Integrable (fun ω => Real.exp (s*(X ω*E ω))) P ∧
      P[fun ω => Real.exp (s*(X ω*E ω)) | m] ≤ᵐ[P] fun _ => Real.exp (σ^2*(s*c)^2/2) := by
  let A : Ω → ℝ := fun ω => (c+X ω)/(2*c)
  let B : Ω → ℝ := fun ω => (c-X ω)/(2*c)
  let F : Ω → ℝ := fun ω => Real.exp ((s*c)*E ω)
  let G : Ω → ℝ := fun ω => Real.exp ((-s*c)*E ω)
  have hA : Measurable[m] A := (measurable_const.add hX).div_const _
  have hB : Measurable[m] B := (measurable_const.sub hX).div_const _
  have hAB : ∀ ω,0 ≤ A ω ∧ 0 ≤ B ω ∧ A ω+B ω=1 := by
    intro ω
    have hx := hbound ω
    rw [abs_le] at hx
    dsimp [A,B]
    refine ⟨div_nonneg (by linarith) (by positivity),div_nonneg (by linarith) (by positivity),?_⟩
    field_simp;ring
  have hAF : Integrable (A*F) P := (hint (s*c)).bdd_mul (c := 1) (hA.mono hm le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hAB ω).1];linarith [(hAB ω).2.1,(hAB ω).2.2])
  have hBG : Integrable (B*G) P := (hint (-s*c)).bdd_mul (c := 1) (hB.mono hm le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hAB ω).2.1];linarith [(hAB ω).1,(hAB ω).2.2])
  have hf : Measurable (fun ω => Real.exp (s*(X ω*E ω))) :=
    ((hX.mono hm le_rfl).mul hE).const_mul s |>.exp
  have hchord : ∀ ω,Real.exp (s*(X ω*E ω)) ≤ (A*F+B*G) ω := by
    intro ω
    simpa only [A,B,F,G,Pi.add_apply,Pi.mul_apply,mul_assoc] using lb_exp_chord s c (X ω) (E ω) hc (hbound ω)
  have hi : Integrable (fun ω => Real.exp (s*(X ω*E ω))) P := (hAF.add hBG).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)];exact hchord ω)
  have hmono := condExp_mono (m := m) hi (hAF.add hBG) (Filter.Eventually.of_forall hchord)
  have hadd := condExp_add hAF hBG m
  have hpullA := condExp_mul_of_stronglyMeasurable_left hA.stronglyMeasurable hAF (hint (s*c))
  have hpullB := condExp_mul_of_stronglyMeasurable_left hB.stronglyMeasurable hBG (hint (-s*c))
  refine ⟨hi,?_⟩
  filter_upwards [hmono,hadd,hpullA,hpullB,hsg (s*c),hsg (-s*c)] with ω h0 h1 h2 h3 h4 h5
  change P[fun ω => Real.exp (s*(X ω*E ω)) | m] ω ≤ Real.exp (σ^2*(s*c)^2/2)
  change P[A*F+B*G | m] ω = P[A*F | m] ω+P[B*G | m] ω at h1
  change P[A*F | m] ω = A ω*P[F | m] ω at h2
  change P[B*G | m] ω = B ω*P[G | m] ω at h3
  have heq : σ^2*(-s*c)^2/2=σ^2*(s*c)^2/2 := by ring
  rw [heq] at h5
  calc _ ≤ P[A*F+B*G | m] ω := h0
    _ = A ω*P[F | m] ω+B ω*P[G | m] ω := by rw [h1,h2,h3]
    _ ≤ A ω*Real.exp (σ^2*(s*c)^2/2)+B ω*Real.exp (σ^2*(s*c)^2/2) :=
      add_le_add (mul_le_mul_of_nonneg_left h4 (hAB ω).1) (mul_le_mul_of_nonneg_left h5 (hAB ω).2.1)
    _ = _ := by rw [←add_mul,(hAB ω).2.2,one_mul]

end BastaniBayati.LassoBandit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BastaniBayati.LassoBandit

noncomputable def lbNoiseSum {Ω : Type*} (X E : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range k,X t ω*E t ω

lemma lb_noise_meas {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ)
    (X E : ℕ → Ω → ℝ) (n k : ℕ) (hk : k ≤ n)
    (hX : ∀ t < n,Measurable[ℱ t] (X t))
    (hE : ∀ t < n,Measurable[ℱ (t+1)] (E t)) : Measurable[ℱ k] (lbNoiseSum X E k) := by
  unfold lbNoiseSum
  apply Finset.measurable_sum
  intro t ht
  have htk := Finset.mem_range.mp ht
  exact ((hX t (by omega)).mono (ℱ.mono (by omega)) le_rfl).mul
    ((hE t (by omega)).mono (ℱ.mono (by omega)) le_rfl)

lemma lb_noise_mgf {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X E : ℕ → Ω → ℝ)
    (n : ℕ) (σ c : ℝ) (hc : 0 < c)
    (hX : ∀ t < n,Measurable[ℱ t] (X t))
    (hE : ∀ t < n,Measurable[ℱ (t+1)] (E t))
    (hb : ∀ t < n,∀ ω,|X t ω| ≤ c)
    (hint : ∀ t < n,∀ s : ℝ,Integrable (fun ω => Real.exp (s*E t ω)) P)
    (hsg : ∀ t < n,∀ s : ℝ,P[fun ω => Real.exp (s*E t ω) | ℱ t] ≤ᵐ[P]
      fun _ => Real.exp (σ^2*s^2/2)) (s : ℝ) :
    ∫⁻ ω,ENNReal.ofReal (Real.exp (s*lbNoiseSum X E n ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (σ^2*(s*c)^2*n/2)) := by
  have main : ∀ k,k ≤ n → ∫⁻ ω,ENNReal.ofReal (Real.exp (s*lbNoiseSum X E k ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (σ^2*(s*c)^2*k/2)) := by
    intro k
    induction k with
    | zero => intro hk;simp [lbNoiseSum]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hpred := lb_predictable_mgf P (ℱ.le k) (X k) (E k) (hX k hkn)
        ((hE k hkn).mono (ℱ.le _) le_rfl) σ c hc (hb k hkn) (hint k hkn) (hsg k hkn) s
      have hW : Measurable[ℱ k] (fun ω => ENNReal.ofReal (Real.exp (s*lbNoiseSum X E k ω))) :=
        ENNReal.measurable_ofReal.comp (((lb_noise_meas ℱ X E n k (by omega) hX hE).const_mul s).exp)
      have hstep := lb_weighted_mgf (ℱ.le k) (show Measurable (fun ω => X k ω*E k ω) from
        ((hX k hkn).mono (ℱ.le _) le_rfl).mul ((hE k hkn).mono (ℱ.le _) le_rfl))
        s (Real.exp (σ^2*(s*c)^2/2)) hpred.1 hpred.2 hW
      have he : (fun ω => ENNReal.ofReal (Real.exp (s*lbNoiseSum X E (k+1) ω))) =
          fun ω => ENNReal.ofReal (Real.exp (s*lbNoiseSum X E k ω))*
            ENNReal.ofReal (Real.exp (s*(X k ω*E k ω))) := by
        funext ω
        rw [lbNoiseSum,Finset.sum_range_succ]
        change ENNReal.ofReal (Real.exp (s*(lbNoiseSum X E k ω+X k ω*E k ω))) = _
        rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [he]
      calc _ ≤ _ := hstep
        _ ≤ ENNReal.ofReal (Real.exp (σ^2*(s*c)^2/2))*
            ENNReal.ofReal (Real.exp (σ^2*(s*c)^2*k/2)) :=
          mul_le_mul' le_rfl (ih (by omega))
        _ = _ := by
          rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]
          congr 2
          push_cast
          ring
  exact main n le_rfl

lemma lb_mgf_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (hS : Measurable S) (v r : ℝ) (hv : 0 < v) (hr : 0 < r)
    (hmgf : ∀ s : ℝ,∫⁻ ω,ENNReal.ofReal (Real.exp (s*S ω)) ∂P ≤ ENNReal.ofReal (Real.exp (v*s^2/2))) :
    P {ω | r < |S ω|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/(2*v))) := by
  have one_side : ∀ (T : Ω → ℝ),Measurable T →
      (∀ s : ℝ,∫⁻ ω,ENNReal.ofReal (Real.exp (s*T ω)) ∂P ≤ ENNReal.ofReal (Real.exp (v*s^2/2))) →
      P {ω | r < T ω} ≤ ENNReal.ofReal (Real.exp (-r^2/(2*v))) := by
    intro T hT hM
    let s := r/v
    have hs : 0 < s := by dsimp [s];positivity
    have hE : Measurable (fun ω => ENNReal.ofReal (Real.exp (s*T ω))) := ENNReal.measurable_ofReal.comp (hT.const_mul s).exp
    have hsub : {ω | r < T ω} ⊆ {ω | ENNReal.ofReal (Real.exp (s*r)) ≤ ENNReal.ofReal (Real.exp (s*T ω))} := by
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.le hs.le))
    have he0 : ENNReal.ofReal (Real.exp (s*r)) ≠ 0 := by positivity
    have he1 : ENNReal.ofReal (Real.exp (s*r)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmark := meas_ge_le_lintegral_div (μ := P) hE.aemeasurable he0 he1
    calc P {ω | r < T ω} ≤ _ := measure_mono hsub
      _ ≤ _ := hmark
      _ ≤ ENNReal.ofReal (Real.exp (v*s^2/2))/ENNReal.ofReal (Real.exp (s*r)) :=
        by rw [div_eq_mul_inv,div_eq_mul_inv];exact mul_le_mul' (hM s) le_rfl
      _ = ENNReal.ofReal (Real.exp (-r^2/(2*v))) := by
        rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
        congr 2
        dsimp [s]
        field_simp
        ring
  have hp := one_side S hS hmgf
  have hn := one_side (fun ω => -S ω) hS.neg (by
    intro s
    simpa only [mul_neg,←neg_mul,neg_sq] using hmgf (-s))
  have hsub : {ω | r < |S ω|} ⊆ {ω | r < S ω} ∪ {ω | r < -S ω} := by
    intro ω hω
    change r < |S ω| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-r^2/(2*v)))+ENNReal.ofReal (Real.exp (-r^2/(2*v))) := add_le_add hp hn
    _ = _ := by rw [←ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le];congr 1;ring

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_constant_coeff_noise_mgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ι → Ω → ℝ)
    (σ : ℝ≥0) (c : ℝ) (hc : 0 ≤ c) (hiid : iIndepFun E P)
    (hsg : ∀ i,HasSubgaussianMGF (E i) (σ^2) P) (x : ι → ℝ)
    (hb : ∀ i,|x i| ≤ c) (s : ℝ) :
    ∫⁻ ω,ENNReal.ofReal (Real.exp (s*(∑ i,x i*E i ω))) ∂P ≤
      ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)*(σ : ℝ)^2*c^2*s^2/2)) := by
  classical
  have hind := hiid.comp (fun i z => x i*z) (fun i => measurable_id.const_mul (x i))
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hind
    (fun i _ => (hsg i).const_mul (x i))
  have hvariance : (∑ i,(x i)^2*(σ : ℝ)^2) ≤ (Fintype.card ι : ℝ)*(σ : ℝ)^2*c^2 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right ((sq_le_sq₀ (abs_nonneg (x i)) hc).mpr (hb i))
        (sq_nonneg (σ : ℝ)))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm (c^2),mul_assoc] using hsum
  have hi : Integrable (fun ω => Real.exp (s*(∑ i,x i*E i ω))) P := hs.integrable_exp_mul s
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
  apply ENNReal.ofReal_le_ofReal
  have heq : (fun ω => Real.exp (s*(∑ i,x i*E i ω))) =
      fun ω => ∏ i,Real.exp ((s*x i)*E i ω) := by
    funext ω
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  rw [heq,hiid.integral_fun_prod_comp (f := fun i z => Real.exp ((s*x i)*z))
    (fun i => (hsg i).aemeasurable)
    (fun i => (Real.measurable_exp.comp (measurable_id.const_mul (s*x i))).aestronglyMeasurable)]
  have hp : (∏ i,∫ ω,Real.exp ((s*x i)*E i ω) ∂P) ≤
      ∏ i,Real.exp ((σ : ℝ)^2*(s*x i)^2/2) := by
    apply Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
    intro i _
    exact (hsg i).mgf_le (s*x i)
  rw [←Real.exp_sum] at hp
  have hv : (∑ i,(σ : ℝ)^2*(s*x i)^2/2) = (∑ i,(x i)^2*(σ : ℝ)^2)*s^2/2 := by
    rw [←Finset.sum_div,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hv] at hp
  exact hp.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg s]))

lemma lb_independent_coeff_noise_mgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X E : ι → Ω → ℝ)
    (σ : ℝ≥0) (c : ℝ) (hc : 0 ≤ c)
    (hX : ∀ i,Measurable (X i)) (hE : ∀ i,Measurable (E i))
    (hiid : iIndepFun E P)
    (hind : IndepFun (fun ω i => X i ω) (fun ω i => E i ω) P)
    (hsg : ∀ i,HasSubgaussianMGF (E i) (σ^2) P)
    (hb : ∀ i ω,|X i ω| ≤ c) (s : ℝ) :
    ∫⁻ ω,ENNReal.ofReal (Real.exp (s*(∑ i,X i ω*E i ω))) ∂P ≤
      ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)*(σ : ℝ)^2*c^2*s^2/2)) := by
  classical
  let xmap : Ω → ι → ℝ := fun ω i => X i ω
  let emap : Ω → ι → ℝ := fun ω i => E i ω
  let F : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (s*(∑ i,z.1 i*z.2 i)))
  have hx : Measurable xmap := measurable_pi_lambda _ hX
  have he : Measurable emap := measurable_pi_lambda _ hE
  have hF : Measurable F := by unfold F;fun_prop
  have hxprob : IsProbabilityMeasure (P.map xmap) := Measure.isProbabilityMeasure_map hx.aemeasurable
  letI := hxprob
  have heprob : IsProbabilityMeasure (P.map emap) := Measure.isProbabilityMeasure_map he.aemeasurable
  letI := heprob
  have hbound : ∀ᵐ x ∂P.map xmap,∀ i,|x i| ≤ c := by
    rw [ae_map_iff hx.aemeasurable (by
      simp only [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro i
      exact measurableSet_le ((measurable_pi_apply i).abs) measurable_const)]
    exact ae_of_all _ (fun ω i => hb i ω)
  have hjoint := hind.map_prod_eq_prod_map_map hx.aemeasurable he.aemeasurable
  change (∫⁻ ω,F (xmap ω,emap ω) ∂P) ≤ _
  rw [←lintegral_map hF (hx.prodMk he),hjoint,lintegral_prod F hF.aemeasurable]
  have hinner : ∀ᵐ x ∂P.map xmap,(∫⁻ e,F (x,e) ∂P.map emap) ≤
      ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)*(σ : ℝ)^2*c^2*s^2/2)) := by
    filter_upwards [hbound] with x hb'
    have hFi : Measurable (fun e => F (x,e)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hFi he]
    exact lb_constant_coeff_noise_mgf P E σ c hc hiid hsg x hb' s
  exact (lintegral_mono_ae hinner).trans_eq (by simp)

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_independent_coordinate_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (X : ι → Ω → Fin d → ℝ)
    (E : ι → Ω → ℝ) (σ : ℝ≥0) (c r : ℝ) (hn : 0 < Fintype.card ι)
    (hσ : 0 < σ) (hc : 0 < c) (hr : 0 < r)
    (hX : ∀ i,Measurable (X i)) (hE : ∀ i,Measurable (E i)) (hiid : iIndepFun E P)
    (hind : IndepFun (fun ω i => X i ω) (fun ω i => E i ω) P)
    (hsg : ∀ i,HasSubgaussianMGF (E i) (σ^2) P) (hb : ∀ i ω,‖X i ω‖ ≤ c)
    (j : Fin d) :
    P {ω | r < |(∑ i,E i ω*X i ω j)/(Fintype.card ι : ℝ)|} ≤
      ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*r^2/(2*(σ : ℝ)^2*c^2))) := by
  let Y : ι → Ω → ℝ := fun i ω => X i ω j
  have hY : ∀ i,Measurable (Y i) := fun i => (measurable_pi_apply j).comp (hX i)
  have hYb : ∀ i ω,|Y i ω| ≤ c := by
    intro i ω
    exact (show |X i ω j| ≤ ‖X i ω‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (X i ω) j).trans (hb i ω)
  have hind' : IndepFun (fun ω i => Y i ω) (fun ω i => E i ω) P := by
    exact hind.comp (measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply j).comp (measurable_pi_apply i))) measurable_id
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hm := lb_independent_coeff_noise_mgf P Y E σ c hc.le hY hE hiid hind' hsg hYb
  have hS : Measurable (fun ω => ∑ i,Y i ω*E i ω) :=
    Finset.measurable_sum _ (fun i _ => (hY i).mul (hE i))
  have ht := lb_mgf_tail P (fun ω => ∑ i,Y i ω*E i ω) hS
    ((σ : ℝ)^2*c^2*Fintype.card ι) ((Fintype.card ι : ℝ)*r) (by positivity) (by positivity) (by
      intro s
      have he : (Fintype.card ι : ℝ)*(σ : ℝ)^2*c^2*s^2/2=((σ : ℝ)^2*c^2*Fintype.card ι)*s^2/2 := by ring
      simpa only [he] using hm s)
  have he : {ω | r < |(∑ i,E i ω*X i ω j)/(Fintype.card ι : ℝ)|} =
      {ω | (Fintype.card ι : ℝ)*r < |∑ i,Y i ω*E i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq,abs_div,abs_of_pos hn',lt_div_iff₀ hn']
    simp only [Y,mul_comm (E _ ω),mul_comm r]
  rw [he]
  have heq : -((Fintype.card ι : ℝ)*r)^2/(2*((σ : ℝ)^2*c^2*Fintype.card ι)) =
      -(Fintype.card ι : ℝ)*r^2/(2*(σ : ℝ)^2*c^2) := by field_simp <;> ring
  simpa only [heq] using ht

lemma lb_independent_noise_max_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (X : ι → Ω → Fin d → ℝ)
    (E : ι → Ω → ℝ) (σ : ℝ≥0) (c r : ℝ) (hn : 0 < Fintype.card ι)
    (hσ : 0 < σ) (hc : 0 < c) (hr : 0 < r)
    (hX : ∀ i,Measurable (X i)) (hE : ∀ i,Measurable (E i)) (hiid : iIndepFun E P)
    (hind : IndepFun (fun ω i => X i ω) (fun ω i => E i ω) P)
    (hsg : ∀ i,HasSubgaussianMGF (E i) (σ^2) P) (hb : ∀ i ω,‖X i ω‖ ≤ c) :
    P {ω | ∃ j : Fin d,r < |(∑ i,E i ω*X i ω j)/(Fintype.card ι : ℝ)|} ≤
      ENNReal.ofReal (2*d*Real.exp (-(Fintype.card ι : ℝ)*r^2/(2*(σ : ℝ)^2*c^2))) := by
  let A : Fin d → Set Ω := fun j => {ω | r < |(∑ i,E i ω*X i ω j)/(Fintype.card ι : ℝ)|}
  have hA := fun j => lb_independent_coordinate_tail P X E σ c r hn hσ hc hr hX hE hiid hind hsg hb j
  have hsub : {ω | ∃ j : Fin d,r < |(∑ i,E i ω*X i ω j)/(Fintype.card ι : ℝ)|} ⊆ ⋃ j,A j := by
    rintro ω ⟨j,h⟩
    exact Set.mem_iUnion.mpr ⟨j,h⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j,P (A j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin d,ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*r^2/(2*(σ : ℝ)^2*c^2))) :=
      Finset.sum_le_sum (fun j _ => hA j)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring

end BastaniBayati.LassoBandit

/- Freedman bound credited to mrfancypants, accepted submission 34d450b7-57ec-4923-81fa-627230f83e2a. -/

open MeasureTheory

namespace StochLinOpt.UpperBound

lemma aux_fr_H (x : ℝ) : 0 ≤ (x - 1) * Real.exp x + 1 := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  nlinarith

lemma aux_fr_G_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2) ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 x := (hasDerivAt_id x).sub_const 2
  have h2 := (h1.mul (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)
  have h3 := h2.add_const 2
  exact h3.congr_deriv (by ring)

lemma aux_fr_G_mono : Monotone (fun y : ℝ => (y - 2) * Real.exp y + y + 2) := by
  apply monotone_of_deriv_nonneg
  · intro x; exact (aux_fr_G_deriv x).differentiableAt
  · intro x; rw [(aux_fr_G_deriv x).deriv]; exact aux_fr_H x

lemma aux_fr_F_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y))
      (((x - 2) * Real.exp x + x + 2) / 3) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ => 1 - y / 3) (-(1/3)) x := by
    simpa using ((hasDerivAt_id x).div_const 3).const_sub 1
  have h3 : HasDerivAt (fun y : ℝ => Real.exp y - 1 - y) (Real.exp x - 1) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)
  have := h1.sub (h2.mul h3)
  exact this.congr_deriv (by ring)

lemma aux_fr_exp_ineq (y : ℝ) : (1 - y / 3) * (Real.exp y - 1 - y) ≤ y ^ 2 / 2 := by
  set F : ℝ → ℝ := fun y => y ^ 2 / 2 - (1 - y / 3) * (Real.exp y - 1 - y) with hF
  have hG0 : ((0:ℝ) - 2) * Real.exp 0 + 0 + 2 = 0 := by simp
  have hcont : Continuous F := by
    rw [hF]; fun_prop
  have hdiff : Differentiable ℝ F := fun x => (aux_fr_F_deriv x).differentiableAt
  have hF0 : F 0 = 0 := by simp [hF]
  suffices 0 ≤ F y by simp only [hF] at this; linarith
  rcases le_total y 0 with hy | hy
  · have hanti : AntitoneOn F (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Iio.mp hx))
      simp only at this
      linarith
    have := hanti (Set.mem_Iic.mpr hy) (Set.mem_Iic.mpr le_rfl) hy
    linarith
  · have hmono : MonotoneOn F (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(aux_fr_F_deriv x).deriv]
      have := aux_fr_G_mono (le_of_lt (Set.mem_Ioi.mp hx))
      simp only at this
      linarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
    linarith

lemma aux_fr_pw (l b x : ℝ) (hl : 0 < l) (hd : 0 < 1 - l * b / 3) (hx : x ≤ b) :
    Real.exp (l * x) ≤ 1 + l * x + l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
  have h1 := aux_fr_exp_ineq (l * x)
  have h2 : 0 ≤ Real.exp (l * x) - 1 - l * x := by
    have := Real.add_one_le_exp (l * x); linarith
  have h3 : l * x ≤ l * b := mul_le_mul_of_nonneg_left hx hl.le
  have h4 : (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x) ≤ (l * x) ^ 2 / 2 := by
    calc (1 - l * b / 3) * (Real.exp (l * x) - 1 - l * x)
        ≤ (1 - l * x / 3) * (Real.exp (l * x) - 1 - l * x) := by
          apply mul_le_mul_of_nonneg_right _ h2; linarith
      _ ≤ _ := h1
  have h5 : Real.exp (l * x) - 1 - l * x ≤ l ^ 2 / (2 * (1 - l * b / 3)) * x ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  linarith


lemma aux_fr_int_condExp {Ω : Type*} {m mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Y Z : Ω → ℝ) (hY : StronglyMeasurable[m] Y)
    (hYZ : Integrable (fun ω => Y ω * Z ω) P) (hZ : Integrable Z P) :
    ∫ ω, Y ω * Z ω ∂P = ∫ ω, Y ω * (P[Z | m]) ω ∂P := by
  calc ∫ ω, Y ω * Z ω ∂P = ∫ ω, (P[Y * Z | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (Y * P[Z | m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hY hYZ hZ)
    _ = _ := rfl

lemma aux_fr_main {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (l c : ℝ) (hl : 0 < l) (hc : 0 ≤ c)
    (hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2)
    (V : ℕ → Ω → ℝ) (hV : ∀ i, V i = P[fun ω' => X i ω' ^ 2 | 𝓕 i]) :
    ∀ k ≤ T, Integrable (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω)) P ∧
      ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P ≤ 1 := by
  have hVsm : ∀ i, StronglyMeasurable[𝓕 i] (V i) := fun i => by
    rw [hV]; exact stronglyMeasurable_condExp
  have hVint : ∀ i, Integrable (V i) P := fun i => by rw [hV]; exact integrable_condExp
  have hVnn : ∀ i, 0 ≤ᵐ[P] V i := fun i => by
    rw [hV]; exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hgood : ∀ᵐ ω ∂P, ∀ i ∈ Finset.Icc 1 T, X i ω ≤ b ∧ 0 ≤ V i ω := by
    rw [Filter.eventually_all_finset]
    intro i hi
    filter_upwards [hb i hi, hVnn i] with ω h1 h2
    exact ⟨h1, h2⟩
  have hXm0 : ∀ i ∈ Finset.Icc 1 T, Measurable (X i) := fun i hi =>
    (hmeas i hi).mono (𝓕.le _) le_rfl
  have hWm : ∀ k, Measurable[𝓕 k] (fun ω => ∑ i ∈ Finset.Icc 1 k, V i ω) := fun k =>
    Finset.measurable_sum _ (fun i hi =>
      (hVsm i).measurable.mono (𝓕.mono (by simp at hi; omega)) le_rfl)
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨ihint, ihle⟩ := ih (by omega)
    have hk1 : k + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hk⟩
    have hSm : Measurable[𝓕 (k+1)] (fun ω => ∑ i ∈ Finset.Icc 1 k, X i ω) :=
      Finset.measurable_sum _ (fun i hi =>
        (hmeas i (by simp at hi ⊢; omega)).mono (𝓕.mono (by simp at hi; omega)) le_rfl)
    set Y : Ω → ℝ := fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) with hYdef
    have hYm : StronglyMeasurable[𝓕 (k+1)] Y := by
      have : Measurable[𝓕 (k+1)] Y := by
        apply Real.measurable_exp.comp
        exact ((hSm.const_mul l).sub (((hWm k).mono (𝓕.mono (Nat.le_succ k)) le_rfl).const_mul c)).sub
          ((hVsm (k+1)).measurable.const_mul c)
      exact this.stronglyMeasurable
    have hYae : AEStronglyMeasurable Y P := (hYm.mono (𝓕.le _)).aestronglyMeasurable
    have hYbd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 k, b) := by
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 : ∑ i ∈ Finset.Icc 1 k, X i ω ≤ ∑ i ∈ Finset.Icc 1 k, b :=
        Finset.sum_le_sum (fun i hi => (hω i (by simp at hi ⊢; omega)).1)
      have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, V i ω :=
        Finset.sum_nonneg (fun i hi => (hω i (by simp at hi ⊢; omega)).2)
      have h3 : 0 ≤ V (k+1) ω := (hω (k+1) hk1).2
      nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_nonneg hc h2, mul_nonneg hc h3]
    have hYint : Integrable Y P := Integrable.of_bound hYae _ hYbd
    have hEm : Measurable (fun ω => Real.exp (l * X (k+1) ω)) :=
      Real.measurable_exp.comp ((hXm0 _ hk1).const_mul l)
    have hEint : Integrable (fun ω => Real.exp (l * X (k+1) ω)) P := by
      refine Integrable.of_bound hEm.aestronglyMeasurable (Real.exp (l * b)) ?_
      filter_upwards [hgood] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hω (k+1) hk1).1 hl.le)
    have hfun : (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 (k+1), X i ω
        - c * ∑ i ∈ Finset.Icc 1 (k+1), V i ω)) =
        fun ω => Y ω * Real.exp (l * X (k+1) ω) := by
      funext ω
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), hYdef,
        ← Real.exp_add]
      congr 1; ring
    have hMint : Integrable (fun ω => Y ω * Real.exp (l * X (k+1) ω)) P :=
      hEint.bdd_mul hYae hYbd
    rw [hfun]
    refine ⟨hMint, ?_⟩
    have hYX : Integrable (fun ω => Y ω * X (k+1) ω) P := (hint _ hk1).bdd_mul hYae hYbd
    have hYX2 : Integrable (fun ω => Y ω * X (k+1) ω ^ 2) P := (hint_sq _ hk1).bdd_mul hYae hYbd
    have hYV : Integrable (fun ω => Y ω * V (k+1) ω) P := (hVint _).bdd_mul hYae hYbd
    have hYX0 : ∫ ω, Y ω * X (k+1) ω ∂P = 0 := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (X (k+1)) hYm hYX (hint _ hk1)]
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
      · simp
      filter_upwards [hmds _ hk1] with ω hω
      simp [hω]
    have hYX2V : ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P = ∫ ω, Y ω * V (k+1) ω ∂P := by
      rw [aux_fr_int_condExp P (𝓕.le (k+1)) Y (fun ω => X (k+1) ω ^ 2) hYm hYX2 (hint_sq _ hk1),
        hV]
    have hYpos : ∀ ω, 0 < Y ω := fun ω => Real.exp_pos _
    have i1 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω)) P := hYint.add (hYX.const_mul l)
    have i2 : Integrable (fun ω => Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) P :=
      i1.add (hYX2.const_mul c)
    have i3 : Integrable (fun ω => Y ω + c * (Y ω * V (k+1) ω)) P := hYint.add (hYV.const_mul c)
    calc ∫ ω, Y ω * Real.exp (l * X (k+1) ω) ∂P
        ≤ ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P := by
          apply integral_mono_ae hMint i2
          filter_upwards [hgood] with ω hω
          have := mul_le_mul_of_nonneg_left (hpw _ (hω (k+1) hk1).1) (hYpos ω).le
          linarith
      _ = ∫ ω, Y ω ∂P + l * ∫ ω, Y ω * X (k+1) ω ∂P + c * ∫ ω, Y ω * X (k+1) ω ^ 2 ∂P := by
          have e1 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω) + c * (Y ω * X (k+1) ω ^ 2)) ∂P =
              ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P + ∫ ω, c * (Y ω * X (k+1) ω ^ 2) ∂P :=
            integral_add i1 (hYX2.const_mul c)
          have e2 : ∫ ω, (Y ω + l * (Y ω * X (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, l * (Y ω * X (k+1) ω) ∂P :=
            integral_add hYint (hYX.const_mul l)
          rw [e1, e2, integral_const_mul, integral_const_mul]
      _ = ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P := by
          have e3 : ∫ ω, (Y ω + c * (Y ω * V (k+1) ω)) ∂P =
              ∫ ω, Y ω ∂P + ∫ ω, c * (Y ω * V (k+1) ω) ∂P :=
            integral_add hYint (hYV.const_mul c)
          rw [hYX0, hYX2V, e3, integral_const_mul]; ring
      _ ≤ ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
            - c * ∑ i ∈ Finset.Icc 1 k, V i ω) ∂P := by
          apply integral_mono_ae i3 ihint
          filter_upwards with ω
          show Y ω + c * (Y ω * V (k+1) ω) ≤ _
          have hY : Y ω = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω - c * V (k+1) ω) := rfl
          have h1 := Real.add_one_le_exp (c * V (k+1) ω)
          have h2 : Y ω * Real.exp (c * V (k+1) ω) = Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
              - c * ∑ i ∈ Finset.Icc 1 k, V i ω) := by
            rw [hY, ← Real.exp_add]; congr 1; ring
          have h3 := hYpos ω
          nlinarith
      _ ≤ 1 := ihle

theorem aux_fr_final {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[𝓕 (i + 1)] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | 𝓕 i] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
  by_cases hD : 2 * v + 2 * a * b / 3 ≤ 0
  · have h1 : 1 ≤ Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
      apply Real.one_le_exp
      exact div_nonneg_of_nonpos (by nlinarith) hD
    exact le_trans measureReal_le_one h1
  push Not at hD
  have hD' : 0 < v + a * b / 3 := by linarith
  set l := a / (v + a * b / 3) with hl_def
  have hl : 0 < l := div_pos ha hD'
  have hne' : v * 3 + a * b ≠ 0 := by
    have : 0 < v * 3 + a * b := by linarith
    exact this.ne'
  have hd : 1 - l * b / 3 = v / (v + a * b / 3) := by
    have hne : v + a * b / 3 ≠ 0 := hD'.ne'
    rw [hl_def]
    field_simp
    ring
  have hdpos : 0 < 1 - l * b / 3 := by rw [hd]; exact div_pos hv hD'
  set c := l ^ 2 / (2 * (1 - l * b / 3)) with hc_def
  have hc : 0 ≤ c := by positivity
  have hpw : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2 := fun x hx =>
    aux_fr_pw l b x hl hdpos hx
  obtain ⟨hMint, hMle⟩ := aux_fr_main P 𝓕 X T b hmeas hint hint_sq hmds hb l c hl hc hpw
    (fun i => P[fun ω' => X i ω' ^ 2 | 𝓕 i]) (fun i => rfl) T le_rfl
  set ε := Real.exp (l * a - c * v) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hsub : {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω ≤ v} ⊆
      {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_ofPred_eq, hε]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h1 hl.le, mul_le_mul_of_nonneg_left h2 hc]
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hMint ε
  have hmono := measureReal_mono (μ := P) hsub
  have key : P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)} ≤ ε⁻¹ := by
    have h1 := hmk.trans hMle
    calc _ = ε⁻¹ * (ε * P.real {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | 𝓕 i] ω)}) := by
          rw [← mul_assoc, inv_mul_cancel₀ hεpos.ne', one_mul]
      _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hεpos.le)
      _ = ε⁻¹ := mul_one _
  have halg : ε⁻¹ = Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
    rw [hε, ← Real.exp_neg]
    congr 1
    rw [hc_def, hd, hl_def]
    field_simp
    ring
  linarith


end StochLinOpt.UpperBound

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
namespace BastaniBayati.LassoBandit

/- Pointwise exponential inequality credited to mrfancypants,
accepted Freedman submission 34d450b7-57ec-4923-81fa-627230f83e2a. -/
lemma lb_bernstein_point (s b x : ℝ) (hb : 0 ≤ b) (hsmall : |s| *b ≤ 1) (hx : |x| ≤ b) :
    Real.exp (s*x) ≤ 1+s*x+s^2*x^2 := by
  have main : ∀ l y : ℝ,0 < l → l*b ≤ 1 → y ≤ b →
      Real.exp (l*y) ≤ 1+l*y+l^2*y^2 := by
    intro l y hl hsmall hy
    have hd : 0 < 1-l*b/3 := by linarith
    have ht := StochLinOpt.UpperBound.aux_fr_pw l b y hl hd hy
    have hcoef : l^2/(2*(1-l*b/3)) ≤ l^2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg l,mul_le_mul_of_nonneg_left hsmall (sq_nonneg l)]
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)])
  rcases lt_trichotomy 0 s with hs | hs | hs
  · exact main s x hs (by simpa only [abs_of_pos hs] using hsmall) (le_abs_self x |>.trans hx)
  · simp [←hs]
  · have ht := main (-s) (-x) (by linarith)
      (by simpa only [abs_of_neg hs] using hsmall) (neg_le_abs x |>.trans hx)
    simpa only [neg_mul_neg,neg_sq] using ht

lemma lb_bounded_variance_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → ℝ) (b v : ℝ) (hb : 0 ≤ b) (hv : 0 ≤ v)
    (hW : Measurable W) (hbound : ∀ ω,|W ω| ≤ b)
    (hmean : ∫ ω,W ω ∂P=0) (hvar : ∫ ω,(W ω)^2 ∂P ≤ v)
    (s : ℝ) (hsmall : |s| *b ≤ 1) :
    Integrable (fun ω => Real.exp (s*W ω)) P ∧
      (∫ ω,Real.exp (s*W ω) ∂P) ≤ Real.exp (s^2*v) := by
  have hi : Integrable W P := Integrable.of_bound hW.aestronglyMeasurable b
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hbound ω))
  have hi2 : Integrable (fun ω => (W ω)^2) P := Integrable.of_bound (hW.pow_const 2).aestronglyMeasurable
    (b^2) (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (W ω)) hb).mpr (hbound ω)))
  have he : Integrable (fun ω => Real.exp (s*W ω)) P :=
    Integrable.of_bound (hW.const_mul s).exp.aestronglyMeasurable (Real.exp (|s| *b))
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg s))))
  refine ⟨he,?_⟩
  have hr : Integrable (fun ω => 1+s*W ω+s^2*(W ω)^2) P :=
    ((integrable_const 1).add (hi.const_mul s)).add (hi2.const_mul (s^2))
  calc _ ≤ ∫ ω,1+s*W ω+s^2*(W ω)^2 ∂P :=
      integral_mono he hr (fun ω => lb_bernstein_point s b (W ω) hb hsmall (hbound ω))
    _ = 1+s^2*(∫ ω,(W ω)^2 ∂P) := by
      have h1 : Integrable (fun ω => 1+s*W ω) P := (integrable_const 1).add (hi.const_mul s)
      have e1 := integral_add h1 (hi2.const_mul (s^2))
      have e2 := integral_add (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P) (hi.const_mul s)
      rw [e1,e2,integral_const_mul,integral_const_mul,hmean]
      simp
    _ ≤ 1+s^2*v := by nlinarith [mul_le_mul_of_nonneg_left hvar (sq_nonneg s)]
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (s^2*v)

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
namespace BastaniBayati.LassoBandit

lemma lb_iid_variance_mgf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ι → Ω → ℝ) (b v : ℝ)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hW : ∀ i,Measurable (W i)) (hiid : iIndepFun W P)
    (hbound : ∀ i ω,|W i ω| ≤ b) (hmean : ∀ i,∫ ω,W i ω ∂P=0)
    (hvar : ∀ i,∫ ω,(W i ω)^2 ∂P ≤ v) (s : ℝ) (hsmall : |s| *b ≤ 1) :
    Integrable (fun ω => Real.exp (s*(∑ i,W i ω))) P ∧
      (∫ ω,Real.exp (s*(∑ i,W i ω)) ∂P) ≤ Real.exp ((Fintype.card ι : ℝ)*s^2*v) := by
  classical
  have hscalar := fun i => lb_bounded_variance_mgf P (W i) b v hb hv (hW i)
    (hbound i) (hmean i) (hvar i) s hsmall
  have hsum : Measurable (fun ω => ∑ i,W i ω) := Finset.measurable_sum _ (fun i _ => hW i)
  have hi : Integrable (fun ω => Real.exp (s*(∑ i,W i ω))) P :=
    Integrable.of_bound (hsum.const_mul s).exp.aestronglyMeasurable
      (Real.exp (|s| *((Fintype.card ι : ℝ)*b))) (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc s*(∑ i,W i ω) ≤ |s*(∑ i,W i ω)| := le_abs_self _
          _ = |s| *|∑ i,W i ω| := abs_mul _ _
          _ ≤ |s| *(∑ i,|W i ω|) := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
          _ ≤ |s| *((Fintype.card ι : ℝ)*b) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i ω)))
  refine ⟨hi,?_⟩
  have hfun : (fun ω => Real.exp (s*(∑ i,W i ω))) = fun ω => ∏ i,Real.exp (s*W i ω) := by
    funext ω
    rw [Finset.mul_sum,Real.exp_sum]
  rw [hfun,hiid.integral_fun_prod_comp (f := fun _ z => Real.exp (s*z)) (fun i => (hW i).aemeasurable)
    (fun _ => (Real.measurable_exp.comp (measurable_id.const_mul s)).aestronglyMeasurable)]
  have hprod : (∏ i,∫ ω,Real.exp (s*W i ω) ∂P) ≤ (∏ _i : ι,Real.exp (s^2*v)) := by
    exact Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
      (fun i _ => (hscalar i).2)
  have heq : (∏ _i : ι,Real.exp (s^2*v)) = Real.exp ((Fintype.card ι : ℝ)*s^2*v) := by
    rw [←Real.exp_sum]
    congr 1
    simp [mul_assoc]
  exact hprod.trans_eq heq

lemma lb_centered_variance_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (c v : ℝ) (hc : 0 ≤ c) (hv : 0 ≤ v)
    (hY : Measurable Y) (hbound : ∀ ω,|Y ω| ≤ c)
    (hsecond : ∫ ω,(Y ω)^2 ∂P ≤ v) (s : ℝ) (hsmall : |s| *(2*c) ≤ 1) :
    Integrable (fun ω => Real.exp (s*(Y ω-∫ z,Y z ∂P))) P ∧
      (∫ ω,Real.exp (s*(Y ω-∫ z,Y z ∂P)) ∂P) ≤ Real.exp (s^2*v) := by
  let m := ∫ ω,Y ω ∂P
  have hmeanbound : |m| ≤ c := by
    have h := norm_integral_le_of_norm_le_const (f := Y) (C := c) (ae_of_all P (fun ω =>
      by simpa only [Real.norm_eq_abs] using hbound ω))
    simpa [m,Real.norm_eq_abs,measureReal_def] using h
  have hi : Integrable Y P := Integrable.of_bound hY.aestronglyMeasurable c
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hbound ω))
  have hi2 : Integrable (fun ω => (Y ω)^2) P := Integrable.of_bound (hY.pow_const 2).aestronglyMeasurable
    (c^2) (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Y ω)) hc).mpr (hbound ω)))
  have hm : ∫ ω,Y ω-m ∂P=0 := by rw [integral_sub hi (integrable_const m)];simp [m]
  have hsq : ∫ ω,(Y ω-m)^2 ∂P=(∫ ω,(Y ω)^2 ∂P)-m^2 := by
    have he : (fun ω => (Y ω-m)^2) = fun ω => ((Y ω)^2-2*m*Y ω)+m^2 := by funext ω;ring
    have h1 : Integrable (fun ω => (Y ω)^2-2*m*Y ω) P := hi2.sub (hi.const_mul (2*m))
    have e1 := integral_add h1 (integrable_const (m^2))
    have e2 := integral_sub hi2 (hi.const_mul (2*m))
    rw [he,e1,e2,integral_const_mul]
    simp [m] <;> ring
  have hv' : ∫ ω,(Y ω-m)^2 ∂P ≤ v := by rw [hsq];linarith [sq_nonneg m]
  apply lb_bounded_variance_mgf P (fun ω => Y ω-m) (2*c) v (by positivity) hv
    (hY.sub_const m) _ hm hv' s hsmall
  intro ω
  calc |Y ω-m| ≤ |Y ω|+|m| := abs_sub _ _
    _ ≤ 2*c := by linarith [hbound ω]

end BastaniBayati.LassoBandit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BastaniBayati.LassoBandit

lemma lb_fixed_chernoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℝ) (s r B : ℝ) (hs : 0 ≤ s)
    (hiPos : Integrable (fun ω => Real.exp (s*S ω)) P)
    (hiNeg : Integrable (fun ω => Real.exp ((-s)*S ω)) P)
    (hPos : (∫ ω,Real.exp (s*S ω) ∂P) ≤ Real.exp B)
    (hNeg : (∫ ω,Real.exp ((-s)*S ω) ∂P) ≤ Real.exp B) :
    P {ω | r < |S ω|} ≤ ENNReal.ofReal (2*Real.exp (B-s*r)) := by
  have hp : P.real {ω | r ≤ S ω} ≤ Real.exp (B-s*r) := by
    calc _ ≤ Real.exp (-s*r)*mgf S P s := measure_ge_le_exp_mul_mgf r hs hiPos
      _ ≤ Real.exp (-s*r)*Real.exp B := mul_le_mul_of_nonneg_left hPos (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hiNeg' : Integrable (fun ω => Real.exp (s*(-S ω))) P := by simpa only [mul_neg,neg_mul] using hiNeg
  have hNeg' : mgf (fun ω => -S ω) P s ≤ Real.exp B := by simpa only [mgf,mul_neg,neg_mul] using hNeg
  have hn : P.real {ω | r ≤ -S ω} ≤ Real.exp (B-s*r) := by
    calc _ ≤ Real.exp (-s*r)*mgf (fun ω => -S ω) P s := measure_ge_le_exp_mul_mgf r hs hiNeg'
      _ ≤ Real.exp (-s*r)*Real.exp B := mul_le_mul_of_nonneg_left hNeg' (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hsub : {ω | r < |S ω|} ⊆ {ω | r ≤ S ω} ∪ {ω | r ≤ -S ω} := by
    intro ω hω
    change r < |S ω| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  have hreal : P.real {ω | r < |S ω|} ≤ 2*Real.exp (B-s*r) := by
    calc _ ≤ P.real ({ω | r ≤ S ω} ∪ {ω | r ≤ -S ω}) := measureReal_mono hsub
      _ ≤ P.real {ω | r ≤ S ω}+P.real {ω | r ≤ -S ω} := measureReal_union_le _ _
      _ ≤ _ := by linarith
  rw [←ENNReal.ofReal_toReal (measure_ne_top P {ω | r < |S ω|})]
  exact ENNReal.ofReal_le_ofReal hreal

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BastaniBayati.LassoBandit

lemma lb_iid_rare_variance_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ι → Ω → ℝ) (c r u : ℝ)
    (hn : 0 < Fintype.card ι) (hc : 0 < c) (hr : 0 < r) (hu : 0 < u) (huSmall : u ≤ 1/2)
    (hW : ∀ i,Measurable (W i)) (hiid : iIndepFun W P)
    (hbound : ∀ i ω,|W i ω| ≤ 2*c) (hmean : ∀ i,∫ ω,W i ω ∂P=0)
    (hvar : ∀ i,∫ ω,(W i ω)^2 ∂P ≤ r*c^2) :
    P {ω | 2*r*c*u < |(∑ i,W i ω)/(Fintype.card ι : ℝ)|} ≤
      ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*r*u^2)) := by
  let s := u/c
  have hs : 0 < s := by dsimp [s];positivity
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hsmall : |s| *(2*c) ≤ 1 := by
    rw [abs_of_pos hs]
    dsimp [s]
    have he : u/c*(2*c)=2*u := by field_simp
    rw [he]
    linarith
  have hp := lb_iid_variance_mgf P W (2*c) (r*c^2) (by positivity) (by positivity)
    hW hiid hbound hmean hvar s hsmall
  have hm := lb_iid_variance_mgf P W (2*c) (r*c^2) (by positivity) (by positivity)
    hW hiid hbound hmean hvar (-s) (by simpa only [abs_neg] using hsmall)
  have ht := lb_fixed_chernoff P (fun ω => ∑ i,W i ω) s
    ((Fintype.card ι : ℝ)*(2*r*c*u)) ((Fintype.card ι : ℝ)*s^2*(r*c^2)) hs.le
    hp.1 hm.1 hp.2 (by simpa only [neg_sq] using hm.2)
  have he : {ω | 2*r*c*u < |(∑ i,W i ω)/(Fintype.card ι : ℝ)|} =
      {ω | (Fintype.card ι : ℝ)*(2*r*c*u) < |∑ i,W i ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq,abs_div,abs_of_pos hn',lt_div_iff₀ hn']
    rw [mul_comm (2*r*c*u)]
  rw [he]
  have hexp : (Fintype.card ι : ℝ)*s^2*(r*c^2)-s*((Fintype.card ι : ℝ)*(2*r*c*u)) =
      -(Fintype.card ι : ℝ)*r*u^2 := by dsimp [s];field_simp <;> ring
  simpa only [hexp] using ht

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
namespace BastaniBayati.LassoBandit

lemma lb_indicator_centered_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : Set Ω) (hE : MeasurableSet E) (Y : Ω → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hY : Measurable Y) (hb : ∀ ω,|Y ω| ≤ c) :
    let V := E.indicator Y
    let W := fun ω => V ω-∫ z,V z ∂P
    Measurable W ∧ (∀ ω,|W ω| ≤ 2*c) ∧ (∫ ω,W ω ∂P)=0 ∧
      (∫ ω,(W ω)^2 ∂P) ≤ P.real E*c^2 := by
  classical
  dsimp only
  let V := E.indicator Y
  let m := ∫ ω,V ω ∂P
  have hV : Measurable V := hY.indicator hE
  have hVb : ∀ ω,|V ω| ≤ c := by
    intro ω
    by_cases h : ω ∈ E
    · simpa only [V,Set.indicator_of_mem h] using hb ω
    · simpa only [V,Set.indicator_of_notMem h,abs_zero] using hc
  have hi : Integrable V P := Integrable.of_bound hV.aestronglyMeasurable c
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hVb ω))
  have hm : |m| ≤ c := by
    have h := norm_integral_le_of_norm_le_const (f := V) (C := c)
      (ae_of_all P (fun ω => by simpa only [Real.norm_eq_abs] using hVb ω))
    simpa [m,Real.norm_eq_abs,measureReal_def] using h
  have hLp : MemLp V 2 P := MemLp.of_bound hV.aestronglyMeasurable c
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hVb ω))
  have hsq : ∫ ω,(V ω-m)^2 ∂P=(∫ ω,(V ω)^2 ∂P)-m^2 := by
    rw [←variance_eq_integral hV.aemeasurable,variance_eq_sub hLp]
    rfl
  have hi2 : Integrable (fun ω => (V ω)^2) P := Integrable.of_bound (hV.pow_const 2).aestronglyMeasurable
    (c^2) (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (V ω)) hc).mpr (hVb ω)))
  have hsec : ∫ ω,(V ω)^2 ∂P ≤ P.real E*c^2 := by
    have hraw : (∫ ω,(V ω)^2 ∂P) ≤ (∫ ω,E.indicator (fun _ => c^2) ω ∂P) := by
      apply integral_mono hi2 ((integrable_const (c^2)).indicator hE)
      intro ω
      by_cases h : ω ∈ E
      · simp only [V,Set.indicator_of_mem h]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Y ω)) hc).mpr (hb ω)
      · simp only [V,Set.indicator_of_notMem h,zero_pow (by decide : 2 ≠ 0)]
        exact le_rfl
    have heq : (∫ ω,E.indicator (fun _ => c^2) ω ∂P) = P.real E*c^2 := by
      rw [integral_indicator hE]
      simp [measureReal_def]
    exact hraw.trans_eq heq
  refine ⟨hV.sub_const m,?_,?_,?_⟩
  · intro ω
    calc |V ω-m| ≤ |V ω|+|m| := abs_sub _ _
      _ ≤ 2*c := by linarith [hVb ω]
  · rw [integral_sub hi (integrable_const m)];simp [m]
  · rw [hsq];linarith [sq_nonneg m]

end BastaniBayati.LassoBandit

/- Matrix rank-one update helpers credited to Nickrobbins95, accepted OFUL submission 028e111f-382d-40d0-8008-127228d5e6cf. -/
set_option autoImplicit false
namespace ConfBallMatrix
open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_symm_dot {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (v w : Fin d → ℝ) :
    v ⬝ᵥ A *ᵥ w = w ⬝ᵥ A *ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_vecMulVec_mulVec {d : ℕ} (x u : Fin d → ℝ) :
    vecMulVec x x *ᵥ u = (x ⬝ᵥ u) • x := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_posdef_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : Vᵀ = V := by
  have := hV.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  exact this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : (V⁻¹)ᵀ = V⁻¹ := by
  rw [transpose_nonsing_inv, e5_posdef_transpose hV]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_unit {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : IsUnit V.det :=
  isUnit_iff_ne_zero.mpr hV.det_pos.ne'

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_mulVec_inv {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V *ᵥ (V⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_mulVec {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V⁻¹ *ᵥ (V *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_a_nonneg {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ V⁻¹ *ᵥ x := by
  have := hV.inv.posSemidef.dotProduct_mulVec_nonneg x
  simpa using this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    (V + vecMulVec x x).det = V.det * (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  rw [vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow (e5_det_unit hV)]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_quad_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x S : Fin d → ℝ)
    (e : ℝ) :
    (S + e • x) ⬝ᵥ (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) =
      S ⬝ᵥ V⁻¹ *ᵥ S + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x)
        - (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  set a := x ⬝ᵥ V⁻¹ *ᵥ x with ha_def
  set b := x ⬝ᵥ V⁻¹ *ᵥ S with hb_def
  have ha : 0 ≤ a := e5_a_nonneg hV x
  have h1a : (1 + a) ≠ 0 := by positivity
  have hdet : IsUnit V.det := e5_det_unit hV
  have hdet' : IsUnit (V + vecMulVec x x).det := by
    rw [e5_det_step hV]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hV.det_pos.ne' h1a)
  set u := V⁻¹ *ᵥ S with hu
  set w := V⁻¹ *ᵥ x with hw
  set cc := (e - b) / (1 + a) with hcc
  have hxu : x ⬝ᵥ u = b := rfl
  have hxw : x ⬝ᵥ w = a := rfl
  have hSw : S ⬝ᵥ w = b := by
    rw [hw, hb_def, e5_symm_dot (e5_inv_transpose hV)]
  have h1 : (V + vecMulVec x x) *ᵥ (u + cc • w) = S + e • x := by
    rw [add_mulVec, e5_vecMulVec_mulVec, mulVec_add, mulVec_smul, hu, hw, e5_mulVec_inv hdet,
      e5_mulVec_inv hdet, ← hu, ← hw, dotProduct_add, dotProduct_smul, hxu, hxw, smul_eq_mul,
      add_assoc, ← add_smul]
    congr 2
    rw [hcc]
    field_simp
    ring
  have key : (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) = u + cc • w := by
    rw [← h1, e5_inv_mulVec hdet']
  rw [key, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, hSw, hxu, hxw]
  simp only [smul_eq_mul]
  rw [hcc]
  field_simp
  ring


open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_det {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) :
    Measurable fun ω => (M ω).det := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hM _ _)

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_inv {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  refine (e5_meas_det hM).inv.mul (e5_meas_det fun k l => ?_)
  simp only [updateRow_apply]
  by_cases h : k = j
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]; exact hM k l

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_quad {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {M : Ω → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j)
    {v w : Ω → Fin d → ℝ} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun ω => v ω ⬝ᵥ M ω *ᵥ w ω := by
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul ((measurable_pi_apply j).comp hw)


end ConfBallMatrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix ConfBallMatrix
namespace BastaniBayati.LassoBandit

lemma lb_l1_split {d : ℕ} (I : Finset (Fin d)) (v : Fin d → ℝ) :
    l1Norm v = l1Norm (restrictTo I v)+l1Norm (restrictTo Iᶜ v) := by
  classical
  unfold l1Norm restrictTo
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ I <;> simp [hj]

lemma lb_l1_difference {d : ℕ} (β b : Fin d → ℝ) :
    l1Norm β-l1Norm b ≤ l1Norm (restrictTo (supp β) (b-β))-
      l1Norm (restrictTo (supp β)ᶜ (b-β)) := by
  classical
  unfold l1Norm
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ supp β
  · simp only [restrictTo,hj,if_pos,Finset.mem_compl,not_true_eq_false,if_false,abs_zero,sub_zero,Pi.sub_apply]
    simpa only [abs_sub_comm] using abs_sub_abs_le_abs_sub (β j) (b j)
  · have hb : β j = 0 := by simpa [supp] using hj
    simp [restrictTo,hj,hb]

lemma lb_cov_quad {n d : ℕ} (X : Fin n → Fin d → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (sampleCov X *ᵥ v) = (∑ t,(X t ⬝ᵥ v)^2)/(n : ℝ) := by
  have hm : sampleCov X = (n : ℝ)⁻¹ • ∑ t,vecMulVec (X t) (X t) := by
    ext i j
    simp [sampleCov,Matrix.smul_apply,Matrix.sum_apply,vecMulVec_apply,div_eq_mul_inv,mul_comm]
  rw [hm,smul_mulVec,sum_mulVec,dotProduct_smul,dotProduct_sum]
  simp only [smul_eq_mul]
  have he : ∀ t,v ⬝ᵥ (vecMulVec (X t) (X t) *ᵥ v) = (X t ⬝ᵥ v)^2 := by
    intro t
    rw [e5_vecMulVec_mulVec,dotProduct_smul,dotProduct_comm]
    simp [smul_eq_mul,pow_two]
  simp only [he]
  ring

lemma lb_cross_eq {n d : ℕ} (X : Fin n → Fin d → ℝ) (E : Fin n → ℝ) (v : Fin d → ℝ) :
    (∑ t,E t*(X t ⬝ᵥ v))/(n : ℝ) =
      ∑ j,((∑ t,E t*X t j)/(n : ℝ))*v j := by
  simp_rw [dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,div_mul_eq_mul_div,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

lemma lb_oracle_numeric (q U V L s φ lam : ℝ) (hs : 0 < s) (hφ : 0 < φ) (hlam : 0 < lam)
    (hq : 0 ≤ q) (hU : 0 ≤ U) (hV : 0 ≤ V) (hL : L=U+V)
    (hbasic : q+lam/2*L ≤ 2*lam*U) (hcompat : φ^2*U^2 ≤ s*q) :
    L ≤ 4*s*lam/φ^2 := by
  have h1 := mul_le_mul_of_nonneg_left hbasic (show 0 ≤ s*φ^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hcompat (sq_nonneg φ)
  have h3 := sq_nonneg (φ^2*U-s*lam)
  have hfin : (s*lam)*(φ^2*L) ≤ (s*lam)*(2*s*lam) := by nlinarith
  have hbound := (mul_le_mul_iff_of_pos_left (mul_pos hs hlam)).mp hfin
  rw [le_div_iff₀ (sq_pos_of_pos hφ)]
  nlinarith

lemma lb_lasso_oracle {n d : ℕ} (X : Fin n → Fin d → ℝ) (E : Fin n → ℝ)
    (β b : Fin d → ℝ) (s0 : ℕ) (φ lam : ℝ) (hn : 1 ≤ n)
    (hs0 : (supp β).card=s0) (hs : 1 ≤ s0) (hφ : 0 < φ) (hlam : 0 < lam)
    (hmin : IsLassoMinimizer X (fun t => X t ⬝ᵥ β+E t) lam b)
    (hnoise : ∀ j,|(∑ t,E t*X t j)/(n : ℝ)| ≤ lam/4)
    (hcompat : sampleCov X ∈ compatSet (supp β) φ) :
    l1Norm (b-β) ≤ 4*s0*lam/φ^2 := by
  classical
  let v := b-β
  let q := v ⬝ᵥ (sampleCov X *ᵥ v)
  let R := (∑ t,E t*(X t ⬝ᵥ v))/(n : ℝ)
  let U := l1Norm (restrictTo (supp β) v)
  let V := l1Norm (restrictTo (supp β)ᶜ v)
  let L := l1Norm v
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hs
  have hq : 0 ≤ q := by simpa [q] using hcompat.1.dotProduct_mulVec_nonneg v
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hL : L=U+V := lb_l1_split (supp β) v
  have hR : R ≤ lam/4*L := by
    dsimp [R]
    rw [lb_cross_eq]
    dsimp [L,l1Norm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc _ ≤ |((∑ t,E t*X t j)/(n : ℝ))*v j| := le_abs_self _
      _ = |(∑ t,E t*X t j)/(n : ℝ)| * |v j| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hnoise j) (abs_nonneg _)
  have hpen : l1Norm β-l1Norm b ≤ U-V := lb_l1_difference β b
  have hm := hmin β
  unfold lassoObjective at hm
  simp only [Fintype.card_fin] at hm
  have herr : ∀ t,X t ⬝ᵥ β+E t-X t ⬝ᵥ b = E t-X t ⬝ᵥ v := by
    intro t
    dsimp [v]
    rw [dotProduct_sub]
    ring
  have hsum : ∑ t,(E t-X t ⬝ᵥ v)^2 =
      ∑ t,E t^2-2*∑ t,E t*(X t ⬝ᵥ v)+∑ t,(X t ⬝ᵥ v)^2 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp only [herr,add_sub_cancel_left] at hm
  rw [hsum,add_div,sub_div,mul_div_assoc] at hm
  have hqeq : (∑ t,(X t ⬝ᵥ v)^2)/(n : ℝ) = q := (lb_cov_quad X v).symm
  change _ ≤ _ at hm
  rw [hqeq] at hm
  change (∑ t,E t^2)/(n : ℝ)-2*R+q+lam*l1Norm b ≤ (∑ t,E t^2)/(n : ℝ)+lam*l1Norm β at hm
  have hp := mul_le_mul_of_nonneg_left hpen hlam.le
  have hbasic : q+lam/2*L ≤ 2*lam*U := by nlinarith
  have hcone : V ≤ 3*U := by nlinarith
  have hcomp := hcompat.2 v hcone
  rw [hs0] at hcomp
  have hcomp' : φ^2*U^2 ≤ (s0 : ℝ)*q := by
    rw [le_div_iff₀ (sq_pos_of_pos hφ)] at hcomp
    nlinarith
  exact lb_oracle_numeric q U V L s0 φ lam hs' hφ hlam hq hU hV hL hbasic hcomp'

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix ConfBallMatrix
namespace BastaniBayati.LassoBandit

lemma lb_cov_quad_general {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (sampleCov X *ᵥ v) = (∑ t,(X t ⬝ᵥ v)^2)/(Fintype.card ι : ℝ) := by
  have hm : sampleCov X = (Fintype.card ι : ℝ)⁻¹ • ∑ t,vecMulVec (X t) (X t) := by
    ext i j
    simp [sampleCov,Matrix.smul_apply,Matrix.sum_apply,vecMulVec_apply,div_eq_mul_inv,mul_comm]
  rw [hm,smul_mulVec,sum_mulVec,dotProduct_smul,dotProduct_sum]
  simp only [smul_eq_mul]
  have he : ∀ t,v ⬝ᵥ (vecMulVec (X t) (X t) *ᵥ v) = (X t ⬝ᵥ v)^2 := by
    intro t
    rw [e5_vecMulVec_mulVec,dotProduct_smul,dotProduct_comm]
    simp [smul_eq_mul,pow_two]
  simp only [he]
  ring


lemma lb_cross_eq_general {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (E : ι → ℝ) (v : Fin d → ℝ) :
    (∑ t,E t*(X t ⬝ᵥ v))/(Fintype.card ι : ℝ) =
      ∑ j,((∑ t,E t*X t j)/(Fintype.card ι : ℝ))*v j := by
  simp_rw [dotProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,div_mul_eq_mul_div,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring


lemma lb_lasso_oracle_general {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (E : ι → ℝ)
    (β b : Fin d → ℝ) (s0 : ℕ) (φ lam : ℝ) (hn : 1 ≤ Fintype.card ι)
    (hs0 : (supp β).card=s0) (hs : 1 ≤ s0) (hφ : 0 < φ) (hlam : 0 < lam)
    (hmin : IsLassoMinimizer X (fun t => X t ⬝ᵥ β+E t) lam b)
    (hnoise : ∀ j,|(∑ t,E t*X t j)/(Fintype.card ι : ℝ)| ≤ lam/4)
    (hcompat : sampleCov X ∈ compatSet (supp β) φ) :
    l1Norm (b-β) ≤ 4*s0*lam/φ^2 := by
  classical
  let v := b-β
  let q := v ⬝ᵥ (sampleCov X *ᵥ v)
  let R := (∑ t,E t*(X t ⬝ᵥ v))/(Fintype.card ι : ℝ)
  let U := l1Norm (restrictTo (supp β) v)
  let V := l1Norm (restrictTo (supp β)ᶜ v)
  let L := l1Norm v
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hs
  have hq : 0 ≤ q := by simpa [q] using hcompat.1.dotProduct_mulVec_nonneg v
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hL : L=U+V := lb_l1_split (supp β) v
  have hR : R ≤ lam/4*L := by
    dsimp [R]
    rw [lb_cross_eq_general]
    dsimp [L,l1Norm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc _ ≤ |((∑ t,E t*X t j)/(Fintype.card ι : ℝ))*v j| := le_abs_self _
      _ = |(∑ t,E t*X t j)/(Fintype.card ι : ℝ)| * |v j| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hnoise j) (abs_nonneg _)
  have hpen : l1Norm β-l1Norm b ≤ U-V := lb_l1_difference β b
  have hm := hmin β
  unfold lassoObjective at hm
  have herr : ∀ t,X t ⬝ᵥ β+E t-X t ⬝ᵥ b = E t-X t ⬝ᵥ v := by
    intro t
    dsimp [v]
    rw [dotProduct_sub]
    ring
  have hsum : ∑ t,(E t-X t ⬝ᵥ v)^2 =
      ∑ t,E t^2-2*∑ t,E t*(X t ⬝ᵥ v)+∑ t,(X t ⬝ᵥ v)^2 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp only [herr,add_sub_cancel_left] at hm
  rw [hsum,add_div,sub_div,mul_div_assoc] at hm
  have hqeq : (∑ t,(X t ⬝ᵥ v)^2)/(Fintype.card ι : ℝ) = q := (lb_cov_quad_general X v).symm
  change _ ≤ _ at hm
  rw [hqeq] at hm
  change (∑ t,E t^2)/(Fintype.card ι : ℝ)-2*R+q+lam*l1Norm b ≤ (∑ t,E t^2)/(Fintype.card ι : ℝ)+lam*l1Norm β at hm
  have hp := mul_le_mul_of_nonneg_left hpen hlam.le
  have hbasic : q+lam/2*L ≤ 2*lam*U := by nlinarith
  have hcone : V ≤ 3*U := by nlinarith
  have hcomp := hcompat.2 v hcone
  rw [hs0] at hcomp
  have hcomp' : φ^2*U^2 ≤ (s0 : ℝ)*q := by
    rw [le_div_iff₀ (sq_pos_of_pos hφ)] at hcomp
    nlinarith
  exact lb_oracle_numeric q U V L s0 φ lam hs' hφ hlam hq hU hV hL hbasic hcomp'


end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
namespace BastaniBayati.LassoBandit

lemma lb_sample_cov_psd {ι : Type*} [Fintype ι] {d : ℕ} (Z : ι → Fin d → ℝ) :
    (sampleCov Z).PosSemidef := by
  classical
  have he : sampleCov Z = (Fintype.card ι : ℝ)⁻¹ • ∑ t,vecMulVec (Z t) (Z t) := by
    ext i j
    simp [sampleCov,Matrix.smul_apply,Matrix.sum_apply,vecMulVec_apply,div_eq_mul_inv,mul_comm]
  rw [he]
  apply Matrix.PosSemidef.smul _ (by positivity)
  apply Matrix.posSemidef_sum
  intro t _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (Z t)

lemma lb_quad_entry_bound {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (δ : ℝ) (hb : ∀ i j,|M i j-N i j| ≤ δ) :
    |v ⬝ᵥ ((M-N) *ᵥ v)| ≤ δ*(l1Norm v)^2 := by
  classical
  simp only [dotProduct,mulVec,Matrix.sub_apply,Finset.mul_sum]
  calc |∑ i,∑ j,v i*((M i j-N i j)*v j)| ≤
        ∑ i,|∑ j,v i*((M i j-N i j)*v j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,∑ j,|v i| *δ*|v j| := by
      apply Finset.sum_le_sum
      intro i _
      calc _ ≤ ∑ j,|v i*((M i j-N i j)*v j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          simp only [abs_mul]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hb i j) (abs_nonneg (v j))) (abs_nonneg (v i))
    _ = _ := by
      simp only [←Finset.mul_sum,←Finset.sum_mul,l1Norm]
      ring

lemma lb_compat_perturb {d : ℕ} (I : Finset (Fin d)) (s : ℕ)
    (M N : Matrix (Fin d) (Fin d) ℝ) (φ δ : ℝ)
    (hs : I.card=s) (hspos : 1 ≤ s) (hφ : 0 < φ) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ φ^2/(32*s)) (hM : M.PosSemidef)
    (hN : N ∈ compatSet I φ) (hb : ∀ i j,|N i j-M i j| ≤ δ) :
    M ∈ compatSet I (φ/Real.sqrt 2) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hspos
  have hφsq : (φ/Real.sqrt 2)^2 = φ^2/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨hM,?_⟩
  intro v hcone
  let U := l1Norm (restrictTo I v)
  let V := l1Norm (restrictTo Iᶜ v)
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hL : l1Norm v=U+V := lb_l1_split I v
  have hLsq : (l1Norm v)^2 ≤ 16*U^2 := by
    change V ≤ 3*U at hcone
    nlinarith
  have hc := hN.2 v hcone
  rw [hs,le_div_iff₀ (sq_pos_of_pos hφ)] at hc
  have herr := lb_quad_entry_bound N M v δ hb
  rw [Matrix.sub_mulVec,dotProduct_sub] at herr
  have he : v ⬝ᵥ (N *ᵥ v)-v ⬝ᵥ (M *ᵥ v) ≤ δ*16*U^2 := by
    exact (le_abs_self _).trans (herr.trans (by nlinarith))
  have hd : δ*(32*s) ≤ φ^2 := (le_div_iff₀ (by positivity)).mp hsmall
  have hdU := mul_le_mul_of_nonneg_right hd (sq_nonneg U)
  have heS := mul_le_mul_of_nonneg_left he hs'.le
  rw [hs,hφsq,le_div_iff₀ (by positivity)]
  change U^2*(φ^2/2) ≤ (s : ℝ)*(v ⬝ᵥ (M *ᵥ v))
  nlinarith

lemma lb_compat_dominate {d : ℕ} (I : Finset (Fin d))
    (M N : Matrix (Fin d) (Fin d) ℝ) (φ p : ℝ) (hφ : 0 < φ) (hp : 0 < p)
    (hM : M.PosSemidef) (hN : N ∈ compatSet I (φ/Real.sqrt 2))
    (hdom : ∀ v : Fin d → ℝ,p/2*(v ⬝ᵥ (N *ᵥ v)) ≤ v ⬝ᵥ (M *ᵥ v)) :
    M ∈ compatSet I (φ*Real.sqrt p/2) := by
  have ha : (φ/Real.sqrt 2)^2 = φ^2/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hb : (φ*Real.sqrt p/2)^2 = φ^2*p/4 := by
    rw [div_pow,mul_pow,Real.sq_sqrt hp.le]
    norm_num
  refine ⟨hM,?_⟩
  intro v hcone
  have hc := hN.2 v hcone
  rw [ha,le_div_iff₀ (by positivity)] at hc
  have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ p/2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hdom v) (Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)
  rw [hb,le_div_iff₀ (by positivity)]
  nlinarith

lemma lb_sample_cov_subset {d : ℕ} (Z : ℕ → Fin d → ℝ) (A B : Finset ℕ)
    (hBA : B ⊆ A) (hA : A.Nonempty) (hB : B.Nonempty) (v : Fin d → ℝ) :
    ((B.card : ℝ)/A.card)*(v ⬝ᵥ (sampleCov (fun t : B => Z t) *ᵥ v)) ≤
      v ⬝ᵥ (sampleCov (fun t : A => Z t) *ᵥ v) := by
  have hn : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hm : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  rw [lb_cov_quad_general,lb_cov_quad_general]
  simp only [Fintype.card_coe]
  rw [Finset.sum_coe_sort B (fun t => (Z t ⬝ᵥ v)^2),Finset.sum_coe_sort A (fun t => (Z t ⬝ᵥ v)^2)]
  have hsum : (∑ t ∈ B,(Z t ⬝ᵥ v)^2) ≤ ∑ t ∈ A,(Z t ⬝ᵥ v)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hBA (fun _ _ _ => sq_nonneg _)
  field_simp
  nlinarith

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
namespace BastaniBayati.LassoBandit

lemma lb_compat_perturb_sparse {d : ℕ} (I : Finset (Fin d)) (s : ℕ)
    (M N : Matrix (Fin d) (Fin d) ℝ) (φ δ : ℝ)
    (hs : I.card ≤ s) (hspos : 1 ≤ s) (hφ : 0 < φ) (hδ : 0 ≤ δ)
    (hsmall : δ ≤ φ^2/(32*s)) (hM : M.PosSemidef)
    (hN : N ∈ compatSet I φ) (hb : ∀ i j,|N i j-M i j| ≤ δ) :
    M ∈ compatSet I (φ/Real.sqrt 2) := by
  by_cases hI : I.card=0
  · have he : I=∅ := Finset.card_eq_zero.mp hI
    refine ⟨hM,?_⟩
    intro v _
    simp [he,l1Norm,restrictTo]
  · have hpos : 1 ≤ I.card := by omega
    have hs' : (0 : ℝ) < s := by exact_mod_cast hspos
    have hI' : (0 : ℝ) < I.card := by exact_mod_cast hpos
    have hcard : (I.card : ℝ) ≤ s := by exact_mod_cast hs
    have hd := (le_div_iff₀ (show (0 : ℝ) < 32*s by positivity)).mp hsmall
    have hc := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 32*δ by positivity)
    have hsmall' : δ ≤ φ^2/(32*I.card) := by rw [le_div_iff₀ (by positivity)];nlinarith
    exact lb_compat_perturb I I.card M N φ δ rfl hpos hφ hδ hsmall' hM hN hb

lemma lb_compat_smul {d : ℕ} (I : Finset (Fin d)) (N : Matrix (Fin d) (Fin d) ℝ)
    (φ r : ℝ) (hφ : 0 < φ) (hr : 0 < r) (hN : N ∈ compatSet I φ) :
    r • N ∈ compatSet I (φ*Real.sqrt r) := by
  refine ⟨hN.1.smul hr.le,?_⟩
  intro v hcone
  have hc := hN.2 v hcone
  rw [le_div_iff₀ (sq_pos_of_pos hφ)] at hc
  have ht := mul_le_mul_of_nonneg_left hc hr.le
  rw [mul_pow,Real.sq_sqrt hr.le,le_div_iff₀ (by positivity),smul_mulVec,dotProduct_smul]
  simp only [smul_eq_mul]
  nlinarith

lemma lb_compat_smaller {d : ℕ} (I : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 ≤ b^2)
    (hM : M ∈ compatSet I b) : M ∈ compatSet I a := by
  refine ⟨hM.1,?_⟩
  intro v hcone
  have hc := hM.2 v hcone
  rw [le_div_iff₀ (sq_pos_of_pos hb)] at hc
  rw [le_div_iff₀ (sq_pos_of_pos ha)]
  exact (mul_le_mul_of_nonneg_left hab (sq_nonneg _)).trans hc

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_masked_covariance_entry_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (Z : ι → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ)) (hU : MeasurableSet U)
    (xmax u : ℝ) (hn : 0 < Fintype.card ι) (hx : 0 < xmax)
    (hr : 0 < PZ.real U) (hu : 0 < u) (huSmall : u ≤ 1/2)
    (hZ : ∀ t,Measurable (Z t)) (hiid : iIndepFun Z P)
    (hlaw : ∀ t,P.map (Z t)=PZ) (hb : ∀ t ω,‖Z t ω‖ ≤ xmax) (a b : Fin d) :
    P {ω | 2*PZ.real U*xmax^2*u <
      |sampleCov (fun t => U.indicator id (Z t ω)) a b-∫ z in U,z a*z b ∂PZ|} ≤
      ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*PZ.real U*u^2)) := by
  classical
  let g : (Fin d → ℝ) → ℝ := U.indicator (fun z => z a*z b)
  let V : ι → Ω → ℝ := fun t => g ∘ Z t
  let m := ∫ z,g z ∂PZ
  let W : ι → Ω → ℝ := fun t ω => V t ω-m
  have hg : Measurable g := ((measurable_pi_apply a).mul (measurable_pi_apply b)).indicator hU
  have hproduct : ∀ t ω,|Z t ω a*Z t ω b| ≤ xmax^2 := by
    intro t ω
    have ha := (show |Z t ω a| ≤ ‖Z t ω‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Z t ω) a).trans (hb t ω)
    have hb' := (show |Z t ω b| ≤ ‖Z t ω‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Z t ω) b).trans (hb t ω)
    rw [abs_mul,pow_two]
    exact mul_le_mul ha hb' (abs_nonneg _) hx.le
  have hmean : ∀ t,∫ ω,V t ω ∂P=m := by
    intro t
    dsimp [V,m]
    rw [←hlaw t,integral_map (hZ t).aemeasurable hg.aestronglyMeasurable]
  have hprob : ∀ t,P.real (Z t ⁻¹' U)=PZ.real U := by
    intro t
    rw [measureReal_def,←Measure.map_apply (hZ t) hU,hlaw t]
    rfl
  have hmoment := fun t => lb_indicator_centered_moments P (Z t ⁻¹' U)
    (hU.preimage (hZ t)) (fun ω => Z t ω a*Z t ω b) (xmax^2) (sq_nonneg _)
    (((measurable_pi_apply a).comp (hZ t)).mul ((measurable_pi_apply b).comp (hZ t)))
    (hproduct t)
  have heq : ∀ t,(Z t ⁻¹' U).indicator (fun ω => Z t ω a*Z t ω b)=V t := by
    intro t
    funext ω
    by_cases h : Z t ω ∈ U <;> simp [V,g,h]
  have hmom : ∀ t,Measurable (W t) ∧ (∀ ω,|W t ω| ≤ 2*xmax^2) ∧
      (∫ ω,W t ω ∂P)=0 ∧ (∫ ω,(W t ω)^2 ∂P) ≤ PZ.real U*(xmax^2)^2 := by
    intro t
    have hh := hmoment t
    dsimp only at hh
    rw [heq t,hmean t,hprob t] at hh
    exact hh
  have hind : iIndepFun W P := by
    have hh := hiid.comp (fun _ z => g z-m) (fun _ => hg.sub_const m)
    exact hh
  have ht := lb_iid_rare_variance_tail P W (xmax^2) (PZ.real U) u hn (by positivity)
    hr hu huSmall (fun t => (hmom t).1) hind (fun t => (hmom t).2.1)
    (fun t => (hmom t).2.2.1) (fun t => (hmom t).2.2.2)
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have havg : ∀ ω,(∑ t,W t ω)/(Fintype.card ι : ℝ)=
      sampleCov (fun t => U.indicator id (Z t ω)) a b-∫ z in U,z a*z b ∂PZ := by
    intro ω
    have hprod : ∀ t,U.indicator id (Z t ω) a*U.indicator id (Z t ω) b=V t ω := by
      intro t
      by_cases h : Z t ω ∈ U <;> simp [V,g,h]
    simp only [sampleCov,hprod,W,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul]
    rw [sub_div,mul_div_cancel_left₀ m hn']
    simp only [m,g,integral_indicator hU]
  simpa only [havg] using ht

lemma lb_masked_covariance_max_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (Z : ι → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ)) (hU : MeasurableSet U)
    (xmax u : ℝ) (hn : 0 < Fintype.card ι) (hx : 0 < xmax)
    (hr : 0 < PZ.real U) (hu : 0 < u) (huSmall : u ≤ 1/2)
    (hZ : ∀ t,Measurable (Z t)) (hiid : iIndepFun Z P)
    (hlaw : ∀ t,P.map (Z t)=PZ) (hb : ∀ t ω,‖Z t ω‖ ≤ xmax) :
    P {ω | ∃ a b : Fin d,2*PZ.real U*xmax^2*u <
      |sampleCov (fun t => U.indicator id (Z t ω)) a b-∫ z in U,z a*z b ∂PZ|} ≤
      ENNReal.ofReal (2*(d : ℝ)^2*Real.exp (-(Fintype.card ι : ℝ)*PZ.real U*u^2)) := by
  classical
  let A : Fin d × Fin d → Set Ω := fun ab => {ω | 2*PZ.real U*xmax^2*u <
    |sampleCov (fun t => U.indicator id (Z t ω)) ab.1 ab.2-∫ z in U,z ab.1*z ab.2 ∂PZ|}
  have hA := fun (ab : Fin d × Fin d) => lb_masked_covariance_entry_tail P Z PZ U hU xmax u hn hx hr
    hu huSmall hZ hiid hlaw hb ab.1 ab.2
  have hsub : {ω | ∃ a b : Fin d,2*PZ.real U*xmax^2*u <
      |sampleCov (fun t => U.indicator id (Z t ω)) a b-∫ z in U,z a*z b ∂PZ|} ⊆ ⋃ ab,A ab := by
    rintro ω ⟨a,b,h⟩
    exact Set.mem_iUnion.mpr ⟨(a,b),h⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ ab,P (A ab) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ab : Fin d × Fin d,ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*PZ.real U*u^2)) :=
      Finset.sum_le_sum (fun ab _ => hA ab)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
        ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_optRegion_measurable {d K : ℕ} (𝒳 : Set (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (h : ℝ) (i : Fin K) (hX : MeasurableSet 𝒳) :
    MeasurableSet (optRegion 𝒳 β h i) := by
  classical
  have hdot : ∀ j : Fin K,Measurable (fun x : Fin d → ℝ => x ⬝ᵥ β j) := by
    intro j
    unfold dotProduct
    fun_prop
  have hmax : Measurable (fun x => maxOther β x i) :=
    Measurable.iSup (fun j : {j : Fin K // j ≠ i} => hdot j)
  exact hX.inter (measurableSet_lt (hmax.add_const h) (hdot i))

lemma lb_compat_quad_dominate {d : ℕ} (I : Finset (Fin d))
    (M N : Matrix (Fin d) (Fin d) ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hM : M.PosSemidef) (hN : N ∈ compatSet I φ)
    (hdom : ∀ v,v ⬝ᵥ (N *ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)) : M ∈ compatSet I φ := by
  refine ⟨hM,?_⟩
  intro v hcone
  exact (hN.2 v hcone).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hdom v) (Nat.cast_nonneg _)) (sq_nonneg φ))

lemma lb_masked_cov_quad_le {ι : Type*} [Fintype ι] {d : ℕ}
    (Z : ι → Fin d → ℝ) (U : Set (Fin d → ℝ)) (v : Fin d → ℝ) :
    v ⬝ᵥ (sampleCov (fun t => U.indicator id (Z t)) *ᵥ v) ≤ v ⬝ᵥ (sampleCov Z *ᵥ v) := by
  classical
  rw [lb_cov_quad_general,lb_cov_quad_general]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro t _
  by_cases h : Z t ∈ U
  · simp only [Set.indicator_of_mem h,id_eq]
    exact le_rfl
  · simpa only [Set.indicator_of_notMem h,zero_dotProduct,zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (Z t ⬝ᵥ v)

lemma lb_masked_compatibility {ι : Type*} [Fintype ι] {d : ℕ}
    (Z : ι → Fin d → ℝ) (PZ : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ))
    (I : Finset (Fin d)) (s0 : ℕ) (xmax φ p : ℝ)
    (hs : I.card ≤ s0) (hspos : 1 ≤ s0) (hx : 0 < xmax) (hφ : 0 < φ)
    (hp : 0 < p) (hpr : p ≤ PZ.real U)
    (hSigma : condSecondMoment PZ U ∈ compatSet I φ)
    (hentry : ∀ a b,|sampleCov (fun t => U.indicator id (Z t)) a b-
      ∫ z in U,z a*z b ∂PZ| ≤ 2*PZ.real U*xmax^2*C2 s0 xmax φ) :
    sampleCov Z ∈ compatSet I (φ*Real.sqrt p/2) := by
  classical
  let r := PZ.real U
  let c := C2 s0 xmax φ
  let δ := 2*r*xmax^2*c
  let N : Matrix (Fin d) (Fin d) ℝ := fun a b => ∫ z in U,z a*z b ∂PZ
  let M := sampleCov (fun t => U.indicator id (Z t))
  have hr : 0 < r := hp.trans_le hpr
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hspos
  have hc : 0 < c := by dsimp [c,C2];apply lt_min <;> positivity
  have hN : N=r • condSecondMoment PZ U := by
    ext a b
    simp only [N,Matrix.smul_apply,smul_eq_mul,condSecondMoment]
    change _=r*(_/r)
    field_simp
  have hcompat := lb_compat_smul I (condSecondMoment PZ U) φ r hφ hr hSigma
  rw [←hN] at hcompat
  have hsmall : δ ≤ (φ*Real.sqrt r)^2/(32*s0) := by
    have hh : c ≤ φ^2/(256*s0*xmax^2) := min_le_right _ _
    have hh' := (le_div_iff₀ (show (0 : ℝ) < 256*s0*xmax^2 by positivity)).mp hh
    have hscaled := mul_le_mul_of_nonneg_left hh' hr.le
    rw [mul_pow,Real.sq_sqrt hr.le,le_div_iff₀ (by positivity)]
    dsimp [δ]
    nlinarith
  have hpert := lb_compat_perturb_sparse I s0 M N (φ*Real.sqrt r) δ hs hspos
    (by positivity) (by dsimp [δ];positivity) hsmall (lb_sample_cov_psd _) hcompat (by
      intro a b
      rw [abs_sub_comm]
      exact hentry a b)
  have hab : (φ*Real.sqrt p/2)^2 ≤ (φ*Real.sqrt r/Real.sqrt 2)^2 := by
    rw [div_pow,div_pow,mul_pow,mul_pow,Real.sq_sqrt hp.le,Real.sq_sqrt hr.le,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_left hpr (sq_nonneg φ)
    nlinarith [sq_nonneg φ]
  have hweak := lb_compat_smaller I M (φ*Real.sqrt p/2) (φ*Real.sqrt r/Real.sqrt 2)
    (by positivity) (by positivity) hab hpert
  exact lb_compat_quad_dominate I (sampleCov Z) M (φ*Real.sqrt p/2) (by positivity)
    (lb_sample_cov_psd _) hweak (lb_masked_cov_quad_le Z U)

lemma lb_masked_compatibility_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (Z : ι → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (U : Set (Fin d → ℝ)) (hU : MeasurableSet U)
    (I : Finset (Fin d)) (s0 : ℕ) (xmax φ p : ℝ)
    (hn : 0 < Fintype.card ι) (hs : I.card ≤ s0) (hspos : 1 ≤ s0)
    (hx : 0 < xmax) (hφ : 0 < φ) (hp : 0 < p) (hpr : p ≤ PZ.real U)
    (hSigma : condSecondMoment PZ U ∈ compatSet I φ)
    (hZ : ∀ t,Measurable (Z t)) (hiid : iIndepFun Z P)
    (hlaw : ∀ t,P.map (Z t)=PZ) (hb : ∀ t ω,‖Z t ω‖ ≤ xmax) :
    P {ω | sampleCov (fun t => Z t ω) ∉ compatSet I (φ*Real.sqrt p/2)} ≤
      ENNReal.ofReal (2*(d : ℝ)^2*Real.exp (-(Fintype.card ι : ℝ)*p*C2 s0 xmax φ^2)) := by
  classical
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hspos
  have hc : 0 < C2 s0 xmax φ := by unfold C2;apply lt_min <;> positivity
  have hsub : {ω | sampleCov (fun t => Z t ω) ∉ compatSet I (φ*Real.sqrt p/2)} ⊆
      {ω | ∃ a b : Fin d,2*PZ.real U*xmax^2*C2 s0 xmax φ <
        |sampleCov (fun t => U.indicator id (Z t ω)) a b-∫ z in U,z a*z b ∂PZ|} := by
    intro ω hω
    by_contra hnot
    apply hω
    apply lb_masked_compatibility (fun t => Z t ω) PZ U I s0 xmax φ p hs hspos hx hφ hp hpr hSigma
    intro a b
    exact le_of_not_gt (fun h => hnot ⟨a,b,h⟩)
  have ht := lb_masked_covariance_max_tail P Z PZ U hU xmax (C2 s0 xmax φ) hn hx
    (hp.trans_le hpr) hc (min_le_left _ _) hZ hiid hlaw hb
  exact (measure_mono hsub).trans (ht.trans (ENNReal.ofReal_le_ofReal (by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hpr
      (show 0 ≤ (Fintype.card ι : ℝ)*C2 s0 xmax φ^2 by positivity)
    nlinarith)))

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BastaniBayati.LassoBandit

lemma lb_forced_count_levels {K q : ℕ} (i : Fin K) (L t : ℕ)
    (hL : 1 ≤ L) (hpow : 2^(L-1)*K*q ≤ t) :
    L*q ≤ (forcedUpTo K q i t).card := by
  classical
  let f : Fin L × Fin q → ℕ := fun nk => (2^nk.1.val-1)*K*q+q*i.val+(nk.2.val+1)
  have htime : ∀ nk : Fin L × Fin q,f nk ≤ 2^nk.1.val*K*q := by
    intro nk
    have hp : 1 ≤ 2^nk.1.val := Nat.one_le_pow _ _ (by omega)
    have hi : q*(i.val+1) ≤ q*K := Nat.mul_le_mul_left q (by omega)
    have he : (2^nk.1.val-1)*K*q+K*q=2^nk.1.val*K*q := by
      have he' : (2^nk.1.val-1)+1=2^nk.1.val := by omega
      calc _ = ((2^nk.1.val-1)+1)*K*q := by ring
        _ = _ := by rw [he']
    dsimp [f]
    nlinarith [nk.2.isLt]
  have hordered : ∀ nk ml : Fin L × Fin q,nk.1.val < ml.1.val → f nk < f ml := by
    intro nk ml hnm
    have hp : 2^nk.1.val < 2^ml.1.val := Nat.pow_lt_pow_right (by omega : 1 < 2) hnm
    have hp' : 2^nk.1.val ≤ 2^ml.1.val-1 := by omega
    have hm := Nat.mul_le_mul_right q (Nat.mul_le_mul_right K hp')
    have ht := htime nk
    dsimp [f] at ht ⊢
    omega
  have hf : ∀ nk : Fin L × Fin q,f nk ∈ forcedUpTo K q i t := by
    intro nk
    have hp : 2^nk.1.val ≤ 2^(L-1) := Nat.pow_le_pow_right (by omega) (by omega)
    have ht := (htime nk).trans ((Nat.mul_le_mul_right q (Nat.mul_le_mul_right K hp)).trans hpow)
    have h1 : 1 ≤ f nk := by dsimp [f];omega
    have hs : f nk ∈ forcedSet K q i := by
      refine ⟨nk.1.val,q*i.val+nk.2.val+1,?_,?_,?_⟩
      · omega
      · nlinarith [nk.2.isLt]
      · dsimp [f];omega
    simpa only [forcedUpTo,Finset.mem_filter,Finset.mem_Icc] using And.intro ⟨h1,ht⟩ hs
  let g : Fin L × Fin q → ↥(forcedUpTo K q i t) := fun nk => ⟨f nk,hf nk⟩
  have hg : Function.Injective g := by
    intro nk ml he
    have he' : f nk=f ml := congrArg Subtype.val he
    have hn : nk.1=ml.1 := by
      apply Fin.ext
      rcases lt_trichotomy nk.1.val ml.1.val with h | h | h
      · have := hordered nk ml h;omega
      · exact h
      · have := hordered ml nk h;omega
    have hk : nk.2=ml.2 := by apply Fin.ext;dsimp [f] at he';rw [hn] at he';omega
    exact Prod.ext hn hk
  have hh := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using hh

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BastaniBayati.LassoBandit

lemma lb_forced_log_count {K q : ℕ} (i : Fin K) (t : ℕ) (hK : 0 < K) (hq : 0 < q)
    (ht : (K*q)^2 ≤ t) :
    (q : ℝ)/2*Real.log t ≤ (forcedUpTo K q i t).card := by
  let a := K*q
  let L := Nat.log 2 (t/a)+1
  have ha : 0 < a := Nat.mul_pos hK hq
  have hat : a ≤ t := (Nat.le_self_pow (by omega) a).trans ht
  have hquot : 0 < t/a := Nat.div_pos hat ha
  have hL : 1 ≤ L := by dsimp [L];omega
  have hp : 2^(L-1)*a ≤ t := by
    have hh := Nat.pow_log_le_self 2 (Nat.ne_of_gt hquot)
    have hmul := Nat.mul_le_mul_right a hh
    dsimp [L]
    simpa only [Nat.add_sub_cancel] using hmul.trans (Nat.div_mul_le_self t a)
  have hcount := lb_forced_count_levels i L t hL (by simpa only [a,mul_assoc] using hp)
  have hupper : t < 2^L*a := by
    have hh := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (t/a)
    exact (Nat.div_lt_iff_lt_mul ha).mp hh
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ht' : (0 : ℝ) < t := by exact_mod_cast ha.trans_le hat
  have hut : (t : ℝ) < (2 : ℝ)^L*a := by exact_mod_cast hupper
  have hlow : (a : ℝ)^2 ≤ t := by exact_mod_cast ht
  have hlower := Real.log_le_log (show (0 : ℝ) < (a : ℝ)^2 by positivity) hlow
  rw [Real.log_pow] at hlower
  have hlog := Real.log_lt_log ht' hut
  rw [Real.log_mul (by positivity) ha'.ne',Real.log_pow] at hlog
  have h2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hL' : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hLL := mul_le_mul_of_nonneg_left h2 hL'
  norm_num at hlower
  simp only [mul_one] at hLL
  have hh : Real.log t/2 ≤ (L : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hc : (L : ℝ)*q ≤ (forcedUpTo K q i t).card := by exact_mod_cast hcount
  nlinarith

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace BastaniBayati.LassoBandit

lemma lb_q0_numeric (d : ℕ) (x h p c1 c2 : ℝ) (q : ℕ)
    (hx : 0 < x) (hh : 0 < h) (hp : 0 < p) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hq : 4*⌈q0 d x h p c1 c2⌉₊ ≤ q) :
    0 < q ∧ 80 ≤ (q : ℝ)*p ∧ 16 ≤ (q : ℝ)*p*c2^2 ∧
      48*Real.log d ≤ (q : ℝ)*p*c2^2 ∧
      16*Real.log d ≤ (q : ℝ)*(h^2*p^2*c1/(256*x^2)) := by
  have hq' : 4*q0 d x h p c1 c2 ≤ (q : ℝ) := by
    have hc := Nat.le_ceil (q0 d x h p c1 c2)
    have hcast : 4*(⌈q0 d x h p c1 c2⌉₊ : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have ha : 20/p ≤ q0 d x h p c1 c2 := (le_max_left _ _).trans (le_max_left _ _)
  have hb : 4/(p*c2^2) ≤ q0 d x h p c1 c2 := (le_max_right _ _).trans (le_max_left _ _)
  have hc : 12*Real.log d/(p*c2^2) ≤ q0 d x h p c1 c2 := (le_max_left _ _).trans (le_max_right _ _)
  have hd : 1024*x^2*Real.log d/(h^2*p^2*c1) ≤ q0 d x h p c1 c2 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hqa : 80 ≤ (q : ℝ)*p := by
    have hh : 20/p ≤ (q : ℝ)/4 := by linarith
    have hd := (div_le_iff₀ hp).mp hh
    nlinarith
  have hqb : 16 ≤ (q : ℝ)*p*c2^2 := by
    have hh : 4/(p*c2^2) ≤ (q : ℝ)/4 := by linarith
    have hd := (div_le_iff₀ (show 0 < p*c2^2 by positivity)).mp hh
    nlinarith
  have hqc : 48*Real.log d ≤ (q : ℝ)*p*c2^2 := by
    have hh : 12*Real.log d/(p*c2^2) ≤ (q : ℝ)/4 := by linarith
    have hd := (div_le_iff₀ (show 0 < p*c2^2 by positivity)).mp hh
    nlinarith
  have hqd : 16*Real.log d ≤ (q : ℝ)*(h^2*p^2*c1/(256*x^2)) := by
    have hh' : 1024*x^2*Real.log d/(h^2*p^2*c1) ≤ (q : ℝ)/4 := by linarith
    have hd' := (div_le_iff₀ (show 0 < h^2*p^2*c1 by positivity)).mp hh'
    rw [←mul_div_assoc,le_div_iff₀ (by positivity)]
    nlinarith
  have hpos : (0 : ℝ) < q := by nlinarith
  exact ⟨by exact_mod_cast hpos,hqa,hqb,hqc,hqd⟩

lemma lb_log_ge_one {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hn')

lemma lb_exp_log_inverse_four (t : ℝ) (ht : 0 < t) :
    Real.exp (-(4*Real.log t))=1/t^4 := by
  rw [Real.exp_neg]
  have he : Real.exp (4*Real.log t)=t^4 := by
    have hh : Real.log (t^4)=4*Real.log t := by rw [Real.log_pow];norm_num
    rw [←hh,Real.exp_log (by positivity)]
  rw [he,one_div]

lemma lb_forced_covariance_numeric (d : ℕ) (N q p c t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (hp : 0 < p) (hc : 0 < c)
    (hlogt : 1 ≤ Real.log t) (hN : q/2*Real.log t ≤ N)
    (hq1 : 16 ≤ q*p*c^2) (hq2 : 48*Real.log d ≤ q*p*c^2) :
    2*(d : ℝ)^2*Real.exp (-N*p*c^2) ≤ 2/t^4 := by
  have hld : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hn := mul_le_mul_of_nonneg_right hN (show 0 ≤ p*c^2 by positivity)
  have h1 := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ Real.log t by linarith)
  have h2 := mul_le_mul_of_nonneg_right hq2 (show 0 ≤ Real.log t by linarith)
  have h3 := mul_le_mul_of_nonneg_left hlogt hld
  have hexp : 2*Real.log d+4*Real.log t ≤ N*p*c^2 := by nlinarith
  have he : (d : ℝ)^2=Real.exp (2*Real.log d) := by
    have hh : Real.log ((d : ℝ)^2)=2*Real.log d := by rw [Real.log_pow];norm_num
    rw [←hh,Real.exp_log (by positivity)]
  calc _ = 2*Real.exp (2*Real.log d-N*p*c^2) := by rw [he,mul_assoc,←Real.exp_add];congr 2;ring
    _ ≤ 2*Real.exp (-(4*Real.log t)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [lb_exp_log_inverse_four t ht];ring

lemma lb_forced_noise_numeric (d : ℕ) (N q rate t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (hrate : 0 < rate)
    (hlogd : 1 ≤ Real.log d) (hlogt : 1 ≤ Real.log t)
    (hN : q/2*Real.log t ≤ N) (hq : 16*Real.log d ≤ q*rate) :
    2*d*Real.exp (-N*rate) ≤ 2/t^4 := by
  have hn := mul_le_mul_of_nonneg_right hN hrate.le
  have h1 := mul_le_mul_of_nonneg_right hq (show 0 ≤ Real.log t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hlogd (show 0 ≤ Real.log t by linarith)
  have h3 := mul_le_mul_of_nonneg_left hlogt (show 0 ≤ Real.log d by linarith)
  have hexp : Real.log d+4*Real.log t ≤ N*rate := by nlinarith
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  calc _ = 2*Real.exp (Real.log d)*Real.exp (-N*rate) := by rw [Real.exp_log hd']
    _ = 2*Real.exp (Real.log d-N*rate) := by rw [mul_assoc,←Real.exp_add];congr 2;ring
    _ ≤ 2*Real.exp (-(4*Real.log t)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [lb_exp_log_inverse_four t ht];ring

end BastaniBayati.LassoBandit

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BastaniBayati.LassoBandit

lemma lb_model_finite {Ω ι : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 : Set (Fin d → ℝ))
    (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0)
    (hm : IsCovariateNoiseModel P 𝒳 PX X ε σ) (f : ι → ℕ)
    (hf : Function.Injective f) (hpos : ∀ t,1 ≤ f t) (i : Fin K) :
    iIndepFun (fun t => X (f t)) P ∧ iIndepFun (fun t => ε i (f t)) P ∧
      IndepFun (fun ω t => X (f t) ω) (fun ω t => ε i (f t) ω) P := by
  have htime : ∀ t,f t-1+1=f t := fun t => Nat.sub_add_cancel (hpos t)
  have hinj : Function.Injective (fun t => f t-1) := by
    intro t u he
    apply hf
    change f t-1=f u-1 at he
    have ht := hpos t
    have hu := hpos u
    omega
  have hpair : Function.Injective (fun t => (i,f t-1)) := by
    intro t u he
    exact hinj (congrArg Prod.snd he)
  have hx := hm.iIndep_X.precomp hinj
  have he := hm.iIndep_ε.precomp hpair
  have hind := hm.indep_X_ε.comp
    (measurable_pi_lambda _ (fun t => measurable_pi_apply (f t-1)))
    (measurable_pi_lambda _ (fun t => measurable_pi_apply (i,f t-1)))
  refine ⟨by simpa only [htime] using hx,by simpa only [htime] using he,?_⟩
  change IndepFun (fun ω t => X (f t-1+1) ω) (fun ω t => ε i (f t-1+1) ω) P at hind
  simpa only [htime] using hind

lemma lb_model_law_probability {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒳 : Set (Fin d → ℝ))
    (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0)
    (hm : IsCovariateNoiseModel P 𝒳 PX X ε σ) : IsProbabilityMeasure PX := by
  rw [←hm.law_X 1 le_rfl]
  exact Measure.isProbabilityMeasure_map (hm.measurable_X 1 le_rfl).aemeasurable

lemma lb_sparsity_bound {d K : ℕ} (β : Fin K → Fin d → ℝ) (i : Fin K) :
    1 ≤ sparsity β ∧ (supp (β i)).card ≤ sparsity β := by
  classical
  refine ⟨le_max_left _ _,?_⟩
  exact (Finset.le_sup (f := fun j => (supp (β j)).card) (Finset.mem_univ i)).trans (le_max_right _ _)

end BastaniBayati.LassoBandit

set_option autoImplicit false
open Matrix ConfBallMatrix
namespace BastaniBayati.LassoBandit
lemma lb_lasso_oracle_sparse_bound {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (E : ι → ℝ)
    (β b : Fin d → ℝ) (s0 : ℕ) (φ lam : ℝ) (hn : 1 ≤ Fintype.card ι)
    (hs0 : (supp β).card ≤ s0) (hs : 1 ≤ s0) (hφ : 0 < φ) (hlam : 0 < lam)
    (hmin : IsLassoMinimizer X (fun t => X t ⬝ᵥ β+E t) lam b)
    (hnoise : ∀ j,|(∑ t,E t*X t j)/(Fintype.card ι : ℝ)| ≤ lam/4)
    (hcompat : sampleCov X ∈ compatSet (supp β) φ) :
    l1Norm (b-β) ≤ 4*s0*lam/φ^2 := by
  classical
  let v := b-β
  let q := v ⬝ᵥ (sampleCov X *ᵥ v)
  let R := (∑ t,E t*(X t ⬝ᵥ v))/(Fintype.card ι : ℝ)
  let U := l1Norm (restrictTo (supp β) v)
  let V := l1Norm (restrictTo (supp β)ᶜ v)
  let L := l1Norm v
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hs
  have hq : 0 ≤ q := by simpa [q] using hcompat.1.dotProduct_mulVec_nonneg v
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hL : L=U+V := lb_l1_split (supp β) v
  have hR : R ≤ lam/4*L := by
    dsimp [R]
    rw [lb_cross_eq_general]
    dsimp [L,l1Norm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc _ ≤ |((∑ t,E t*X t j)/(Fintype.card ι : ℝ))*v j| := le_abs_self _
      _ = |(∑ t,E t*X t j)/(Fintype.card ι : ℝ)| * |v j| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hnoise j) (abs_nonneg _)
  have hpen : l1Norm β-l1Norm b ≤ U-V := lb_l1_difference β b
  have hm := hmin β
  unfold lassoObjective at hm
  have herr : ∀ t,X t ⬝ᵥ β+E t-X t ⬝ᵥ b = E t-X t ⬝ᵥ v := by
    intro t
    dsimp [v]
    rw [dotProduct_sub]
    ring
  have hsum : ∑ t,(E t-X t ⬝ᵥ v)^2 =
      ∑ t,E t^2-2*∑ t,E t*(X t ⬝ᵥ v)+∑ t,(X t ⬝ᵥ v)^2 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp only [herr,add_sub_cancel_left] at hm
  rw [hsum,add_div,sub_div,mul_div_assoc] at hm
  have hqeq : (∑ t,(X t ⬝ᵥ v)^2)/(Fintype.card ι : ℝ) = q := (lb_cov_quad_general X v).symm
  change _ ≤ _ at hm
  rw [hqeq] at hm
  change (∑ t,E t^2)/(Fintype.card ι : ℝ)-2*R+q+lam*l1Norm b ≤ (∑ t,E t^2)/(Fintype.card ι : ℝ)+lam*l1Norm β at hm
  have hp := mul_le_mul_of_nonneg_left hpen hlam.le
  have hbasic : q+lam/2*L ≤ 2*lam*U := by nlinarith
  have hcone : V ≤ 3*U := by nlinarith
  have hcomp := hcompat.2 v hcone
  have hcomp' : φ^2*U^2 ≤ (s0 : ℝ)*q := by
    rw [le_div_iff₀ (sq_pos_of_pos hφ)] at hcomp
    have hcard : ((supp β).card : ℝ) ≤ s0 := by exact_mod_cast hs0
    have hcq := mul_le_mul_of_nonneg_right hcard hq
    nlinarith
  exact lb_oracle_numeric q U V L s0 φ lam hs' hφ hlam hq hU hV hL hbasic hcomp'



end BastaniBayati.LassoBandit



open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace BastaniBayati.LassoBandit

/-- **Proposition 2**, Bastani–Bayati, p. 286, stated for the optimal arms `i ∈ 𝒦_opt` (see the
moderation notes: the page says "for all `i ∈ [K]`", but Assumption 4 and the region `Uᵢ` on
which the proof sketch of §4.2 rests exist only for `i ∈ 𝒦_opt`). Under the model of §2.1 and
Assumptions 1–4, with `K ≥ 2`, `d > 2`, the forced-sample estimator `β̂(𝒯_{i,t}, λ₁)` — any LASSO
estimator on the forced samples `𝒯_{i,t} = 𝒯ᵢ ∩ [t]` of arm `i`, whose responses are
`X_sᵀβᵢ + ε_{i,s}` — satisfies `Pr[‖β̂(𝒯_{i,t}, λ₁) − βᵢ‖₁ > h/(4x_max)] ≤ 5/t⁴` when
`λ₁ = φ₀² p_* h/(64 s₀ x_max)`, `t ≥ (Kq)²` and `q ≥ 4⌈q₀⌉`. -/
theorem lb_forced_estimator_checked
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d K : ℕ}
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0) (β : Fin K → Fin d → ℝ)
    (xmax b C0 h pstar φ0 : ℝ) (Kopt Ksub : Finset (Fin K)) (s0 : ℕ)
    (hmodel : IsCovariateNoiseModel P 𝒳 PX X ε σ) (hσ : 0 < σ)
    (hA1 : ParameterSet 𝒳 β xmax b) (hA2 : MarginCondition PX β C0)
    (hA3 : ArmOptimality 𝒳 PX β Kopt Ksub h pstar)
    (hA4 : CompatibilityAssumption 𝒳 PX β Kopt h φ0)
    (hs0 : s0 = sparsity β) (hK : 2 ≤ K) (hd : 2 < d)
    (sel : LassoSelector d) (hsel : IsLassoSelector sel)
    (q t : ℕ)
    (hq : 4 * ⌈q0 d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0)⌉₊ ≤ q)
    (ht : (K * q) ^ 2 ≤ t) (i : Fin K) (hi : i ∈ Kopt) :
    P {ω | h / (4 * xmax) < l1Norm (lassoEst sel (forcedUpTo K q i t) (fun s => X s ω)
        (fun s => X s ω ⬝ᵥ β i + ε i s ω) (lam1 s0 xmax h pstar φ0) - β i)} ≤
      ENNReal.ofReal (5 / (t : ℝ) ^ 4) := by
  classical
  have hx := hA1.1
  have hh := hA3.1
  have hp := hA3.2.1
  have hφ := hA4.1
  have hsparsity := lb_sparsity_bound β i
  rw [←hs0] at hsparsity
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hsparsity.1
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hc1 : 0 < C1 s0 σ xmax φ0 := by unfold C1;positivity
  have hc2 : 0 < C2 s0 xmax φ0 := by unfold C2;apply lt_min <;> positivity
  have hqn := lb_q0_numeric d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0) q
    hx hh hp hc1 hc2 hq
  have hqpos := hqn.1
  have hKq : 2 ≤ K*q := by nlinarith
  have ht3 : 3 ≤ t := by nlinarith
  have hlogt := lb_log_ge_one ht3
  have hlogd := lb_log_ge_one (by omega : 3 ≤ d)
  have ht' : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  let A := forcedUpTo K q i t
  let n := A.card
  let f : Fin n → ℕ := A.orderEmbOfFin rfl
  let Z : Fin n → Ω → Fin d → ℝ := fun k => X (f k)
  let E : Fin n → Ω → ℝ := fun k => ε i (f k)
  let lam := lam1 s0 xmax h pstar φ0
  let φ := φ0*Real.sqrt pstar/2
  have hlam : 0 < lam := by dsimp [lam,lam1];positivity
  have hφ' : 0 < φ := by dsimp [φ];positivity
  have hcount : (q : ℝ)/2*Real.log t ≤ n := lb_forced_log_count i t (by omega) hqpos ht
  have hn' : (0 : ℝ) < n := by
    have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hL : 0 < Real.log t := by linarith
    exact (mul_pos (div_pos hqp (by norm_num)) hL).trans_le hcount
  have hn : 0 < n := by exact_mod_cast hn'
  have hA : A ≠ ∅ := (Finset.card_ne_zero.mp hn.ne').ne_empty
  have hf : Function.Injective f := (A.orderEmbOfFin rfl).injective
  have hfpos : ∀ k,1 ≤ f k := by
    intro k
    have hm := A.orderEmbOfFin_mem rfl k
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hfinite := lb_model_finite P 𝒳 PX X ε σ hmodel f hf hfpos i
  have hZ : ∀ k,Measurable (Z k) := fun k => hmodel.measurable_X _ (hfpos k)
  have hE : ∀ k,Measurable (E k) := fun k => hmodel.measurable_ε i _ (hfpos k)
  have hsg : ∀ k,HasSubgaussianMGF (E k) (σ^2) P := fun k => hmodel.subgaussian i _ (hfpos k)
  have hbound : ∀ k ω,‖Z k ω‖ ≤ xmax := fun k ω =>
    hA1.2.2.1 _ (hmodel.mem_domain _ (hfpos k) ω)
  have hlaw : ∀ k,P.map (Z k)=PX := fun k => hmodel.law_X _ (hfpos k)
  haveI : IsProbabilityMeasure PX := lb_model_law_probability P 𝒳 PX X ε σ hmodel
  let U := optRegion 𝒳 β h i
  have hU : MeasurableSet U := lb_optRegion_measurable 𝒳 β h i hmodel.measurableSet_domain
  have hpr : pstar ≤ PX.real U := by
    have hm := ENNReal.toReal_mono (measure_ne_top PX U) (hA3.2.2.2.2.2 i hi)
    rw [ENNReal.toReal_ofReal hp.le] at hm
    exact hm
  let BadCov : Set Ω := {ω | sampleCov (fun k => Z k ω) ∉ compatSet (supp (β i)) φ}
  let BadNoise : Set Ω := {ω | ∃ j : Fin d,lam/4 < |(∑ k,E k ω*Z k ω j)/(n : ℝ)|}
  have hcov : P BadCov ≤ ENNReal.ofReal (2/(t : ℝ)^4) := by
    have hc := lb_masked_compatibility_tail P Z PX U hU (supp (β i)) s0 xmax φ0 pstar
      (by simpa using hn) hsparsity.2 hsparsity.1 hx hφ hp hpr (hA4.2 i hi)
      hZ hfinite.1 hlaw hbound
    have hb := lb_forced_covariance_numeric d n q pstar (C2 s0 xmax φ0) t (by omega)
      ht' hp hc2 hlogt hcount hqn.2.2.1 hqn.2.2.2.1
    simp only [Fintype.card_fin] at hc
    exact hc.trans (ENNReal.ofReal_le_ofReal hb)
  have hnoise : P BadNoise ≤ ENNReal.ofReal (2/(t : ℝ)^4) := by
    have ht0 := lb_independent_noise_max_tail P Z E σ xmax (lam/4) (by simpa using hn)
      hσ hx (by positivity) hZ hE hfinite.2.1 hfinite.2.2 hsg hbound
    let rate := h^2*pstar^2*C1 s0 σ xmax φ0/(256*xmax^2)
    have hrate : 0 < rate := by dsimp [rate];positivity
    have hrateEq : (lam/4)^2/(2*(σ : ℝ)^2*xmax^2)=rate := by
      dsimp [lam,lam1,rate,C1]
      field_simp <;> ring
    have he : -(n : ℝ)*(lam/4)^2/(2*(σ : ℝ)^2*xmax^2)=-(n : ℝ)*rate := by
      rw [mul_div_assoc,hrateEq]
    have hb := lb_forced_noise_numeric d n q rate t (by omega) ht' hrate
      hlogd hlogt hcount hqn.2.2.2.2
    have ht1 : P BadNoise ≤ ENNReal.ofReal (2*d*Real.exp (-(n : ℝ)*rate)) := by
      simpa only [Fintype.card_fin,he] using ht0
    exact ht1.trans (ENNReal.ofReal_le_ofReal hb)
  have hmin : ∀ ω,IsLassoMinimizer (fun k => Z k ω)
      (fun k => Z k ω ⬝ᵥ β i+E k ω) lam
      (lassoEst sel A (fun s => X s ω) (fun s => X s ω ⬝ᵥ β i+ε i s ω) lam) := by
    intro ω
    dsimp only [lassoEst]
    rw [if_neg hA]
    exact hsel n _ _ lam hlam.le
  have horacleEq : 4*(s0 : ℝ)*lam/φ^2=h/(4*xmax) := by
    dsimp [lam,lam1,φ]
    rw [div_pow,mul_pow,Real.sq_sqrt hp.le]
    field_simp <;> ring
  have hsub : {ω | h/(4*xmax) < l1Norm (lassoEst sel A (fun s => X s ω)
      (fun s => X s ω ⬝ᵥ β i+ε i s ω) lam-β i)} ⊆ BadCov ∪ BadNoise := by
    intro ω hω
    by_contra hnot
    have hc : sampleCov (fun k => Z k ω) ∈ compatSet (supp (β i)) φ := by
      by_contra hc
      exact hnot (Or.inl hc)
    have hnn : ∀ j,|(∑ k,E k ω*Z k ω j)/(Fintype.card (Fin n) : ℝ)| ≤ lam/4 := by
      intro j
      simp only [Fintype.card_fin]
      exact le_of_not_gt (fun hj => hnot (Or.inr ⟨j,hj⟩))
    have ho := lb_lasso_oracle_sparse_bound (fun k => Z k ω) (fun k => E k ω) (β i)
      (lassoEst sel A (fun s => X s ω) (fun s => X s ω ⬝ᵥ β i+ε i s ω) lam)
      s0 φ lam (by simp only [Fintype.card_fin];omega) hsparsity.2 hsparsity.1 hφ' hlam (hmin ω) hnn hc
    rw [horacleEq] at ho
    exact (not_lt_of_ge ho) hω
  calc _ ≤ P (BadCov ∪ BadNoise) := measure_mono hsub
    _ ≤ P BadCov+P BadNoise := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2/(t : ℝ)^4)+ENNReal.ofReal (2/(t : ℝ)^4) := add_le_add hcov hnoise
    _ ≤ _ := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have htt : (0 : ℝ) < (t : ℝ)^4 := by positivity
      rw [←add_div,div_le_div_iff_of_pos_right htt]
      norm_num


end BastaniBayati.LassoBandit


open MeasureTheory ProbabilityTheory Matrix BastaniBayati.LassoBandit
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d K : ℕ}
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin K → ℕ → Ω → ℝ) (σ : ℝ≥0) (β : Fin K → Fin d → ℝ)
    (xmax b C0 h pstar φ0 : ℝ) (Kopt Ksub : Finset (Fin K)) (s0 : ℕ)
    (hmodel : IsCovariateNoiseModel P 𝒳 PX X ε σ) (hσ : 0 < σ)
    (hA1 : ParameterSet 𝒳 β xmax b) (hA2 : MarginCondition PX β C0)
    (hA3 : ArmOptimality 𝒳 PX β Kopt Ksub h pstar)
    (hA4 : CompatibilityAssumption 𝒳 PX β Kopt h φ0)
    (hs0 : s0 = sparsity β) (hK : 2 ≤ K) (hd : 2 < d)
    (sel : LassoSelector d) (hsel : IsLassoSelector sel)
    (q t : ℕ)
    (hq : 4 * ⌈q0 d xmax h pstar (C1 s0 σ xmax φ0) (C2 s0 xmax φ0)⌉₊ ≤ q)
    (ht : (K * q) ^ 2 ≤ t) (i : Fin K) (hi : i ∈ Kopt) :
    P {ω | h / (4 * xmax) < l1Norm (lassoEst sel (forcedUpTo K q i t) (fun s => X s ω)
        (fun s => X s ω ⬝ᵥ β i + ε i s ω) (lam1 s0 xmax h pstar φ0) - β i)} ≤
      ENNReal.ofReal (5 / (t : ℝ) ^ 4) := by
  exact lb_forced_estimator_checked P 𝒳 PX X ε σ β xmax b C0 h pstar φ0 Kopt Ksub s0
    hmodel hσ hA1 hA2 hA3 hA4 hs0 hK hd sel hsel q t hq ht i hi

#print axioms solution
