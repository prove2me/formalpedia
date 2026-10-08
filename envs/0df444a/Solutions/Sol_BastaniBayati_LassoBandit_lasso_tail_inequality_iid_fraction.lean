-- Prove2me | solution 1 for BastaniBayati.LassoBandit.lasso_tail_inequality_iid_fraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T19:10:04.04061+00:00
-- url     : https://prove2.me/submissions/8ff4e004-c081-4b3f-ac19-357b1b6716b5

/- Written by Codex. Weighted-MGF helpers adapted from Nickrobbins95's
accepted UCB(delta) submission 85177580-d961-4a1a-9320-e4e2db2e23e0.
Matrix helpers credited to accepted OFUL submission 028e111f-382d-40d0-8008-127228d5e6cf. -/
import Mathlib
import Definitions.Def_BastaniBayati_LassoBandit_Basic
import Definitions.Def_BastaniBayati_LassoBandit_Constants


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
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BastaniBayati.LassoBandit

lemma lb_finite_noise_mgf {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X E : ℕ → Ω → ℝ)
    (A : Finset ℕ) (σ c : ℝ) (hc : 0 < c)
    (hX : ∀ t ∈ A,Measurable[ℱ t] (X t))
    (hE : ∀ t ∈ A,Measurable[ℱ (t+1)] (E t))
    (hb : ∀ t ∈ A,∀ ω,|X t ω| ≤ c)
    (hint : ∀ t ∈ A,∀ s : ℝ,Integrable (fun ω => Real.exp (s*E t ω)) P)
    (hsg : ∀ t ∈ A,∀ s : ℝ,P[fun ω => Real.exp (s*E t ω) | ℱ t] ≤ᵐ[P]
      fun _ => Real.exp (σ^2*s^2/2)) (s : ℝ) :
    ∫⁻ ω,ENNReal.ofReal (Real.exp (s*(∑ t ∈ A,X t ω*E t ω))) ∂P ≤
      ENNReal.ofReal (Real.exp (σ^2*(s*c)^2*A.card/2)) := by
  classical
  revert hX hE hb hint hsg
  induction A using Finset.induction_on_max with
  | empty => intros;simp
  | insert t A hlt ih =>
    intro hX hE hb hint hsg
    have htA : t ∉ A := fun h => (hlt t h).false
    have ht : t ∈ insert t A := Finset.mem_insert_self _ _
    have hpred := lb_predictable_mgf P (ℱ.le t) (X t) (E t) (hX t ht)
      ((hE t ht).mono (ℱ.le _) le_rfl) σ c hc (hb t ht) (hint t ht) (hsg t ht) s
    have hSum : Measurable[ℱ t] (fun ω => ∑ u ∈ A,X u ω*E u ω) := by
      apply Finset.measurable_sum
      intro u hu
      have hut := hlt u hu
      have hu' : u ∈ insert t A := Finset.mem_insert_of_mem hu
      exact ((hX u hu').mono (ℱ.mono (by omega)) le_rfl).mul
        ((hE u hu').mono (ℱ.mono (by omega)) le_rfl)
    have hW : Measurable[ℱ t] (fun ω => ENNReal.ofReal (Real.exp (s*(∑ u ∈ A,X u ω*E u ω)))) :=
      ENNReal.measurable_ofReal.comp (hSum.const_mul s).exp
    have hstep := lb_weighted_mgf (ℱ.le t)
      (((hX t ht).mono (ℱ.le _) le_rfl).mul ((hE t ht).mono (ℱ.le _) le_rfl))
      s (Real.exp (σ^2*(s*c)^2/2)) hpred.1 hpred.2 hW
    have hih := ih (fun u hu => hX u (Finset.mem_insert_of_mem hu))
      (fun u hu => hE u (Finset.mem_insert_of_mem hu))
      (fun u hu => hb u (Finset.mem_insert_of_mem hu))
      (fun u hu => hint u (Finset.mem_insert_of_mem hu))
      (fun u hu => hsg u (Finset.mem_insert_of_mem hu))
    have he : (fun ω => ENNReal.ofReal (Real.exp (s*(∑ u ∈ insert t A,X u ω*E u ω)))) =
      fun ω => ENNReal.ofReal (Real.exp (s*(∑ u ∈ A,X u ω*E u ω)))*
        ENNReal.ofReal (Real.exp (s*(X t ω*E t ω))) := by
      funext ω
      rw [Finset.sum_insert htA,add_comm,mul_add,Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [he]
    calc _ ≤ _ := hstep
      _ ≤ ENNReal.ofReal (Real.exp (σ^2*(s*c)^2/2))*
        ENNReal.ofReal (Real.exp (σ^2*(s*c)^2*A.card/2)) := mul_le_mul' le_rfl hih
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add,Finset.card_insert_of_notMem htA]
        congr 2
        push_cast
        ring

lemma lb_finite_coordinate_tail {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → Fin d → ℝ)
    (E : ℕ → Ω → ℝ) (A : Finset ℕ) (σ c r : ℝ) (hA : A.Nonempty)
    (hσ : 0 < σ) (hc : 0 < c) (hr : 0 < r)
    (hX : ∀ t ∈ A,Measurable[ℱ t] (X t))
    (hE : ∀ t ∈ A,Measurable[ℱ (t+1)] (E t))
    (hint : ∀ t ∈ A,∀ s : ℝ,Integrable (fun ω => Real.exp (s*E t ω)) P)
    (hsg : ∀ t ∈ A,∀ s : ℝ,P[fun ω => Real.exp (s*E t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp (σ^2*s^2/2))
    (hb : ∀ t ∈ A,∀ ω,‖X t ω‖ ≤ c) (j : Fin d) :
    P {ω | r < |(∑ t ∈ A,E t ω*X t ω j)/(A.card : ℝ)|} ≤
      ENNReal.ofReal (2*Real.exp (-(A.card : ℝ)*r^2/(2*σ^2*c^2))) := by
  let Y : ℕ → Ω → ℝ := fun t ω => X t ω j
  have hY : ∀ t ∈ A,Measurable[ℱ t] (Y t) := fun t ht => (measurable_pi_apply j).comp (hX t ht)
  have hYb : ∀ t ∈ A,∀ ω,|Y t ω| ≤ c := by
    intro t ht ω
    have hi : |X t ω j| ≤ ‖X t ω‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (X t ω) j
    exact hi.trans (hb t ht ω)
  have hn : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hm := lb_finite_noise_mgf P ℱ Y E A σ c hc hY hE hYb hint hsg
  have hS : Measurable (fun ω => ∑ t ∈ A,Y t ω*E t ω) := by
    exact Finset.measurable_sum _ (fun t ht => ((hY t ht).mono (ℱ.le _) le_rfl).mul
      ((hE t ht).mono (ℱ.le _) le_rfl))
  have htail := lb_mgf_tail P (fun ω => ∑ t ∈ A,Y t ω*E t ω) hS
    (σ^2*c^2*A.card) (A.card*r) (by positivity) (by positivity) (by
      intro s
      have he : σ^2*(s*c)^2*A.card/2 = (σ^2*c^2*A.card)*s^2/2 := by ring
      simpa only [he] using hm s)
  have he : {ω | r < |(∑ t ∈ A,E t ω*X t ω j)/(A.card : ℝ)|} =
      {ω | (A.card : ℝ)*r < |∑ t ∈ A,Y t ω*E t ω|} := by
    ext ω
    change r < |(∑ t ∈ A,E t ω*X t ω j)/(A.card : ℝ)| ↔ _
    rw [abs_div,abs_of_pos hn,lt_div_iff₀ hn]
    simp only [Y,mul_comm (E _ ω),mul_comm r,Set.mem_setOf_eq]
  rw [he]
  have heq : -((A.card : ℝ)*r)^2/(2*(σ^2*c^2*A.card)) = -(A.card : ℝ)*r^2/(2*σ^2*c^2) := by
    field_simp <;> ring
  simpa only [heq] using htail

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_independent_average_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (m c δ : ℝ)
    (hn : 0 < Fintype.card ι) (hc : 0 < c) (hδ : 0 < δ)
    (hY : ∀ t,Measurable (Y t)) (hiid : iIndepFun Y P)
    (hb : ∀ t ω,|Y t ω| ≤ c) (hm : ∀ t,∫ ω,Y t ω ∂P=m) :
    P {ω | δ < |(∑ t,Y t ω)/(Fintype.card ι : ℝ)-m|} ≤
      ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*δ^2/(2*c^2))) := by
  classical
  let w : ℝ≥0 := (‖c-(-c)‖₊/2)^2
  have hw : (w : ℝ)=c^2 := by
    simp only [w,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_ofNat,coe_nnnorm,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ c-(-c) by linarith)]
    ring
  have hsub : ∀ t,HasSubgaussianMGF (fun ω => Y t ω-m) w P := by
    intro t
    have h := hasSubgaussianMGF_of_mem_Icc (hY t).aemeasurable
      (ae_of_all P (fun ω => abs_le.mp (hb t ω)))
    simpa only [hm t] using h
  have hcent : iIndepFun (fun t ω => Y t ω-m) P := by
    exact hiid.comp (fun _ y => y-m) (fun _ => measurable_id.sub_const _)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hcent (s := Finset.univ)
    (fun t _ => hsub t)
  have hn' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  let S : Ω → ℝ := fun ω => ∑ t,(Y t ω-m)
  have hS : Measurable S := Finset.measurable_sum _ (fun t _ => (hY t).sub_const m)
  have htail := lb_mgf_tail P S hS ((Fintype.card ι : ℝ)*c^2)
    ((Fintype.card ι : ℝ)*δ) (by positivity) (by positivity) (by
      intro s
      rw [←ofReal_integral_eq_lintegral_ofReal (hsum.integrable_exp_mul s)
        (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
      apply ENNReal.ofReal_le_ofReal
      have hh := hsum.mgf_le s
      simpa only [mgf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,NNReal.coe_mul,
        NNReal.coe_natCast,hw,S] using hh)
  have he : {ω | δ < |(∑ t,Y t ω)/(Fintype.card ι : ℝ)-m|} =
      {ω | (Fintype.card ι : ℝ)*δ < |S ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hsum' : S ω=(∑ t,Y t ω)-(Fintype.card ι : ℝ)*m := by
      simp [S,Finset.sum_sub_distrib]
    rw [hsum']
    have heq : (∑ t,Y t ω)/(Fintype.card ι : ℝ)-m =
        ((∑ t,Y t ω)-(Fintype.card ι : ℝ)*m)/(Fintype.card ι : ℝ) := by field_simp
    rw [heq,abs_div,abs_of_pos hn',lt_div_iff₀ hn',mul_comm δ]
  rw [he]
  have hexp : -((Fintype.card ι : ℝ)*δ)^2/(2*((Fintype.card ι : ℝ)*c^2)) =
      -(Fintype.card ι : ℝ)*δ^2/(2*c^2) := by field_simp <;> ring
  simpa only [hexp] using htail

lemma lb_covariance_entry_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (Z : ι → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (xmax δ : ℝ) (hn : 0 < Fintype.card ι)
    (hxmax : 0 < xmax) (hδ : 0 < δ) (hZ : ∀ t,Measurable (Z t))
    (hiid : iIndepFun Z P) (hlaw : ∀ t,P.map (Z t)=PZ)
    (hb : ∀ t ω,‖Z t ω‖ ≤ xmax) (i j : Fin d) :
    P {ω | δ < |sampleCov (fun t => Z t ω) i j-∫ z,z i*z j ∂PZ|} ≤
      ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*δ^2/(2*xmax^4))) := by
  let f : (Fin d → ℝ) → ℝ := fun z => z i*z j
  have hf : Measurable f := (measurable_pi_apply i).mul (measurable_pi_apply j)
  have hfZ : ∀ t,Measurable (fun ω => Z t ω i*Z t ω j) := fun t => hf.comp (hZ t)
  have hInd : iIndepFun (fun t ω => Z t ω i*Z t ω j) P := hiid.comp (fun _ => f) (fun _ => hf)
  have hmean : ∀ t,∫ ω,Z t ω i*Z t ω j ∂P=∫ z,z i*z j ∂PZ := by
    intro t
    rw [←hlaw t,integral_map (hZ t).aemeasurable hf.aestronglyMeasurable]
  have hbound : ∀ t ω,|Z t ω i*Z t ω j| ≤ xmax^2 := by
    intro t ω
    have hi0 : |Z t ω i| ≤ ‖Z t ω‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Z t ω) i
    have hi := hi0.trans (hb t ω)
    have hj0 : |Z t ω j| ≤ ‖Z t ω‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (Z t ω) j
    have hj := hj0.trans (hb t ω)
    rw [abs_mul,pow_two]
    exact mul_le_mul hi hj (abs_nonneg _) hxmax.le
  have ht := lb_independent_average_tail P (fun t ω => Z t ω i*Z t ω j)
    (∫ z,z i*z j ∂PZ) (xmax^2) δ hn (by positivity) hδ hfZ hInd hbound hmean
  simpa only [sampleCov,pow_mul,show (xmax^2)^2=xmax^4 by ring] using ht

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
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_covariance_max_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (Z : ι → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (xmax δ : ℝ) (hn : 0 < Fintype.card ι)
    (hxmax : 0 < xmax) (hδ : 0 < δ) (hZ : ∀ t,Measurable (Z t))
    (hiid : iIndepFun Z P) (hlaw : ∀ t,P.map (Z t)=PZ)
    (hb : ∀ t ω,‖Z t ω‖ ≤ xmax) :
    P {ω | ∃ i j : Fin d,δ < |sampleCov (fun t => Z t ω) i j-∫ z,z i*z j ∂PZ|} ≤
      ENNReal.ofReal (2*(d : ℝ)^2*Real.exp (-(Fintype.card ι : ℝ)*δ^2/(2*xmax^4))) := by
  classical
  let A : (Fin d × Fin d) → Set Ω := fun ij =>
    {ω | δ < |sampleCov (fun t => Z t ω) ij.1 ij.2-∫ z,z ij.1*z ij.2 ∂PZ|}
  have hA : ∀ ij,P (A ij) ≤ ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*δ^2/(2*xmax^4))) :=
    fun ij => lb_covariance_entry_tail P Z PZ xmax δ hn hxmax hδ hZ hiid hlaw hb ij.1 ij.2
  have hsub : {ω | ∃ i j : Fin d,δ < |sampleCov (fun t => Z t ω) i j-∫ z,z i*z j ∂PZ|} ⊆ ⋃ ij,A ij := by
    rintro ω ⟨i,j,h⟩
    exact Set.mem_iUnion.mpr ⟨(i,j),h⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ ij,P (A ij) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ij : Fin d × Fin d,ENNReal.ofReal (2*Real.exp (-(Fintype.card ι : ℝ)*δ^2/(2*xmax^4))) :=
      Finset.sum_le_sum (fun ij _ => hA ij)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
        ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring

lemma lb_covariance_fraction_numeric (d : ℕ) (N m p c : ℝ) (hd : 1 < d)
    (hp : 0 < p) (hc : 0 < c) (hfrac : p/2*N ≤ m)
    (hsize : 6*Real.log d/(p*c^2) ≤ N) :
    2*(d : ℝ)^2*Real.exp (-2*m*c^2) ≤ Real.exp (-p*c^2*N/2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 6*Real.log d ≤ N*(p*c^2) := (div_le_iff₀ (by positivity)).mp hsize
  have hf := mul_le_mul_of_nonneg_right hfrac (show 0 ≤ 2*c^2 by positivity)
  have hpow : 2*(d : ℝ)^2 ≤ (d : ℝ)^3 := by nlinarith [sq_nonneg (d : ℝ)]
  have he : (d : ℝ)^3=Real.exp (3*Real.log d) := by
    rw [show 3*Real.log d=Real.log d+Real.log d+Real.log d by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hd']
    ring
  calc _ ≤ (d : ℝ)^3*Real.exp (-2*m*c^2) := mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (3*Real.log d-2*m*c^2) := by rw [he,←Real.exp_add];congr 1;ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_covariance_fraction {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (Z : ℕ → Ω → Fin d → ℝ)
    (PZ : Measure (Fin d → ℝ)) (A B : Finset ℕ) (I : Finset (Fin d))
    (s0 : ℕ) (xmax φ p : ℝ) (hs : I.card=s0) (hspos : 1 ≤ s0)
    (hxmax : 0 < xmax) (hφ : 0 < φ) (hp : 0 < p) (hd : 1 < d)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    (hZ : ∀ t ∈ B,Measurable (Z t))
    (hiid : iIndepFun (fun t : B => Z t) P)
    (hlaw : ∀ t ∈ B,P.map (Z t)=PZ) (hb : ∀ t ∈ B,∀ ω,‖Z t ω‖ ≤ xmax)
    (hSigma : (fun i j => ∫ z,z i*z j ∂PZ : Matrix (Fin d) (Fin d) ℝ) ∈ compatSet I φ)
    (hfrac : p/2 ≤ (B.card : ℝ)/A.card)
    (hsize : 6*Real.log d/(p*C2 s0 xmax φ^2) ≤ A.card) :
    P {ω | sampleCov (fun t : A => Z t ω) ∉ compatSet I (φ*Real.sqrt p/2)} ≤
      ENNReal.ofReal (Real.exp (-(p*C2 s0 xmax φ^2*A.card/2))) := by
  classical
  let c := C2 s0 xmax φ
  let δ := 2*xmax^2*c
  let Sg : Matrix (Fin d) (Fin d) ℝ := fun i j => ∫ z,z i*z j ∂PZ
  have hs' : (0 : ℝ) < s0 := by exact_mod_cast hspos
  have hc : 0 < c := by dsimp [c,C2];apply lt_min <;> positivity
  have hδ : 0 < δ := by dsimp [δ];positivity
  have hn : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hm : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hsmall : δ ≤ φ^2/(32*s0) := by
    have hh : c ≤ φ^2/(256*s0*xmax^2) := min_le_right _ _
    have hh' := (le_div_iff₀ (show (0 : ℝ) < 256*s0*xmax^2 by positivity)).mp hh
    rw [le_div_iff₀ (by positivity)]
    dsimp [δ]
    nlinarith
  let Bad : Set Ω := {ω | ∃ i j : Fin d,δ < |sampleCov (fun t : B => Z t ω) i j-Sg i j|}
  have hsub : {ω | sampleCov (fun t : A => Z t ω) ∉ compatSet I (φ*Real.sqrt p/2)} ⊆ Bad := by
    intro ω hω
    by_contra hnot
    have hentry : ∀ i j,|Sg i j-sampleCov (fun t : B => Z t ω) i j| ≤ δ := by
      intro i j
      rw [abs_sub_comm]
      exact le_of_not_gt (fun h => hnot ⟨i,j,h⟩)
    have hcomp := lb_compat_perturb I s0 (sampleCov (fun t : B => Z t ω)) Sg φ δ
      hs hspos hφ hδ.le hsmall (lb_sample_cov_psd _) hSigma hentry
    have hdom : ∀ v : Fin d → ℝ,p/2*(v ⬝ᵥ (sampleCov (fun t : B => Z t ω) *ᵥ v)) ≤
        v ⬝ᵥ (sampleCov (fun t : A => Z t ω) *ᵥ v) := by
      intro v
      exact (mul_le_mul_of_nonneg_right hfrac ((lb_sample_cov_psd _).dotProduct_mulVec_nonneg v)).trans
        (lb_sample_cov_subset (fun t => Z t ω) A B hBA hA hB v)
    exact hω (lb_compat_dominate I _ _ φ p hφ hp (lb_sample_cov_psd _) hcomp hdom)
  have ht := lb_covariance_max_tail P (fun t : B => Z t) PZ xmax δ
    (by simpa using Finset.card_pos.mpr hB) hxmax hδ
    (fun t => hZ t t.2) hiid (fun t => hlaw t t.2) (fun t => hb t t.2)
  have he : -(B.card : ℝ)*δ^2/(2*xmax^4) = -2*B.card*c^2 := by
    dsimp [δ]
    field_simp <;> ring
  have hf : p/2*(A.card : ℝ) ≤ B.card := (le_div_iff₀ hn).mp hfrac
  have hnumer := lb_covariance_fraction_numeric d A.card B.card p c hd hp hc hf hsize
  calc _ ≤ P Bad := measure_mono hsub
    _ ≤ ENNReal.ofReal (2*(d : ℝ)^2*Real.exp (-2*B.card*c^2)) := by
      simpa only [Bad,Sg,Fintype.card_coe,he] using ht
    _ ≤ _ := by simpa only [c,neg_div,neg_mul] using ENNReal.ofReal_le_ofReal hnumer

end BastaniBayati.LassoBandit

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

lemma lb_iid_fraction_checked {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (PZ : Measure (Fin d → ℝ))
    (A A' : Finset ℕ) (φ1 p χ : ℝ) (βhat : Ω → Fin d → ℝ)
    (hσ : 0 < σ) (hxmax : 0 < xmax) (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0)
    (hφ1 : 0 < φ1) (hp : 0 < p) (hχ : 0 < χ) (hd : 1 < d)
    (hZ_adapted : ∀ t ∈ A, Measurable[ℱ t] (Z t))
    (hε_meas : ∀ t ∈ A, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t ∈ A, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t ∈ A, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t ∈ A, ∀ ω, ‖Z t ω‖ ≤ xmax)
    (hA'A : A' ⊆ A)
    (hiid : iIndepFun (fun t : A' => Z t) P) (hlaw : ∀ t ∈ A', P.map (Z t) = PZ)
    (hSigma : (fun a b => ∫ z, z a * z b ∂PZ : Matrix (Fin d) (Fin d) ℝ) ∈ compatSet (supp β) φ1)
    (hfrac : p / 2 ≤ (A'.card : ℝ) / A.card)
    (hsize : 6 * Real.log d / (p * C2 s0 xmax φ1 ^ 2) ≤ A.card)
    (hβhat : ∀ ω, IsLassoMinimizer (fun t : A => Z t ω) (fun t : A => Z t ω ⬝ᵥ β + ε t ω)
      (χ * φ1 ^ 2 * p / (16 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax (φ1 * Real.sqrt p / 2)) * A.card * χ ^ 2
          + Real.log d) +
        Real.exp (-(p * C2 s0 xmax φ1 ^ 2 * A.card / 2))) := by
  classical
  let a := φ1*Real.sqrt p/2
  let lam := χ*φ1^2*p/(16*s0)
  have hs : (0 : ℝ) < s0 := by exact_mod_cast hs0pos
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hc : 0 < C2 s0 xmax φ1 := by unfold C2;apply lt_min <;> positivity
  have hd' : (1 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log d := Real.log_pos hd'
  have hsizepos : 0 < 6*Real.log d/(p*C2 s0 xmax φ1^2) := by positivity
  have hn : (0 : ℝ) < A.card := hsizepos.trans_le hsize
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hn)
  have hm : (0 : ℝ) < A'.card := by
    have hf := (le_div_iff₀ hn).mp hfrac
    exact (mul_pos (by positivity : 0 < p/2) hn).trans_le hf
  have hB : A'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hm)
  have ha : 0 < a := by dsimp [a];positivity
  have hlam : 0 < lam := by dsimp [lam];positivity
  have ha2 : a^2=φ1^2*p/4 := by
    dsimp [a]
    rw [div_pow,mul_pow,Real.sq_sqrt hp.le]
    norm_num
  let B : Fin d → Set Ω := fun j =>
    {ω | lam/4 < |(∑ t ∈ A,ε t ω*Z t ω j)/(A.card : ℝ)|}
  let C : Set Ω := {ω | sampleCov (fun t : A => Z t ω) ∉ compatSet (supp β) a}
  have hBtail : ∀ j,P (B j) ≤ ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax a)*A.card*χ^2)) := by
    intro j
    have ht := lb_finite_coordinate_tail P ℱ Z ε A σ xmax (lam/4) hA hσ' hxmax
      (by positivity) hZ_adapted hε_meas hε_int hε_subg hbound j
    have he : -(A.card : ℝ)*(lam/4)^2/(2*(σ : ℝ)^2*xmax^2) =
        -(C1 s0 σ xmax a)*A.card*χ^2 := by
      unfold C1
      rw [show a^4=(a^2)^2 by ring,ha2]
      dsimp [lam]
      field_simp <;> ring
    simpa only [B,he] using ht
  have hCtail : P C ≤ ENNReal.ofReal (Real.exp (-(p*C2 s0 xmax φ1^2*A.card/2))) :=
    lb_covariance_fraction P Z PZ A A' (supp β) s0 xmax φ1 p hs0 hs0pos hxmax hφ1 hp hd
      hA hB hA'A (fun t ht => (hZ_adapted t (hA'A ht)).mono (ℱ.le _) le_rfl)
      hiid hlaw (fun t ht => hbound t (hA'A ht)) hSigma hfrac hsize
  have hsub : {ω | χ < l1Norm (βhat ω-β)} ⊆ (⋃ j,B j) ∪ C := by
    intro ω hω
    by_cases hC : ω ∈ C
    · exact Or.inr hC
    · by_cases hN : ω ∈ ⋃ j,B j
      · exact Or.inl hN
      · exfalso
        have hcompat : sampleCov (fun t : A => Z t ω) ∈ compatSet (supp β) a := by
          simpa only [C,Set.mem_ofPred_eq,not_not] using hC
        have hnoise : ∀ j,|(∑ t : A,ε t ω*Z t ω j)/(Fintype.card A : ℝ)| ≤ lam/4 := by
          intro j
          have hj : ω ∉ B j := fun hj => hN (Set.mem_iUnion.mpr ⟨j,hj⟩)
          rw [Fintype.card_coe,Finset.sum_coe_sort A (fun t => ε t ω*Z t ω j)]
          exact le_of_not_gt hj
        have horacle := lb_lasso_oracle_general (fun t : A => Z t ω) (fun t : A => ε t ω)
          β (βhat ω) s0 a lam (by simpa using Finset.card_pos.mpr hA)
          hs0 hs0pos ha hlam (hβhat ω) hnoise hcompat
        have he : 4*(s0 : ℝ)*lam/a^2=χ := by rw [ha2];dsimp [lam];field_simp <;> norm_num
        rw [he] at horacle
        exact (not_lt_of_ge horacle) hω
  have hsum : (∑ _j : Fin d,ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax a)*A.card*χ^2))) =
      ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax a)*A.card*χ^2+Real.log d)) := by
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    rw [Real.exp_add,Real.exp_log (by linarith : (0 : ℝ) < d)]
    ring
  calc _ ≤ P ((⋃ j,B j) ∪ C) := measure_mono hsub
    _ ≤ P (⋃ j,B j)+P C := measure_union_le _ _
    _ ≤ (∑ j,P (B j))+P C := add_le_add (measure_iUnion_fintype_le P B) le_rfl
    _ ≤ (∑ _j : Fin d,ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax a)*A.card*χ^2)))+
      ENNReal.ofReal (Real.exp (-(p*C2 s0 xmax φ1^2*A.card/2))) :=
      add_le_add (Finset.sum_le_sum (fun j _ => hBtail j)) hCtail
    _ = _ := by rw [hsum,←ENNReal.ofReal_add (by positivity) (by positivity)]

end BastaniBayati.LassoBandit

open MeasureTheory ProbabilityTheory Matrix BastaniBayati.LassoBandit
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (PZ : Measure (Fin d → ℝ))
    (A A' : Finset ℕ) (φ1 p χ : ℝ) (βhat : Ω → Fin d → ℝ)
    (hσ : 0 < σ) (hxmax : 0 < xmax) (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0)
    (hφ1 : 0 < φ1) (hp : 0 < p) (hχ : 0 < χ) (hd : 1 < d)
    (hZ_adapted : ∀ t ∈ A, Measurable[ℱ t] (Z t))
    (hε_meas : ∀ t ∈ A, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t ∈ A, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t ∈ A, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t ∈ A, ∀ ω, ‖Z t ω‖ ≤ xmax)
    (hA'A : A' ⊆ A)
    (hiid : iIndepFun (fun t : A' => Z t) P) (hlaw : ∀ t ∈ A', P.map (Z t) = PZ)
    (hSigma : (fun a b => ∫ z, z a * z b ∂PZ : Matrix (Fin d) (Fin d) ℝ) ∈ compatSet (supp β) φ1)
    (hfrac : p / 2 ≤ (A'.card : ℝ) / A.card)
    (hsize : 6 * Real.log d / (p * C2 s0 xmax φ1 ^ 2) ≤ A.card)
    (hβhat : ∀ ω, IsLassoMinimizer (fun t : A => Z t ω) (fun t : A => Z t ω ⬝ᵥ β + ε t ω)
      (χ * φ1 ^ 2 * p / (16 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax (φ1 * Real.sqrt p / 2)) * A.card * χ ^ 2
          + Real.log d) +
        Real.exp (-(p * C2 s0 xmax φ1 ^ 2 * A.card / 2))) := by
  exact lb_iid_fraction_checked P ℱ Z ε β σ xmax s0 PZ A A' φ1 p χ βhat hσ hxmax hs0 hs0pos hφ1 hp hχ hd hZ_adapted hε_meas hε_int hε_subg hbound hA'A hiid hlaw hSigma hfrac hsize hβhat

#print axioms solution
