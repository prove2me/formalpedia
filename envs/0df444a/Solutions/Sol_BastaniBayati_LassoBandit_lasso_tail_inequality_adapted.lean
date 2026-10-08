-- Prove2me | solution 1 for BastaniBayati.LassoBandit.lasso_tail_inequality_adapted
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T17:08:20.94771+00:00
-- url     : https://prove2.me/submissions/e1df86f0-bd57-4438-beaa-cb9ea598ffc1

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
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace BastaniBayati.LassoBandit

lemma lb_coordinate_tail {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d n : ℕ} (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → Fin d → ℝ)
    (E : ℕ → Ω → ℝ) (σ c r : ℝ) (hn : 1 ≤ n) (hσ : 0 < σ) (hc : 0 < c) (hr : 0 < r)
    (hX : ∀ t < n,Measurable[ℱ t] (X t))
    (hE : ∀ t < n,Measurable[ℱ (t+1)] (E t))
    (hint : ∀ t < n,∀ s : ℝ,Integrable (fun ω => Real.exp (s*E t ω)) P)
    (hsg : ∀ t < n,∀ s : ℝ,P[fun ω => Real.exp (s*E t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp (σ^2*s^2/2))
    (hb : ∀ t < n,∀ ω,‖X t ω‖ ≤ c) (j : Fin d) :
    P {ω | r < |(∑ t : Fin n,E t ω*X t ω j)/(n : ℝ)|} ≤
      ENNReal.ofReal (2*Real.exp (-(n : ℝ)*r^2/(2*σ^2*c^2))) := by
  let Y : ℕ → Ω → ℝ := fun t ω => X t ω j
  have hY : ∀ t < n,Measurable[ℱ t] (Y t) := fun t ht => (measurable_pi_apply j).comp (hX t ht)
  have hYb : ∀ t < n,∀ ω,|Y t ω| ≤ c := by
    intro t ht ω
    have hi : |X t ω j| ≤ ‖X t ω‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (X t ω) j
    exact hi.trans (hb t ht ω)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := lb_noise_mgf P ℱ Y E n σ c hc hY hE hYb hint hsg
  have hS := (lb_noise_meas ℱ Y E n n le_rfl hY hE).mono (ℱ.le _) le_rfl
  have htail := lb_mgf_tail P (lbNoiseSum Y E n) hS (σ^2*c^2*n) (n*r) (by positivity) (by positivity)
    (by
      intro s
      have heq : σ^2*(s*c)^2*n/2=(σ^2*c^2*n)*s^2/2 := by ring
      simpa only [heq] using hm s)
  have he : {ω | r < |(∑ t : Fin n,E t ω*X t ω j)/(n : ℝ)|} =
      {ω | (n : ℝ)*r < |lbNoiseSum Y E n ω|} := by
    ext ω
    change r < |(∑ t : Fin n,E t ω*X t ω j)/(n : ℝ)| ↔ (n : ℝ)*r < |lbNoiseSum Y E n ω|
    rw [abs_div,abs_of_pos hn',lt_div_iff₀ hn']
    have hsum : (∑ t : Fin n,E t ω*X t ω j) = lbNoiseSum Y E n ω := by
      rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => E t ω*X t ω j)]
      unfold lbNoiseSum Y
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hsum,mul_comm r (n : ℝ)]
  rw [he]
  have heq : -((n : ℝ)*r)^2/(2*(σ^2*c^2*n))=-(n : ℝ)*r^2/(2*σ^2*c^2) := by
    field_simp <;> ring
  simpa only [heq] using htail

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
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal
namespace BastaniBayati.LassoBandit

/-- **Proposition 1** (LASSO Tail Inequality for Adapted Observations), Bastani–Bayati, p. 283.
Rows `X₀, …, X_{n−1}` (the paper's `X₁, …, Xₙ`) and noises `ε₀, …, ε_{n−1}` on a filtered
probability space: `X_t` is `ℱ_t`-measurable (it may depend on the past rows and responses),
`ε_t` is `ℱ_{t+1}`-measurable and `σ`-subgaussian conditionally on `ℱ_t`, the responses are
`Y(t) = X_tᵀβ + ε_t`, `‖β‖₀ = s₀ ≥ 1`, every realization has `‖X_t‖_∞ ≤ x_max`. Then for every
`φ, χ > 0`, every LASSO estimator `β̂` with `λ = χφ²/(4s₀)` satisfies
`Pr[‖β̂ − β‖₁ > χ] ≤ 2 exp[−C₁(φ) n χ² + log d] + Pr[Σ̂(X) ∉ 𝒞(supp(β), φ)]`. -/
lemma lb_adapted_checked {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d n : ℕ} (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (φ χ : ℝ)
    (βhat : Ω → Fin d → ℝ)
    (hn : 1 ≤ n) (hσ : 0 < σ) (hxmax : 0 < xmax)
    (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0) (hφ : 0 < φ) (hχ : 0 < χ)
    (hX_adapted : ∀ t < n, Measurable[ℱ t] (X t))
    (hε_meas : ∀ t < n, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t < n, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t < n, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t < n, ∀ ω, ‖X t ω‖ ≤ xmax)
    (hβhat : ∀ ω, IsLassoMinimizer (fun k : Fin n => X k ω) (fun k : Fin n => X k ω ⬝ᵥ β + ε k ω)
      (χ * φ ^ 2 / (4 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax φ) * n * χ ^ 2 + Real.log d)) +
        P {ω | sampleCov (fun k : Fin n => X k ω) ∉ compatSet (supp β) φ} := by
  classical
  let lam := χ*φ^2/(4*s0)
  have hs : (0 : ℝ) < s0 := by exact_mod_cast hs0pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hlam : 0 < lam := by dsimp [lam];positivity
  have hd : 0 < d := by
    have hc : (supp β).card ≤ d := by simpa only [Fintype.card_fin] using Finset.card_le_univ (supp β)
    omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let A : Fin d → Set Ω := fun j => {ω | lam/4 < |(∑ t : Fin n,ε t ω*X t ω j)/(n : ℝ)|}
  let C : Set Ω := {ω | sampleCov (fun k : Fin n => X k ω) ∉ compatSet (supp β) φ}
  have hA : ∀ j,P (A j) ≤ ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax φ)*n*χ^2)) := by
    intro j
    have h := lb_coordinate_tail P ℱ X ε σ xmax (lam/4) hn hσ' hxmax (by positivity)
      hX_adapted hε_meas hε_int hε_subg hbound j
    have he : -(n : ℝ)*(lam/4)^2/(2*(σ : ℝ)^2*xmax^2) = -(C1 s0 σ xmax φ)*n*χ^2 := by
      dsimp [lam,C1]
      field_simp
      ring
    simpa only [A,he] using h
  have hsub : {ω | χ < l1Norm (βhat ω-β)} ⊆ (⋃ j,A j) ∪ C := by
    intro ω hω
    by_cases hC : ω ∈ C
    · exact Or.inr hC
    · by_cases hN : ω ∈ ⋃ j,A j
      · exact Or.inl hN
      · exfalso
        have hcompat : sampleCov (fun k : Fin n => X k ω) ∈ compatSet (supp β) φ := by
          simpa only [C,Set.mem_ofPred_eq,not_not] using hC
        have hnoise : ∀ j,|(∑ t : Fin n,ε t ω*X t ω j)/(n : ℝ)| ≤ lam/4 := by
          intro j
          have hj : ω ∉ A j := fun hj => hN (Set.mem_iUnion.mpr ⟨j,hj⟩)
          exact le_of_not_gt hj
        have horacle := lb_lasso_oracle (fun k : Fin n => X k ω) (fun k : Fin n => ε k ω)
          β (βhat ω) s0 φ lam hn hs0 hs0pos hφ hlam (hβhat ω) hnoise hcompat
        have he : 4*(s0 : ℝ)*lam/φ^2 = χ := by dsimp [lam];field_simp
        rw [he] at horacle
        exact (not_lt_of_ge horacle) hω
  have hsum : (∑ _j : Fin d,ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax φ)*n*χ^2))) =
      ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax φ)*n*χ^2+Real.log d)) := by
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    rw [Real.exp_add,Real.exp_log hd']
    ring
  calc _ ≤ P ((⋃ j,A j) ∪ C) := measure_mono hsub
    _ ≤ P (⋃ j,A j)+P C := measure_union_le _ _
    _ ≤ (∑ j,P (A j))+P C := add_le_add (measure_iUnion_fintype_le P A) le_rfl
    _ ≤ (∑ _j : Fin d,ENNReal.ofReal (2*Real.exp (-(C1 s0 σ xmax φ)*n*χ^2)))+P C :=
      add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hA j)) le_rfl
    _ = _ := by rw [hsum]


end BastaniBayati.LassoBandit


open MeasureTheory ProbabilityTheory Matrix BastaniBayati.LassoBandit
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d n : ℕ} (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (β : Fin d → ℝ) (σ : ℝ≥0) (xmax : ℝ) (s0 : ℕ) (φ χ : ℝ)
    (βhat : Ω → Fin d → ℝ)
    (hn : 1 ≤ n) (hσ : 0 < σ) (hxmax : 0 < xmax)
    (hs0 : (supp β).card = s0) (hs0pos : 1 ≤ s0) (hφ : 0 < φ) (hχ : 0 < χ)
    (hX_adapted : ∀ t < n, Measurable[ℱ t] (X t))
    (hε_meas : ∀ t < n, Measurable[ℱ (t + 1)] (ε t))
    (hε_int : ∀ t < n, ∀ s : ℝ, Integrable (fun ω => Real.exp (s * ε t ω)) P)
    (hε_subg : ∀ t < n, ∀ s : ℝ,
      P[fun ω => Real.exp (s * ε t ω) | ℱ t] ≤ᵐ[P] fun _ => Real.exp ((σ : ℝ) ^ 2 * s ^ 2 / 2))
    (hbound : ∀ t < n, ∀ ω, ‖X t ω‖ ≤ xmax)
    (hβhat : ∀ ω, IsLassoMinimizer (fun k : Fin n => X k ω) (fun k : Fin n => X k ω ⬝ᵥ β + ε k ω)
      (χ * φ ^ 2 / (4 * s0)) (βhat ω)) :
    P {ω | χ < l1Norm (βhat ω - β)} ≤
      ENNReal.ofReal (2 * Real.exp (-(C1 s0 σ xmax φ) * n * χ ^ 2 + Real.log d)) +
        P {ω | sampleCov (fun k : Fin n => X k ω) ∉ compatSet (supp β) φ} := by
  exact lb_adapted_checked P ℱ X ε β σ xmax s0 φ χ βhat hn hσ hxmax hs0 hs0pos hφ hχ hX_adapted hε_meas hε_int hε_subg hbound hβhat

#print axioms solution
