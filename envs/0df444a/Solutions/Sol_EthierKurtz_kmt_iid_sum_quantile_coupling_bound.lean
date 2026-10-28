-- Prove2me | solution 1 for EthierKurtz.kmt_iid_sum_quantile_coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:55:59.840353+00:00
-- url     : https://prove2.me/submissions/ad142f05-a375-40c4-8a19-f63da4604771

import Mathlib.Tactic
import Theorems.Thm_EthierKurtz_cramer_iid_bounded_tail_ratio
import Theorems.Thm_EthierKurtz_berry_esseen_bounded_independent
import Theorems.Thm_EthierKurtz_tusnady_quantile_sandwich
import Mathlib

namespace IidQAux
open MeasureTheory ProbabilityTheory

local notation "Φ" => cdf (gaussianReal (0:ℝ) (1:NNReal))

lemma gauss_Ioc_pos {a b : ℝ} (h : a < b) : 0 < (gaussianReal (0:ℝ) (1:NNReal)) (Set.Ioc a b) := by
  have hv : (1:NNReal) ≠ 0 := one_ne_zero
  have h1 : volume (Set.Ioc a b) ≠ 0 := by simp [h]
  rw [pos_iff_ne_zero]
  intro h0
  exact h1 ((gaussianReal_absolutelyContinuous' 0 hv) h0)

lemma phi_lt {a b : ℝ} (h : a < b) : Φ a < Φ b := by
  rw [cdf_eq_real, cdf_eq_real]
  have := gauss_Ioc_pos h
  have e : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := (Set.Iic_union_Ioc_eq_Iic h.le).symm
  rw [e, measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  have : 0 < (gaussianReal (0:ℝ) (1:NNReal)).real (Set.Ioc a b) :=
    ENNReal.toReal_pos this.ne' (measure_ne_top _ _)
  linarith

lemma phi_pos (t : ℝ) : 0 < Φ t := lt_of_le_of_lt (cdf_nonneg _ _) (phi_lt (show t - 1 < t by linarith))


section
set_option linter.unusedSectionVars false
variable {F : Measure ℝ} [IsProbabilityMeasure F] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma meas_sum : Measurable (fun x : ι → ℝ => ∑ i, x i) := by fun_prop

lemma ae_coord {K : ℝ} (hK : ∀ᵐ x ∂F, |x| ≤ K) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => F), ∀ i, |x i| ≤ K := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : ι => F) i).quasiMeasurePreserving.ae hK

lemma ae_sum {K : ℝ} (hK : ∀ᵐ x ∂F, |x| ≤ K) :
    ∀ᵐ y ∂((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)),
      |y| ≤ (Fintype.card ι : ℝ) * K := by
  rw [ae_map_iff meas_sum.aemeasurable (measurableSet_le (by fun_prop) (by fun_prop))]
  filter_upwards [ae_coord (ι := ι) hK] with x hx
  calc |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, K := Finset.sum_le_sum fun i _ => hx i
    _ = _ := by simp

lemma cdf_low {K : ℝ} (hK : ∀ᵐ x ∂F, |x| ≤ K) {x : ℝ} (hx : x < -((Fintype.card ι : ℝ) * K)) :
    cdf ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) x = 0 := by
  have : IsProbabilityMeasure ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) :=
    Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  rw [cdf_eq_real, measureReal_def]
  have h := ae_sum (ι := ι) hK
  rw [ae_iff] at h
  have : ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) (Set.Iic x) = 0 := by
    refine measure_mono_null ?_ h
    intro y hy
    simp only [Set.mem_Iic] at hy
    simp only [Set.mem_setOf_eq, not_le]
    linarith [neg_abs_le y]
  simp [this]

lemma cdf_high {K : ℝ} (hK : ∀ᵐ x ∂F, |x| ≤ K) {x : ℝ} (hx : (Fintype.card ι : ℝ) * K ≤ x) :
    cdf ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) x = 1 := by
  have : IsProbabilityMeasure ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) :=
    Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  rw [cdf_eq_real, measureReal_def]
  have h := ae_sum (ι := ι) hK
  rw [ae_iff] at h
  have : ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) (Set.Iic x)ᶜ = 0 := by
    refine measure_mono_null ?_ h
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hy
    simp only [Set.mem_setOf_eq, not_le]
    linarith [le_abs_self y]
  rw [(prob_compl_eq_zero_iff measurableSet_Iic).1 this]; simp

lemma right_tail (y : ℝ) :
    ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)).real (Set.Ioi y) =
      (Measure.pi fun _ : ι => F).real {x : ι → ℝ | y < ∑ i, x i} := by
  rw [map_measureReal_apply meas_sum measurableSet_Ioi]; rfl

lemma left_tail (y : ℝ) :
    ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)).real (Set.Iio (-y)) =
      (Measure.pi fun _ : ι => F.map Neg.neg).real {x : ι → ℝ | y < ∑ i, x i} := by
  have : IsProbabilityMeasure (F.map Neg.neg) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [map_measureReal_apply meas_sum measurableSet_Iio]
  have hpi : (Measure.pi fun _ : ι => F).map (fun x i => Neg.neg (x i)) =
      Measure.pi fun _ : ι => F.map Neg.neg :=
    Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (Neg.neg : ℝ → ℝ)).aemeasurable)
  rw [← hpi, map_measureReal_apply (by fun_prop) (measurableSet_lt (by fun_prop) (by fun_prop))]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq, Finset.sum_neg_distrib]
  constructor <;> intro h <;> linarith

lemma neg_hyps {K : ℝ} (hK : ∀ᵐ x ∂F, |x| ≤ K) (h1 : ∫ x, x ∂F = 0) (h2 : ∫ x, x ^ 2 ∂F = 1) :
    (∀ᵐ x ∂(F.map Neg.neg), |x| ≤ K) ∧ ∫ x, x ∂(F.map Neg.neg) = 0 ∧
      ∫ x, x ^ 2 ∂(F.map Neg.neg) = 1 := by
  have hm : Measurable (Neg.neg : ℝ → ℝ) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · rw [ae_map_iff hm.aemeasurable (measurableSet_le (by fun_prop) (by fun_prop))]
    filter_upwards [hK] with x hx; simpa using hx
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    show ∫ x, -x ∂F = 0
    rw [integral_neg, h1, neg_zero]
  · rw [integral_map hm.aemeasurable (by fun_prop)]
    simp only [even_two, Even.neg_pow]
    exact h2

lemma kolmo {K : ℝ} (hK0 : 0 < K) (hK : ∀ᵐ x ∂F, |x| ≤ K) (h1 : ∫ x, x ∂F = 0)
    (h2 : ∫ x, x ^ 2 ∂F = 1) (hn : K ^ 2 ≤ (Fintype.card ι : ℝ)) (z : ℝ) :
    Φ z - 7 * K / √(Fintype.card ι : ℝ) ≤
        cdf ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i))
          (√(Fintype.card ι : ℝ) * z) ∧
      cdf ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i))
          (√(Fintype.card ι : ℝ) * z) ≤ Φ z + 7 * K / √(Fintype.card ι : ℝ) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set s : ℝ := √n with hs_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hs : 0 < s := Real.sqrt_pos.2 hnpos
  have hs2 : s ^ 2 = n := Real.sq_sqrt hnpos.le
  have hKs : K ≤ s := (Real.le_sqrt hK0.le hnpos.le).2 hn
  set P := Measure.pi fun _ : ι => F with hP
  set L := P.map (fun x : ι → ℝ => ∑ i, x i) with hL
  have : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map meas_sum.aemeasurable
  let c : ℝ → ℝ := fun x => max (-K) (min K x)
  have hc : Measurable c := by fun_prop
  have hcae : ∀ᵐ x ∂F, c x = x := by
    filter_upwards [hK] with x hx
    rw [abs_le] at hx
    simp only [c]; rw [min_eq_right hx.2, max_eq_right hx.1]
  let X : ℝ → ℝ := fun x => c x / s
  let ξ : ι → (ι → ℝ) → ℝ := fun i ω => X (ω i)
  have hind : iIndepFun ξ P := iIndepFun_pi (fun _ => (hc.div_const s).aemeasurable)
  have hmeas : ∀ i, Measurable (ξ i) := fun i => (hc.div_const s).comp (measurable_pi_apply i)
  have hbd : ∀ i ω, |ξ i ω| ≤ K / s := by
    intro i ω
    simp only [ξ, X, abs_div, abs_of_pos hs]
    gcongr
    simp only [c]; rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0 := by
    intro i
    show ∫ ω, X (ω i) ∂(Measure.pi fun _ : ι => F) = 0
    rw [integral_comp_eval (μ := fun _ : ι => F) (i := i) (f := X)
      (hc.div_const s).aestronglyMeasurable]
    rw [integral_congr_ae (hcae.mono fun x hx => by simp only [X]; rw [hx])]
    rw [integral_div, h1, zero_div]
  have hsq : ∑ i, ∫ ω, ξ i ω ^ 2 ∂P = 1 := by
    have : ∀ i, ∫ ω, ξ i ω ^ 2 ∂P = 1 / n := by
      intro i
      show ∫ ω, X (ω i) ^ 2 ∂(Measure.pi fun _ : ι => F) = 1 / n
      rw [integral_comp_eval (μ := fun _ : ι => F) (i := i) (f := fun x => X x ^ 2)
        ((hc.div_const s).pow_const 2).aestronglyMeasurable]
      rw [integral_congr_ae (hcae.mono fun x hx => by simp only [X]; rw [hx, div_pow])]
      rw [integral_div, h2, hs2]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hn_def]; field_simp
  have hBE := EthierKurtz.berry_esseen_bounded_independent ξ hind hmeas (div_pos hK0 hs) hbd hmean
    hsq ((div_le_one hs).2 hKs)
  -- relate to L
  have key : ∀ z, |L.real (Set.Iio (s * z)) - Φ z| ≤ 7 * K / s := by
    intro z
    have e : P {ω | ∑ i, ξ i ω < z} = P {ω | ∑ i, ω i < s * z} := by
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [ae_coord (ι := ι) hK] with ω hω
      have : ∑ i, ξ i ω = (∑ i, ω i) / s := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h' := abs_le.1 (hω i)
        simp only [ξ, X, c]; rw [min_eq_right h'.2, max_eq_right h'.1]
      simp only [this, div_lt_iff₀ hs, mul_comm z s]
    have hz := hBE z
    rw [e] at hz
    rw [hL, map_measureReal_apply meas_sum measurableSet_Iio, mul_div_assoc]
    exact hz
  rw [cdf_eq_real L]
  constructor
  · have := (abs_le.1 (key z)).1
    have hm : L.real (Set.Iio (s * z)) ≤ L.real (Set.Iic (s * z)) :=
      measureReal_mono Set.Iio_subset_Iic_self
    linarith
  · have hev : ∀ z' > z, L.real (Set.Iic (s * z)) ≤ Φ z' + 7 * K / s := by
      intro z' hz'
      have h3 := (abs_le.1 (key z')).2
      have hm : L.real (Set.Iic (s * z)) ≤ L.real (Set.Iio (s * z')) :=
        measureReal_mono (Set.Iic_subset_Iio.2 (mul_lt_mul_of_pos_left hz' hs))
      linarith
    have ht : Filter.Tendsto (fun z' => Φ z' + 7 * K / s) (nhdsWithin z (Set.Ioi z))
        (nhds (Φ z + 7 * K / s)) := by
      apply Filter.Tendsto.add_const
      exact ((cdf (gaussianReal (0:ℝ) (1:NNReal))).right_continuous z).tendsto.mono_left
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hev)
end

end IidQAux


open MeasureTheory ProbabilityTheory
theorem solution :
    ∀ {F : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure F] {K : ℝ},
      (0 : ℝ) < K →
        (∀ᵐ (x : ℝ) ∂F, |x| ≤ K) →
          ∫ (x : ℝ), x ∂F = (0 : ℝ) →
            ∫ (x : ℝ), x ^ (2 : ℕ) ∂F = (1 : ℝ) →
              ∃ (C : ℝ) (m₀ : ℕ),
                (0 : ℝ) < C ∧
                  (1 : ℕ) ≤ m₀ ∧
                    ∀ (ι : Type) [inst : Fintype ι] [DecidableEq ι],
                      m₀ ≤ Fintype.card ι →
                        ∀ (w : ℝ),
                          |InfSet.sInf
                                  {x : ℝ |
                                    (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                        (w / √↑(Fintype.card ι)) ≤
                                      (ProbabilityTheory.cdf
                                            (MeasureTheory.Measure.map (fun (x : ι → ℝ) => ∑ i : ι, x i)
                                              (MeasureTheory.Measure.pi fun (x : ι) => F)))
                                        x} -
                                w| ≤
                            C * ((1 : ℝ) + w ^ (2 : ℕ) / ↑(Fintype.card ι)) := by
  intro F _ K hK0 hK h1 h2
  obtain ⟨c1, e1, hc1, he1, hcr1⟩ := EthierKurtz.cramer_iid_bounded_tail_ratio hK0 hK h1 h2
  obtain ⟨hK', h1', h2'⟩ := IidQAux.neg_hyps hK h1 h2
  have : IsProbabilityMeasure (F.map Neg.neg) := Measure.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨c2, e2, hc2, he2, hcr2⟩ := EthierKurtz.cramer_iid_bounded_tail_ratio hK0 hK' h1' h2'
  obtain ⟨c, ε, m0, hc, hε, hm0, hsand⟩ :=
    EthierKurtz.tusnady_quantile_sandwich c1 e1 c2 e2 (7 * K) hc1 he1 hc2 he2 (by positivity)
  refine ⟨1 + 3 * c + (2 * K / ε + 1) * (2 / ε), max m0 (max ⌈K ^ 2⌉₊ ⌈2 / ε⌉₊),
    by positivity, le_trans hm0 (le_max_left _ _), ?_⟩
  intro ι _ _ hcard w
  have hN0 : m0 ≤ Fintype.card ι := le_trans (le_max_left _ _) hcard
  have hN1 : 1 ≤ Fintype.card ι := le_trans hm0 hN0
  have hNK : K ^ 2 ≤ (Fintype.card ι : ℝ) := le_trans (Nat.le_ceil _)
    (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hcard)
  have hNe : 2 / ε ≤ (Fintype.card ι : ℝ) := le_trans (Nat.le_ceil _)
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hcard)
  have : IsProbabilityMeasure ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i)) :=
    Measure.isProbabilityMeasure_map IidQAux.meas_sum.aemeasurable
  have hS := hsand (Fintype.card ι) hN0
    ((Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i))
    (fun y hy1 hy2 => by rw [IidQAux.right_tail]; exact hcr1 ι hN1 y hy1 hy2)
    (fun y hy1 hy2 => by rw [IidQAux.left_tail]; exact hcr2 ι hN1 y hy1 hy2)
    (fun z _ => IidQAux.kolmo hK0 hK h1 h2 hNK z)
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set L := (Measure.pi fun _ : ι => F).map (fun x : ι → ℝ => ∑ i, x i) with hL
  have hn1 : (1 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hN1
  have hnpos : 0 < n := by linarith
  have hsn : 0 < √n := Real.sqrt_pos.2 hnpos
  set A := {x : ℝ | cdf (gaussianReal (0:ℝ) (1:NNReal)) (w / √n) ≤ cdf L x} with hA
  have hA_mem : n * K ∈ A := by
    rw [hA, Set.mem_setOf_eq, IidQAux.cdf_high hK le_rfl]; exact cdf_le_one _ _
  have hA_low : ∀ x ∈ A, -(n * K) ≤ x := by
    intro x hx
    by_contra h
    push_neg at h
    have h0 := IidQAux.cdf_low hK h
    have hx' : cdf (gaussianReal (0:ℝ) (1:NNReal)) (w / √n) ≤ cdf L x := hx
    rw [h0] at hx'
    linarith [IidQAux.phi_pos (w / √n)]
  have hbdd : BddBelow A := ⟨-(n * K), hA_low⟩
  have hQ_le : sInf A ≤ n * K := csInf_le hbdd hA_mem
  have hQ_ge : -(n * K) ≤ sInf A := le_csInf ⟨_, hA_mem⟩ hA_low
  set t := w ^ 2 / n with ht_def
  have ht0 : 0 ≤ t := by positivity
  have hD0 : 0 ≤ (2 * K / ε + 1) * (2 / ε) := by positivity
  have h2e : 2 ≤ ε * n := by rw [div_le_iff₀ hε] at hNe; linarith
  by_cases hw : |w| ≤ ε * n / 2
  · have hup := (hS w (by linarith)).1
    have hQ1 : sInf A ≤ w + c * (1 + t) := csInf_le hbdd hup
    have hw1 : |w - 1| ≤ ε * n := by
      have := abs_sub (w) 1
      simp at this; linarith
    have hlo := (hS (w - 1) hw1).2
    have hlt : cdf (gaussianReal (0:ℝ) (1:NNReal)) ((w - 1) / √n) <
        cdf (gaussianReal (0:ℝ) (1:NNReal)) (w / √n) :=
      IidQAux.phi_lt (div_lt_div_of_pos_right (by linarith) hsn)
    have hQ2 : w - 1 - c * (1 + (w - 1) ^ 2 / n) ≤ sInf A := by
      refine le_csInf ⟨_, hA_mem⟩ fun x hx => ?_
      by_contra h
      push_neg at h
      have hm := monotone_cdf L h.le
      have hx' : cdf (gaussianReal (0:ℝ) (1:NNReal)) (w / √n) ≤ cdf L x := hx
      linarith
    have hq : (w - 1) ^ 2 / n ≤ 2 * t + 2 := by
      have e1 : (w - 1) ^ 2 / n ≤ (2 * w ^ 2 + 2) / n :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (w + 1)]) hnpos.le
      have e2 : (2 * w ^ 2 + 2) / n = 2 * t + 2 / n := by rw [ht_def]; ring
      have e3 : 2 / n ≤ 2 := div_le_self (by norm_num) hn1
      linarith
    have hcq := mul_le_mul_of_nonneg_left hq hc.le
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hc.le ht0, mul_nonneg hD0 ht0]
    · nlinarith [mul_nonneg hc.le ht0, mul_nonneg hD0 ht0]
  · push_neg at hw
    set a := |w| with ha
    have ha0 : 0 < a := lt_of_le_of_lt (by positivity) hw
    have hnK : n * K ≤ (2 * K / ε) * a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    have hat : a ≤ (2 / ε) * t := by
      rw [ht_def, ← sq_abs, ← ha, div_mul_div_comm, le_div_iff₀ (by positivity)]; nlinarith
    have hQw : |sInf A - w| ≤ n * K + a := by
      rw [abs_le]; constructor <;> linarith [le_abs_self w, neg_abs_le w]
    have h3 : (2 * K / ε + 1) * a ≤ (2 * K / ε + 1) * (2 / ε) * t := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hat (by positivity)
    have h4 : 0 ≤ (1 + 3 * c) * (1 + t) := by positivity
    have e : (1 + 3 * c + (2 * K / ε + 1) * (2 / ε)) * (1 + t) =
        (1 + 3 * c) * (1 + t) + (2 * K / ε + 1) * (2 / ε) + (2 * K / ε + 1) * (2 / ε) * t := by ring
    have e2 : (2 * K / ε) * a + a = (2 * K / ε + 1) * a := by ring
    rw [e]; linarith
