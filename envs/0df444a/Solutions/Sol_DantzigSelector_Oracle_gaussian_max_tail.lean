-- Prove2me | solution 1 for DantzigSelector.Oracle.gaussian_max_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:31:38.253559+00:00
-- url     : https://prove2.me/submissions/ac146f20-dbf6-4316-a66a-24bd51b7dc8d

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
lemma gmt1f_pdf_eq (y : ℝ) :
    gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]

open MeasureTheory ProbabilityTheory in
lemma gmt1f_pdf_tendsto :
    Filter.Tendsto (gaussianPDFReal 0 1) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [mul_zero] at h
  have hf : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
    funext y; rw [gmt1f_pdf_eq]; congr 2; ring
  rw [hf]
  exact h

open MeasureTheory ProbabilityTheory in
lemma gmt1f_pdf_deriv (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  have hf : gaussianPDFReal 0 1 = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
    funext y; rw [gmt1f_pdf_eq]; congr 2; ring
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  rw [hf]
  exact h2.congr_deriv (by ring)

open MeasureTheory ProbabilityTheory in
lemma gmt1f_tail (u : ℝ) (hu : 0 < u) :
    gaussianReal 0 1 (Set.Ioi u) ≤ ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  apply ENNReal.ofReal_le_ofReal
  have hderiv : ∀ v ∈ Set.Ici u, HasDerivAt (fun v => -gaussianPDFReal 0 1 v / u)
      (v / u * gaussianPDFReal 0 1 v) v := by
    intro v _
    exact ((gmt1f_pdf_deriv v).neg.div_const u).congr_deriv (by ring)
  have hpos : ∀ v ∈ Set.Ioi u, 0 ≤ v / u * gaussianPDFReal 0 1 v := by
    intro v hv
    exact mul_nonneg (div_nonneg (hu.trans hv).le hu.le) (gaussianPDFReal_nonneg _ _ _)
  have hlim : Filter.Tendsto (fun v => -gaussianPDFReal 0 1 v / u) Filter.atTop
      (nhds (-0 / u)) := (gmt1f_pdf_tendsto.neg).div_const u
  have hI := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  calc ∫ x in Set.Ioi u, gaussianPDFReal 0 1 x
      ≤ ∫ x in Set.Ioi u, x / u * gaussianPDFReal 0 1 x := by
        refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn hint
          measurableSet_Ioi (fun x hx => ?_)
        exact le_mul_of_one_le_left (gaussianPDFReal_nonneg _ _ _)
          ((one_le_div hu).2 (le_of_lt hx))
    _ = gaussianPDFReal 0 1 u / u := by rw [hI]; ring

open MeasureTheory ProbabilityTheory in
lemma gmt1f_abs_tail (u : ℝ) (hu : 0 < u) :
    gaussianReal 0 1 {x | u < |x|} ≤ 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
  have hset : {x : ℝ | u < |x|} = Set.Ioi u ∪ (fun x => -x) ⁻¹' Set.Ioi u := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_preimage]
    exact lt_abs
  rw [hset]
  refine (measure_union_le _ _).trans ?_
  have h2 : gaussianReal 0 1 ((fun x => -x) ⁻¹' Set.Ioi u) = gaussianReal 0 1 (Set.Ioi u) := by
    rw [← Measure.map_apply measurable_neg measurableSet_Ioi, gaussianReal_map_neg, neg_zero]
  rw [h2, two_mul]
  exact add_le_add (gmt1f_tail u hu) (gmt1f_tail u hu)

open MeasureTheory ProbabilityTheory in
lemma gmt1f_law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : Fin n → ℝ) (hc : ∑ i, c i ^ 2 = 1)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P) :
    P.map (fun ω => ∑ i, c i * z i ω) = gaussianReal 0 1 := by
  set Y : Fin n → Ω → ℝ := fun i ω => c i * z i ω with hY
  have hYlaw' : ∀ i, ∃ v : NNReal, (v : ℝ) = c i ^ 2 ∧ HasLaw (Y i) (gaussianReal 0 v) P := by
    intro i
    have h := gaussianReal_const_mul (hz i) (c i)
    rw [mul_zero] at h
    refine ⟨_, ?_, h⟩
    rw [NNReal.coe_mul, NNReal.coe_one, mul_one]; rfl
  choose v hv hYlaw using hYlaw'
  have hYind : iIndepFun Y P := hind.comp (fun i x => c i * x) (fun i => by fun_prop)
  have hG : HasGaussianLaw (fun ω => ∑ i, Y i ω) P :=
    hYind.hasGaussianLaw_fun_sum (fun i => (hYlaw i).hasGaussianLaw)
  have hmem : ∀ i, MemLp (Y i) 2 P := by
    intro i
    have h0 : MemLp id (2 : ENNReal) (P.map (Y i)) := by
      rw [(hYlaw i).map_eq]; exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hYlaw i).aemeasurable).1 h0
  have hmean : P[fun ω => ∑ i, Y i ω] = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable one_le_two)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [(hYlaw i).integral_eq, integral_id_gaussianReal]
  have hvar : Var[fun ω => ∑ i, Y i ω; P] = 1 := by
    have hfn : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by
      funext ω; simp [Finset.sum_apply]
    rw [hfn, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hYind.indepFun hij)]
    have : ∀ i, Var[Y i; P] = c i ^ 2 := by
      intro i
      rw [(hYlaw i).variance_eq, variance_id_gaussianReal, hv i]
    simp only [this]
    rw [hc]
  show P.map (fun ω => ∑ i, Y i ω) = gaussianReal 0 1
  rw [hG.map_eq_gaussianReal, hmean, hvar]
  simp

open MeasureTheory ProbabilityTheory CandesTao.Decoding DantzigSelector.Sparse in
theorem solution {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 1) P) (hind : iIndepFun z P)
    (u : ℝ) (hu : 0 < u) :
    P {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|} ≤
      ENNReal.ofReal
        (2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) / u) := by
  classical
  have hset : {ω | ∃ j : Fin p, u < |∑ i, X i j * z i ω|}
      = ⋃ j, {ω | u < |∑ i, X i j * z i ω|} := by
    ext ω; simp
  rw [hset]
  refine (measure_iUnion_fintype_le P _).trans ?_
  have hj : ∀ j, P {ω | u < |∑ i, X i j * z i ω|}
      ≤ 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) := by
    intro j
    have hc : ∑ i, X i j ^ 2 = 1 := by
      have h := hX j
      unfold l2Norm column at h
      rwa [Real.sqrt_eq_one] at h
    have hmap := gmt1f_law P (fun i => X i j) hc z hz hind
    have hae : AEMeasurable (fun ω => ∑ i, X i j * z i ω) P := by
      have := fun i => (hz i).aemeasurable
      fun_prop
    have hms : MeasurableSet {x : ℝ | u < |x|} :=
      measurableSet_lt measurable_const measurable_abs
    calc P {ω | u < |∑ i, X i j * z i ω|}
        = P.map (fun ω => ∑ i, X i j * z i ω) {x : ℝ | u < |x|} := by
          rw [Measure.map_apply_of_aemeasurable hae hms]; rfl
      _ = gaussianReal 0 1 {x : ℝ | u < |x|} := by rw [hmap]
      _ ≤ _ := gmt1f_abs_tail u hu
  calc ∑ j, P {ω | u < |∑ i, X i j * z i ω|}
      ≤ ∑ _j : Fin p, 2 * ENNReal.ofReal (gaussianPDFReal 0 1 u / u) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, gmt1f_pdf_eq]
      rw [show 2 * (p : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) / u
          = (p : ℝ) * (2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2) / u)) by ring]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
