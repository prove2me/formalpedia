-- Prove2me | solution 1 for BilateralProfitMHR.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:39:10.488894+00:00
-- url     : https://prove2.me/submissions/1ceeba5a-4e6f-421f-a69d-7caf60bcea0d

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model

open MeasureTheory Set
open scoped Topology

namespace BilateralProfitMHR
open BilateralProfit MechanismDesign.BilateralTrade

private noncomputable def densityLaw (f : ℝ → ℝ) (l u : ℝ) : Measure ℝ :=
  (volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal (f x))

private lemma densityLaw_Icc (f : ℝ → ℝ) {l u c d : ℝ}
    (hf : IntervalIntegrable f volume l u) (hl : l ≤ c) (hcd : c ≤ d) (hd : d ≤ u)
    (hpos : ∀ x ∈ Icc l u, 0 ≤ f x) :
    densityLaw f l u (Icc c d) = ENNReal.ofReal (∫ x in c..d, f x) := by
  have hlu : l ≤ u := hl.trans (hcd.trans hd)
  have hs : Icc c d ⊆ Icc l u := Icc_subset_Icc hl hd
  have hfi : IntegrableOn f (Icc c d) volume := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp
    exact hf.mono_set (by simpa [uIcc_of_le hcd, uIcc_of_le hlu] using hs)
  rw [densityLaw, withDensity_apply _ measurableSet_Icc,
    Measure.restrict_restrict_of_subset hs, ← ofReal_integral_eq_lintegral_ofReal hfi]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun x hx => hpos x (hs hx))

private lemma densityLaw_univ (f : ℝ → ℝ) {l u : ℝ} (hlu : l ≤ u)
    (hf : IntervalIntegrable f volume l u) (hpos : ∀ x ∈ Icc l u, 0 ≤ f x) :
    densityLaw f l u univ = ENNReal.ofReal (∫ x in l..u, f x) := by
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hlu).mp hf)]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlu]
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ hpos)

private lemma densityLaw_Iic (f : ℝ → ℝ) {l u p : ℝ}
    (hf : IntervalIntegrable f volume l u) (hp : p ∈ Icc l u)
    (hpos : ∀ x ∈ Icc l u, 0 ≤ f x) :
    densityLaw f l u (Iic p) = ENNReal.ofReal (∫ x in l..p, f x) := by
  rw [densityLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic p ∩ Icc l u = Icc l p := by ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]; grind
  rw [hset]
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hp.1).mp
    (hf.mono_set (by simpa [uIcc_of_le hp.1, uIcc_of_le (hp.1.trans hp.2)] using
      (Icc_subset_Icc (le_refl l) hp.2)))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp.1]
  · exact (ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all _ fun x hx => hpos x ⟨hx.1, hx.2.trans hp.2⟩)

private lemma densityLaw_Ici (f : ℝ → ℝ) {l u q : ℝ}
    (hf : IntervalIntegrable f volume l u) (hq : q ∈ Icc l u)
    (hpos : ∀ x ∈ Icc l u, 0 ≤ f x) :
    densityLaw f l u (Ici q) = ENNReal.ofReal (∫ x in q..u, f x) := by
  rw [densityLaw, withDensity_apply _ measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici q ∩ Icc l u = Icc q u := by ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; grind
  rw [hset]
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hq.2).mp
    (hf.mono_set (by simpa [uIcc_of_le hq.2, uIcc_of_le (hq.1.trans hq.2)] using
      (Icc_subset_Icc hq.1 (le_refl u))))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.2]
  · exact (ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all _ fun x hx => hpos x ⟨hq.1.trans hx.1, hx.2⟩)

private lemma prior_eq_prod (E : Environment) :
    E.prior = (densityLaw E.fS E.loS E.hiS).prod (densityLaw E.fB E.loB E.hiB) := by
  rw [densityLaw, densityLaw, prod_withDensity E.fS_measurable.ennreal_ofReal
    E.fB_measurable.ennreal_ofReal, Measure.prod_restrict, ← Measure.volume_eq_prod]
  unfold Environment.prior Environment.typeSpace
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  exact ENNReal.ofReal_mul (E.fS_pos z.1 hz.1).le

private lemma densityLaw_isProbability {f : ℝ → ℝ} {l u : ℝ} (hlu : l ≤ u)
    (hf : IntervalIntegrable f volume l u) (hpos : ∀ x ∈ Icc l u, 0 ≤ f x)
    (hint : ∫ x in l..u, f x = 1) : IsProbabilityMeasure (densityLaw f l u) := by
  constructor
  rw [densityLaw_univ f hlu hf hpos, hint, ENNReal.ofReal_one]

private lemma prior_isProbabilityMeasure (E : Environment) : IsProbabilityMeasure E.prior := by
  rw [prior_eq_prod]
  letI := densityLaw_isProbability E.loS_lt_hiS.le E.fS_intervalIntegrable
    (fun x hx => (E.fS_pos x hx).le) E.fS_integral
  letI := densityLaw_isProbability E.loB_lt_hiB.le E.fB_intervalIntegrable
    (fun x hx => (E.fB_pos x hx).le) E.fB_integral
  infer_instance

private lemma ptrade_nonneg (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade D a :=
  ENNReal.toReal_nonneg

private lemma ptrade_le_one (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (a : ℝ × ℝ) :
    Ptrade D a ≤ 1 := by
  unfold Ptrade
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one

private lemma mu_nonneg {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a.1 ≤ a.2) :
    0 ≤ muP D a := mul_nonneg (sub_nonneg.mpr ha) (ptrade_nonneg D a)

private lemma mu_le_ptrade {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a ∈ unitSq) :
    muP D a ≤ Ptrade D a := by
  unfold muP
  apply mul_le_of_le_one_left (ptrade_nonneg D a)
  rcases ha with ⟨ha, hb⟩
  linarith [ha.1, hb.2]

private lemma mu_le_one {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : muP D a ≤ 1 :=
  (mu_le_ptrade ha).trans (ptrade_le_one D a)

private lemma cdfS_intervalIntegrable (E : Environment) (hE : UnitSupport E) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) : IntervalIntegrable E.fS volume a b := by
  rcases hE with ⟨h0, h1, _, _⟩
  have hi := E.fS_intervalIntegrable
  rw [h0, h1] at hi
  apply hi.mono_set
  rw [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact uIcc_subset_Icc ha hb

private lemma cdfB_intervalIntegrable (E : Environment) (hE : UnitSupport E) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) : IntervalIntegrable E.fB volume a b := by
  rcases hE with ⟨_, _, h0, h1⟩
  have hi := E.fB_intervalIntegrable
  rw [h0, h1] at hi
  apply hi.mono_set
  rw [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact uIcc_subset_Icc ha hb

private lemma continuousOn_cdfS (E : Environment) (hE : UnitSupport E) :
    ContinuousOn E.cdfS (Icc 0 1) := by
  change ContinuousOn (fun x => ∫ t in E.loS..x, E.fS t) (Icc 0 1)
  have h := intervalIntegral.continuousOn_primitive_interval' E.fS_intervalIntegrable
    (show E.loS ∈ uIcc E.loS E.hiS from left_mem_uIcc)
  simpa [Environment.cdfS, uIcc_of_le E.loS_lt_hiS.le, hE.1, hE.2.1] using h

private lemma continuousOn_cdfB (E : Environment) (hE : UnitSupport E) :
    ContinuousOn E.cdfB (Icc 0 1) := by
  change ContinuousOn (fun x => ∫ t in E.loB..x, E.fB t) (Icc 0 1)
  have h := intervalIntegral.continuousOn_primitive_interval' E.fB_intervalIntegrable
    (show E.loB ∈ uIcc E.loB E.hiB from left_mem_uIcc)
  simpa [Environment.cdfB, uIcc_of_le E.loB_lt_hiB.le, hE.2.2.1, hE.2.2.2] using h

private lemma cdfS_pos (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Ioc 0 1) :
    0 < E.cdfS x := by
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (cdfS_intervalIntegrable E hE (by norm_num) ⟨hx.1.le, hx.2⟩) _ hx.1
  intro t ht
  apply E.fS_pos t
  simpa [hE.1, hE.2.1] using (show t ∈ Icc 0 1 from ⟨ht.1.le, ht.2.le.trans hx.2⟩)

private lemma tailB_eq_integral (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Icc 0 1) :
    1 - E.cdfB x = ∫ t in x..1, E.fB t := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (cdfB_intervalIntegrable E hE (a := 0) (b := x) (by norm_num) hx)
    (cdfB_intervalIntegrable E hE (a := x) (b := 1) hx (by norm_num))
  have htotal := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at htotal
  rw [htotal] at h
  simp only [Environment.cdfB, hE.2.2.1]
  linarith

private lemma tailB_pos (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Ico 0 1) :
    0 < 1 - E.cdfB x := by
  rw [tailB_eq_integral E hE ⟨hx.1, hx.2.le⟩]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (cdfB_intervalIntegrable E hE ⟨hx.1, hx.2.le⟩ (by norm_num)) _ hx.2
  intro t ht
  apply E.fB_pos t
  simpa [hE.2.2.1, hE.2.2.2] using (show t ∈ Icc 0 1 from ⟨hx.1.trans ht.1.le, ht.2.le⟩)

private lemma ptrade_factorization (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : Ptrade E.prior a = E.cdfS a.1 * (1 - E.cdfB a.2) := by
  letI := densityLaw_isProbability E.loB_lt_hiB.le E.fB_intervalIntegrable
    (fun x hx => (E.fB_pos x hx).le) E.fB_integral
  have hS : a.1 ∈ Icc E.loS E.hiS := by simpa [hE.1, hE.2.1] using ha.1
  have hB : a.2 ∈ Icc E.loB E.hiB := by simpa [hE.2.2.1, hE.2.2.2] using ha.2
  have hset : {v | Trades v a} = Iic a.1 ×ˢ Ici a.2 := rfl
  unfold Ptrade
  rw [prior_eq_prod, hset, Measure.prod_prod,
    densityLaw_Iic E.fS E.fS_intervalIntegrable hS (fun x hx => (E.fS_pos x hx).le),
    densityLaw_Ici E.fB E.fB_intervalIntegrable hB (fun x hx => (E.fB_pos x hx).le),
    ENNReal.toReal_mul]
  have hSp : 0 ≤ ∫ x in E.loS..a.1, E.fS x :=
    intervalIntegral.integral_nonneg hS.1 (fun x hx => (E.fS_pos x ⟨hx.1, hx.2.trans hS.2⟩).le)
  have hBp : 0 ≤ ∫ x in a.2..E.hiB, E.fB x :=
    intervalIntegral.integral_nonneg hB.2 (fun x hx => (E.fB_pos x ⟨hB.1.trans hx.1, hx.2⟩).le)
  rw [ENNReal.toReal_ofReal hSp, ENNReal.toReal_ofReal hBp, hE.2.2.2,
    ← tailB_eq_integral E hE ha.2]
  rfl

private lemma mu_factorization (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : muP E.prior a = (a.2 - a.1) * E.cdfS a.1 * (1 - E.cdfB a.2) := by
  rw [muP, ptrade_factorization E hE ha, mul_assoc]

private lemma intT_subset_unitSq : intT ⊆ unitSq := by
  intro a ha
  exact ⟨⟨ha.1.le, (ha.2.1.trans ha.2.2).le⟩, ⟨(ha.1.trans ha.2.1).le, ha.2.2.le⟩⟩

private lemma mu_pos (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ} (ha : a ∈ intT) :
    0 < muP E.prior a := by
  rw [mu_factorization E hE (intT_subset_unitSq ha)]
  exact mul_pos (mul_pos (sub_pos.mpr ha.2.1)
    (cdfS_pos E hE ⟨ha.1, (ha.2.1.trans ha.2.2).le⟩))
    (tailB_pos E hE ⟨(ha.1.trans ha.2.1).le, ha.2.2⟩)

private lemma continuousOn_mu (E : Environment) (hE : UnitSupport E) :
    ContinuousOn (muP E.prior) unitSq := by
  apply ContinuousOn.congr
    (((continuous_snd.sub continuous_fst).continuousOn.mul
      ((continuousOn_cdfS E hE).comp continuous_fst.continuousOn (fun a ha => ha.1))).mul
      (continuousOn_const.sub ((continuousOn_cdfB E hE).comp continuous_snd.continuousOn (fun a ha => ha.2))))
  intro a ha
  exact mu_factorization E hE ha

private lemma continuousOn_loss (E : Environment) (hE : UnitSupport E) :
    ContinuousOn (lossL E.prior) intT := by
  exact (((continuousOn_mu E hE).mono intT_subset_unitSq).log
    (fun a ha => (mu_pos E hE ha).ne')).neg

private lemma cdfS_mono (E : Environment) (hE : UnitSupport E) : MonotoneOn E.cdfS (Icc 0 1) := by
  intro x hx y hy hxy
  have hp := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t ht =>
    (E.fS_pos t (by simpa [hE.1, hE.2.1] using
      (show t ∈ Icc 0 1 from ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩))).le)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (cdfS_intervalIntegrable E hE (a := 0) (b := x) (by norm_num) hx)
    (cdfS_intervalIntegrable E hE hx hy)
  unfold Environment.cdfS
  rw [hE.1]
  linarith

private lemma cdfB_mono (E : Environment) (hE : UnitSupport E) : MonotoneOn E.cdfB (Icc 0 1) := by
  intro x hx y hy hxy
  have hp := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t ht =>
    (E.fB_pos t (by simpa [hE.2.2.1, hE.2.2.2] using
      (show t ∈ Icc 0 1 from ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩))).le)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (cdfB_intervalIntegrable E hE (a := 0) (b := x) (by norm_num) hx)
    (cdfB_intervalIntegrable E hE hx hy)
  unfold Environment.cdfB
  rw [hE.2.2.1]
  linarith

private lemma cdfS_nonneg (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Icc 0 1) :
    0 ≤ E.cdfS x := by
  have he : E.cdfS 0 = 0 := by simp [Environment.cdfS, hE.1]
  have h := cdfS_mono E hE (show (0:ℝ) ∈ Icc 0 1 by norm_num) hx hx.1
  rwa [he] at h

private lemma tailB_nonneg (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Icc 0 1) :
    0 ≤ 1 - E.cdfB x := by
  have he : E.cdfB 1 = 1 := by simpa [Environment.cdfB, hE.2.2.2] using E.fB_integral
  have h := cdfB_mono E hE hx (show (1:ℝ) ∈ Icc 0 1 by norm_num) hx.2
  rw [he] at h
  linarith

private lemma mu_zero_left (E : Environment) (hE : UnitSupport E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    muP E.prior (0,q) = 0 := by
  rw [mu_factorization E hE (show (0,q) ∈ unitSq from ⟨by norm_num, hq⟩)]
  simp [Environment.cdfS, hE.1]

private lemma mu_zero_right (E : Environment) (hE : UnitSupport E) {p : ℝ} (hp : p ∈ Icc 0 1) :
    muP E.prior (p,1) = 0 := by
  rw [mu_factorization E hE (show (p,1) ∈ unitSq from ⟨hp, by norm_num⟩)]
  have he : E.cdfB 1 = 1 := by simpa [Environment.cdfB, hE.2.2.2] using E.fB_integral
  simp [he]

private lemma mu_zero_diag (D : Measure (ℝ × ℝ)) (x : ℝ) : muP D (x,x) = 0 := by simp [muP]

private lemma ptrade_product (E : Environment) (hE : UnitSupport E) {x z y : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    Ptrade E.prior (x,z) * Ptrade E.prior (z,y) =
      Ptrade E.prior (x,y) * Ptrade E.prior (z,z) := by
  rw [ptrade_factorization E hE (a := (x,z)) ⟨hx,hz⟩, ptrade_factorization E hE (a := (z,y)) ⟨hz,hy⟩,
    ptrade_factorization E hE (a := (x,y)) ⟨hx,hy⟩, ptrade_factorization E hE (a := (z,z)) ⟨hz,hz⟩]
  ring

private lemma ptrade_le_center (E : Environment) (hE : UnitSupport E) {x z y : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) (hy : y ∈ Icc 0 1)
    (hxz : x ≤ z) (hzy : z ≤ y) :
    Ptrade E.prior (x,z) ≤ Ptrade E.prior (z,z) ∧
    Ptrade E.prior (z,y) ≤ Ptrade E.prior (z,z) ∧
    Ptrade E.prior (x,y) ≤ Ptrade E.prior (z,z) := by
  rw [ptrade_factorization E hE (a := (x,z)) ⟨hx,hz⟩, ptrade_factorization E hE (a := (z,y)) ⟨hz,hy⟩,
    ptrade_factorization E hE (a := (x,y)) ⟨hx,hy⟩, ptrade_factorization E hE (a := (z,z)) ⟨hz,hz⟩]
  have hs := cdfS_mono E hE hx hz hxz
  have hb := cdfB_mono E hE hz hy hzy
  have h1 := mul_le_mul_of_nonneg_right hs (tailB_nonneg E hE hz)
  have h2 := mul_le_mul_of_nonneg_left (show 1 - E.cdfB y ≤ 1 - E.cdfB z by linarith)
    (cdfS_nonneg E hE hz)
  refine ⟨h1, h2, ?_⟩
  exact (mul_le_mul_of_nonneg_right hs (tailB_nonneg E hE hy)).trans h2

private lemma mu_pos_iff_mem_intT (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : 0 < muP E.prior a ↔ a ∈ intT := by
  refine ⟨?_, mu_pos E hE⟩
  intro hpos
  have horder : a.1 < a.2 := by
    by_contra hh
    have hm : muP E.prior a ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hh)) (ptrade_nonneg _ _)
    linarith
  have hl : 0 < a.1 := by
    by_contra hh
    have he : a.1 = 0 := le_antisymm (le_of_not_gt hh) ha.1.1
    have hz := mu_zero_left E hE ha.2
    have hae : a = (0,a.2) := by ext <;> simp [he]
    rw [hae, hz] at hpos
    exact lt_irrefl _ hpos
  have hr : a.2 < 1 := by
    by_contra hh
    have he : a.2 = 1 := le_antisymm ha.2.2 (le_of_not_gt hh)
    have hz := mu_zero_right E hE ha.1
    have hae : a = (a.1,1) := by ext <;> simp [he]
    rw [hae, hz] at hpos
    exact lt_irrefl _ hpos
  exact ⟨hl,horder,hr⟩

private lemma muStar_bddAbove (E : Environment) : BddAbove (muP E.prior '' unitSq) := by
  letI := prior_isProbabilityMeasure E
  refine ⟨1, ?_⟩
  rintro y ⟨a, ha, rfl⟩
  exact mu_le_one ha

private lemma mu_le_muStar (E : Environment) {a : ℝ × ℝ} (ha : a ∈ unitSq) :
    muP E.prior a ≤ muStar E.prior := le_csSup (muStar_bddAbove E) ⟨a,ha,rfl⟩

private lemma muStar_pos (E : Environment) (hE : UnitSupport E) : 0 < muStar E.prior := by
  have ha : ((1/3:ℝ),(2/3:ℝ)) ∈ intT := by norm_num [intT]
  exact (mu_pos E hE ha).trans_le (mu_le_muStar E (intT_subset_unitSq ha))

private lemma muStar_le_one (E : Environment) : muStar E.prior ≤ 1 := by
  letI := prior_isProbabilityMeasure E
  apply csSup_le (Set.Nonempty.image _ ?_)
  · rintro y ⟨a, ha, rfl⟩
    exact mu_le_one ha
  · exact ⟨(0,0), by norm_num [unitSq]⟩

private lemma exists_muStar (E : Environment) (hE : UnitSupport E) :
    ∃ a ∈ intT, muP E.prior a = muStar E.prior := by
  have hcompact : IsCompact unitSq := isCompact_Icc.prod isCompact_Icc
  have hne : unitSq.Nonempty := ⟨(0,0), by norm_num [unitSq]⟩
  obtain ⟨a, ha, hmax⟩ := hcompact.exists_isMaxOn hne (continuousOn_mu E hE)
  have he : muP E.prior a = muStar E.prior := by
    apply le_antisymm (mu_le_muStar E ha)
    apply csSup_le (hne.image _)
    rintro y ⟨b,hb,rfl⟩
    exact hmax hb
  exact ⟨a, (mu_pos_iff_mem_intT E hE ha).mp (he.symm ▸ muStar_pos E hE), he⟩

private lemma sub_le_mul_log_sub {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u - v ≤ u * (Real.log u - Real.log v) := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hu.le
  have he : u * (v / u - 1) = v - u := by field_simp
  rw [he] at hmul
  nlinarith

private lemma loss_gap_nonneg (D : Measure (ℝ × ℝ)) {a b : ℝ × ℝ}
    (ha : 0 < muP D a) (hab : muP D a ≤ muP D b) :
    0 ≤ lossL D a - lossL D b := by
  have hlog := Real.log_le_log ha hab
  unfold lossL
  linarith

private lemma profit_gap_le_loss_gap (D : Measure (ℝ × ℝ)) {a b : ℝ × ℝ}
    (ha : 0 < muP D a) (hb : 0 < muP D b) :
    muP D b - muP D a ≤ muP D b * (lossL D a - lossL D b) := by
  have h := sub_le_mul_log_sub hb ha
  simpa only [lossL, sub_neg_eq_add, neg_add_eq_sub, add_comm] using h

private lemma profit_gap_le_muStar_loss_gap (E : Environment) (hE : UnitSupport E)
    {a b : ℝ × ℝ} (ha : a ∈ intT) (hb : b ∈ intT) (hab : muP E.prior a ≤ muP E.prior b) :
    muP E.prior b - muP E.prior a ≤ muStar E.prior * (lossL E.prior a - lossL E.prior b) := by
  exact (profit_gap_le_loss_gap E.prior (mu_pos E hE ha) (mu_pos E hE hb)).trans
    (mul_le_mul_of_nonneg_right (mu_le_muStar E (intT_subset_unitSq hb))
      (loss_gap_nonneg E.prior (mu_pos E hE ha) hab))

end BilateralProfitMHR


open MeasureTheory Set Filter
open scoped Topology NNReal

namespace BilateralProfitMHR

private lemma ac_comp_lipschitzOn {f g : ℝ → ℝ} {a b : ℝ} {s : Set ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g s)
    (hm : MapsTo f (uIcc a b) s) : AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := hf (ε / ((K : ℝ) + 1)) (div_pos hε (by positivity))
  refine ⟨δ,hδ,fun E hE hsmall => ?_⟩
  have hdist := hfδ E hE hsmall
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hbound : (∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))) ≤
      (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply hg.dist_le_mul
    · exact hm (hE.1 i hi).1
    · exact hm (hE.1 i hi).2
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) :=
    Finset.sum_nonneg (fun _ _ => dist_nonneg)
  apply hbound.trans_lt
  have := (mul_lt_mul_of_pos_left hdist (show 0 < (K : ℝ) + 1 by positivity))
  have he : ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) = ε := by field_simp
  rw [he] at this
  linarith

private lemma log_lipschitzOn_Ici {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ Real.log (Ici c) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ici c)
    (fun x hx => (Real.hasDerivAt_log (hc.trans_le hx).ne').hasDerivWithinAt)
  intro x hx
  change |x⁻¹| ≤ c⁻¹
  rw [abs_of_pos (inv_pos.mpr (hc.trans_le hx))]
  exact inv_anti₀ hc hx

private lemma ac_log {f : ℝ → ℝ} {a b c : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hc : 0 < c) (hfc : ∀ x ∈ uIcc a b, c ≤ f x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (f x)) a b :=
  ac_comp_lipschitzOn hf (log_lipschitzOn_Ici hc) hfc

private lemma ac_log_of_pos {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < f x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (f x)) a b := by
  obtain ⟨c,hc,hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  exact ac_log hf (hpos c hc) (fun x hx => hmin hx)

private lemma convexOn_of_ac_monotone_ae_deriv {s : Set ℝ} {f g : ℝ → ℝ}
    (hs : Convex ℝ s) (hac : ∀ x ∈ s, ∀ z ∈ s, AbsolutelyContinuousOnInterval f x z)
    (hg : MonotoneOn g s) (hd : ∀ᵐ t, t ∈ s → HasDerivAt f (g t) t) : ConvexOn ℝ s f := by
  apply convexOn_of_slope_mono_adjacent hs
  intro x y z hx hz hxy hyz
  have hy : y ∈ s := hs.ordConnected.out hx hz ⟨hxy.le,hyz.le⟩
  have hxyac := hac x hx y hy
  have hyzac := hac y hy z hz
  have hsxy : Icc x y ⊆ s := hs.ordConnected.out hx hy
  have hsyz : Icc y z ⊆ s := hs.ordConnected.out hy hz
  have hleft : ∫ t in x..y, deriv f t ≤ ∫ _ in x..y, g y := by
    apply intervalIntegral.integral_mono_ae_restrict hxy.le hxyac.intervalIntegrable_deriv intervalIntegrable_const
    simp only [Filter.EventuallyLE]
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hd] with t ht htx
    rw [(ht (hsxy htx)).deriv]
    exact hg (hsxy htx) hy htx.2
  have hright : ∫ _ in y..z, g y ≤ ∫ t in y..z, deriv f t := by
    apply intervalIntegral.integral_mono_ae_restrict hyz.le intervalIntegrable_const hyzac.intervalIntegrable_deriv
    simp only [Filter.EventuallyLE]
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hd] with t ht htz
    rw [(ht (hsyz htz)).deriv]
    exact hg hy (hsyz htz) htz.1
  rw [hxyac.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hleft
  rw [hyzac.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hright
  have hl : (f y - f x) / (y - x) ≤ g y :=
    (div_le_iff₀ (sub_pos.mpr hxy)).mpr (by nlinarith)
  have hr : g y ≤ (f z - f y) / (z - y) :=
    (le_div_iff₀ (sub_pos.mpr hyz)).mpr (by nlinarith)
  exact hl.trans hr

end BilateralProfitMHR


open MeasureTheory Set Filter
open scoped Topology NNReal

namespace BilateralProfitMHR
open BilateralProfit MechanismDesign.BilateralTrade

private lemma cdfS_ac (E : Environment) (hE : UnitSupport E) {x z : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) : AbsolutelyContinuousOnInterval E.cdfS x z := by
  have h := E.fS_intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (c := E.loS) left_mem_uIcc
  apply h.mono
  simpa [uIcc_of_le E.loS_lt_hiS.le, hE.1, hE.2.1] using uIcc_subset_Icc hx hz

private lemma cdfB_ac (E : Environment) (hE : UnitSupport E) {x z : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) : AbsolutelyContinuousOnInterval E.cdfB x z := by
  have h := E.fB_intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (c := E.loB) left_mem_uIcc
  apply h.mono
  simpa [uIcc_of_le E.loB_lt_hiB.le, hE.2.2.1, hE.2.2.2] using uIcc_subset_Icc hx hz

private lemma cdfS_ae_hasDerivAt (E : Environment) (hE : UnitSupport E) :
    ∀ᵐ t, t ∈ Icc 0 1 → HasDerivAt E.cdfS (E.fS t) t := by
  filter_upwards [E.fS_intervalIntegrable.ae_hasDerivAt_integral] with t ht hmem
  apply ht
  · simpa [uIcc_of_le E.loS_lt_hiS.le, hE.1, hE.2.1] using hmem
  · exact left_mem_uIcc

private lemma cdfB_ae_hasDerivAt (E : Environment) (hE : UnitSupport E) :
    ∀ᵐ t, t ∈ Icc 0 1 → HasDerivAt E.cdfB (E.fB t) t := by
  filter_upwards [E.fB_intervalIntegrable.ae_hasDerivAt_integral] with t ht hmem
  apply ht
  · simpa [uIcc_of_le E.loB_lt_hiB.le, hE.2.2.1, hE.2.2.2] using hmem
  · exact left_mem_uIcc

private lemma convexOn_neg_log_cdfS (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ConvexOn ℝ (Ioo 0 1) (fun x => -Real.log (E.cdfS x)) := by
  apply convexOn_of_ac_monotone_ae_deriv (g := fun x => -(E.fS x / E.cdfS x)) (convex_Ioo 0 1)
  · intro x hx z hz
    apply AbsolutelyContinuousOnInterval.neg
    apply ac_log_of_pos (cdfS_ac E hE ⟨hx.1.le,hx.2.le⟩ ⟨hz.1.le,hz.2.le⟩)
    intro t ht
    have hsub : uIcc x z ⊆ Ioo (0:ℝ) 1 := (convex_Ioo (0:ℝ) 1).ordConnected.uIcc_subset hx hz
    exact cdfS_pos E hE ⟨(hsub ht).1, (hsub ht).2.le⟩
  · exact (hM.1.mono Ioo_subset_Ioc_self).neg
  · filter_upwards [cdfS_ae_hasDerivAt E hE] with t ht hmem
    exact ((ht ⟨hmem.1.le,hmem.2.le⟩).log
      (cdfS_pos E hE ⟨hmem.1,hmem.2.le⟩).ne').neg

private lemma convexOn_neg_log_tailB (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ConvexOn ℝ (Ioo 0 1) (fun x => -Real.log (1 - E.cdfB x)) := by
  apply convexOn_of_ac_monotone_ae_deriv (g := fun x => E.fB x / (1 - E.cdfB x)) (convex_Ioo 0 1)
  · intro x hx z hz
    apply AbsolutelyContinuousOnInterval.neg
    apply ac_log_of_pos
    · exact ((LipschitzWith.const (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval).sub
        (cdfB_ac E hE ⟨hx.1.le,hx.2.le⟩ ⟨hz.1.le,hz.2.le⟩)
    · intro t ht
      have hsub : uIcc x z ⊆ Ioo (0:ℝ) 1 := (convex_Ioo (0:ℝ) 1).ordConnected.uIcc_subset hx hz
      exact tailB_pos E hE ⟨(hsub ht).1.le,(hsub ht).2⟩
  · exact hM.2.mono Ioo_subset_Ico_self
  · filter_upwards [cdfB_ae_hasDerivAt E hE] with t ht hmem
    convert! (((ht ⟨hmem.1.le,hmem.2.le⟩).const_sub 1).log
      (tailB_pos E hE ⟨hmem.1.le,hmem.2⟩).ne').neg using 1 <;> simp only [neg_div, neg_neg]

private lemma convex_intT : Convex ℝ intT := by
  let fstL : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ
  let sndL : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
  have h := ((convex_Ioi (0:ℝ)).linear_preimage fstL).inter
    (((convex_Ioi (0:ℝ)).linear_preimage (sndL - fstL)).inter
      ((convex_Iio (1:ℝ)).linear_preimage sndL))
  convert! h using 1
  ext a
  simp only [intT, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, mem_Iio,
    LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, fstL, sndL]
  constructor <;> intro ha <;> rcases ha with ⟨h1,h2,h3⟩ <;> exact ⟨h1,by linarith,h3⟩

private lemma loss_eq_sum (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ} (ha : a ∈ intT) :
    lossL E.prior a = -Real.log (a.2 - a.1) - Real.log (E.cdfS a.1) -
      Real.log (1 - E.cdfB a.2) := by
  have hp := cdfS_pos E hE ⟨ha.1, (ha.2.1.trans ha.2.2).le⟩
  have hq := tailB_pos E hE ⟨(ha.1.trans ha.2.1).le, ha.2.2⟩
  unfold lossL
  rw [mu_factorization E hE (intT_subset_unitSq ha),
    Real.log_mul (mul_pos (sub_pos.mpr ha.2.1) hp).ne' hq.ne',
    Real.log_mul (sub_pos.mpr ha.2.1).ne' hp.ne']
  ring

private lemma convexOn_loss (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ConvexOn ℝ intT (lossL E.prior) := by
  let fstL : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ
  let sndL : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ
  have hgap := (strictConcaveOn_log_Ioi.concaveOn.neg.comp_linearMap (sndL - fstL)).subset
    (show intT ⊆ (sndL - fstL) ⁻¹' Ioi (0:ℝ) from fun a ha => sub_pos.mpr ha.2.1) convex_intT
  have hS := ((convexOn_neg_log_cdfS E hE hM).comp_linearMap fstL).subset
    (show intT ⊆ fstL ⁻¹' Ioo (0:ℝ) 1 from fun a ha => ⟨ha.1,ha.2.1.trans ha.2.2⟩) convex_intT
  have hB := ((convexOn_neg_log_tailB E hE hM).comp_linearMap sndL).subset
    (show intT ⊆ sndL ⁻¹' Ioo (0:ℝ) 1 from fun a ha => ⟨ha.1.trans ha.2.1,ha.2.2⟩) convex_intT
  apply (hgap.add hS |>.add hB).congr
  intro a ha
  simp only [Pi.add_apply, Function.comp_apply, LinearMap.sub_apply, fstL, sndL,
    LinearMap.fst_apply, LinearMap.snd_apply, Pi.neg_apply]
  rw [loss_eq_sum E hE ha]
  ring

private lemma profit_superlevel_convex (E : Environment) (hE : UnitSupport E) (hM : IsMHR E)
    {c : ℝ} (hc : 0 < c) : Convex ℝ {a ∈ intT | c ≤ muP E.prior a} := by
  have h := (convexOn_loss E hE hM).convex_le (-Real.log c)
  convert! h using 1
  ext a
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨ha,hcμ⟩
    refine ⟨ha, ?_⟩
    change -Real.log (muP E.prior a) ≤ -Real.log c
    exact neg_le_neg ((Real.log_le_log_iff hc (mu_pos E hE ha)).mpr hcμ)
  · rintro ⟨ha,hL⟩
    refine ⟨ha, ?_⟩
    change -Real.log (muP E.prior a) ≤ -Real.log c at hL
    exact (Real.log_le_log_iff hc (mu_pos E hE ha)).mp (neg_le_neg_iff.mp hL)

private lemma proposition_3_2_proved (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ContinuousOn (lossL E.prior) intT ∧ ConvexOn ℝ intT (lossL E.prior) :=
  ⟨continuousOn_loss E hE, convexOn_loss E hE hM⟩

end BilateralProfitMHR

open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

theorem solution (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    ContinuousOn (lossL E.prior) intT ∧ ConvexOn ℝ intT (lossL E.prior) :=
  BilateralProfitMHR.proposition_3_2_proved E hE hM

