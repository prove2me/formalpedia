-- Prove2me | solution 1 for ChanceStateCtrl.General.eq_17_19_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:23:19.748061+00:00
-- url     : https://prove2.me/submissions/2644f742-90a0-4e1a-94d6-e90c86ff0b05

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped MatrixOrder Pointwise

namespace A3S48RD
open ChanceStateCtrl.General

lemma chi_Iio (m : ℕ) : chiLaw m (Iio 0) = 0 := by
  rw [chiLaw, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
    (fun t ht => by simp [chiDensity, not_le.2 (show t < 0 from ht)])]
  simp

lemma chi_Icc_eq_Iic (m : ℕ) {s : ℝ} (hs : 0 ≤ s) : chiLaw m (Icc 0 s) = chiLaw m (Iic s) := by
  refine le_antisymm (measure_mono Icc_subset_Iic_self) ?_
  calc chiLaw m (Iic s) ≤ chiLaw m (Iio 0 ∪ Icc 0 s) := by
        refine measure_mono fun t ht => ?_
        by_cases h : t < 0
        · exact Or.inl h
        · exact Or.inr ⟨not_lt.1 h, ht⟩
    _ ≤ chiLaw m (Iio 0) + chiLaw m (Icc 0 s) := measure_union_le _ _
    _ = chiLaw m (Icc 0 s) := by rw [chi_Iio, zero_add]

lemma chi_Ici (m : ℕ) : chiLaw m (Ici 0) = 1 := by
  set f : ℝ → ℝ := fun t => t ^ (m - 1) * Real.exp (-t ^ 2 / 2) with hf
  have hfi : IntegrableOn f (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)
      (s := ((m - 1 : ℕ) : ℝ))
      (by have : (0:ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [hf, Real.rpow_natCast]
    congr 2; ring
  have hfpos : ∀ t ∈ Ioi (0:ℝ), 0 < f t := fun t ht => by
    have : (0:ℝ) < t := ht
    positivity
  have hI : 0 < ∫ t in Ioi (0:ℝ), f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => (hfpos t ht).le)) hfi]
    have : Function.support f ∩ Ioi 0 = Ioi 0 := by
      ext t; constructor
      · exact fun h => h.2
      · exact fun h => ⟨(hfpos t h).ne', h⟩
    rw [this]; simp
  have hK : chiConst m = (∫ t in Ioi (0:ℝ), f t)⁻¹ := rfl
  rw [chiLaw, withDensity_apply _ measurableSet_Ici,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun t => ENNReal.ofReal (chiConst m * f t))
    (fun t ht => by simp [chiDensity, le_of_lt (show (0:ℝ) < t from ht), hf, mul_assoc])]
  rw [← ofReal_integral_eq_lintegral_ofReal (hfi.const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
      mul_nonneg (by rw [hK]; exact (inv_pos.2 hI).le) (hfpos t ht).le))]
  rw [integral_const_mul, hK, inv_mul_cancel₀ hI.ne', ENNReal.ofReal_one]

end A3S48RD

open A3S48RD ChanceStateCtrl.General in
theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (u : U) (hu : g u 0 < 0) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    (radius Sigma g u v < ⊤ →
      {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} =
          Set.Icc 0 (radius Sigma g u v).toReal ∧
        g u ((radius Sigma g u v).toReal • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) = 0 ∧
        (∀ r : ℝ, 0 ≤ r → g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) = 0 →
          r = (radius Sigma g u v).toReal) ∧
        radialProb Sigma g u v = chiCDF m (radius Sigma g u v).toReal) ∧
    (radius Sigma g u v = ⊤ →
      {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} = Set.Ici 0 ∧
        radialProb Sigma g u v = 1) := by
  set w := sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))
  set ψ : ℝ → ℝ := fun r => g u (r • w) with hψ
  set A : Set ℝ := {r : ℝ | 0 ≤ r ∧ g u (r • w) ≤ 0} with hAdef
  have hψc : Continuous ψ := by
    have := hA.locLip.continuous
    exact this.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
  have hψ0 : ψ 0 < 0 := by simpa [hψ] using hu
  have hconv : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ψ (a * x + b * y) ≤ a * ψ x + b * ψ y := by
    intro x y a b ha hb hab
    have := (hA.convex_snd u).2 (mem_univ (x • w)) (mem_univ (y • w)) ha hb hab
    simp only [smul_eq_mul, smul_smul] at this
    simpa [hψ, add_smul, mul_smul] using this
  have hmid : ∀ r ∈ A, ∀ s, 0 ≤ s → s < r → ψ s < 0 := by
    intro r hr s hs hsr
    have hr0 : 0 < r := lt_of_le_of_lt hs hsr
    have := hconv 0 r (1 - s / r) (s / r) (by rw [sub_nonneg, div_le_one hr0]; exact hsr.le)
      (by positivity) (by ring)
    have e : (1 - s / r) * 0 + s / r * r = s := by field_simp; ring
    rw [e] at this
    have h1 : 0 < 1 - s / r := by rw [sub_pos, div_lt_one hr0]; exact hsr
    have h2 : s / r * ψ r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hr.2
    nlinarith
  have hint : ∀ r ∈ A, ∀ s, 0 ≤ s → s ≤ r → s ∈ A := by
    intro r hr s hs hsr
    rcases hsr.lt_or_eq with h | h
    · exact ⟨hs, (hmid r hr s hs h).le⟩
    · exact h ▸ hr
  have h0A : (0:ℝ) ∈ A := ⟨le_rfl, hψ0.le⟩
  have hAclosed : IsClosed A :=
    isClosed_le continuous_const continuous_id |>.inter (isClosed_le hψc continuous_const)
  have hrad : radius Sigma g u v = ⨆ r ∈ A, ENNReal.ofReal r := rfl
  have hle_rad : ∀ r ∈ A, ENNReal.ofReal r ≤ radius Sigma g u v := fun r hr => by
    rw [hrad]; exact le_iSup₂ (f := fun r (_ : r ∈ A) => ENNReal.ofReal r) r hr
  constructor
  · intro hlt
    have hbdd : BddAbove A := ⟨(radius Sigma g u v).toReal, fun r hr =>
      (ENNReal.ofReal_le_iff_le_toReal hlt.ne).1 (hle_rad r hr)⟩
    set s := sSup A
    have hsA : s ∈ A := hAclosed.csSup_mem ⟨0, h0A⟩ hbdd
    have hs0 : 0 ≤ s := hsA.1
    have hrs : radius Sigma g u v = ENNReal.ofReal s := by
      refine le_antisymm ?_ (hle_rad s hsA)
      rw [hrad]; exact iSup₂_le fun r hr => ENNReal.ofReal_le_ofReal (le_csSup hbdd hr)
    rw [hrs, ENNReal.toReal_ofReal hs0]
    have hset : A = Icc 0 s := by
      ext r; constructor
      · intro hr; exact ⟨hr.1, le_csSup hbdd hr⟩
      · intro hr; exact hint s hsA r hr.1 hr.2
    refine ⟨hset, ?_, ?_, ?_⟩
    · refine le_antisymm hsA.2 (not_lt.1 fun hneg => ?_)
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
        (hψc.continuousAt.eventually (gt_mem_nhds hneg))
      have hy : s + δ / 2 ∈ A := ⟨by positivity, (hball (by
        rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)).le⟩
      have := le_csSup hbdd hy
      linarith
    · intro r hr0 hr
      have hrA : r ∈ A := ⟨hr0, hr.le⟩
      refine le_antisymm (le_csSup hbdd hrA) (not_lt.1 fun hlt' => ?_)
      have := hmid s hsA r hr0 hlt'
      simp only [hψ] at this
      linarith
    · simp only [radialProb, chiCDF]
      show (chiLaw m A).toReal = _
      rw [hset, chi_Icc_eq_Iic m hs0]
  · intro htop
    have hset : A = Ici 0 := by
      ext r; constructor
      · intro hr; exact hr.1
      · intro hr
        by_contra hnot
        have hbd : ∀ r' ∈ A, r' ≤ r := fun r' hr' => by
          by_contra hgt
          exact hnot (hint r' hr' r hr (not_le.1 hgt).le)
        have : radius Sigma g u v ≤ ENNReal.ofReal r := by
          rw [hrad]; exact iSup₂_le fun r' hr' => ENNReal.ofReal_le_ofReal (hbd r' hr')
        rw [htop] at this
        exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
    refine ⟨hset, ?_⟩
    simp only [radialProb]
    show (chiLaw m A).toReal = 1
    rw [hset, chi_Ici, ENNReal.toReal_one]
