-- Prove2me | solution 1 for CompOT.NotHilbertian.proposition_8_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T04:19:41.889358+00:00
-- url     : https://prove2.me/submissions/769b1913-ae58-47d6-9243-a068561a493d

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

set_option autoImplicit false

open MeasureTheory

namespace CompOT.NotHilbertian.P8ab0ad33

open CompOT.NotHilbertian

/-- The two-point measure `(δ_x + δ_y) / 2`. -/
noncomputable def tp {d : ℕ} (x y : E d) : Measure (E d) :=
  (2⁻¹ : ENNReal) • Measure.dirac x + (2⁻¹ : ENNReal) • Measure.dirac y

lemma tp_comm {d : ℕ} (x y : E d) : tp x y = tp y x := add_comm _ _

lemma tp_univ {d : ℕ} (x y : E d) : tp x y Set.univ = 1 := by
  simp [tp, ENNReal.inv_two_add_inv_two]

lemma tp_ae {d : ℕ} (x y : E d) : ∀ᵐ z ∂(tp x y), z = x ∨ z = y := by
  rw [ae_iff]
  simp [tp, Measure.dirac_apply]

lemma tp_mem {d : ℕ} (p : ℝ) (x y : E d) : tp x y ∈ Pp d p := by
  refine ⟨⟨tp_univ x y⟩, ?_⟩
  rw [tp, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]
  simp [ENNReal.add_lt_top, ENNReal.mul_lt_top]

lemma rpow_back {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) :
    (ENNReal.ofReal (c ^ p)) ^ (1 / p) = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul hc,
    mul_one_div_cancel hp.ne', Real.rpow_one]

lemma lower {d : ℕ} {p : ℝ} (hp : 0 < p) {x1 x2 y1 y2 : E d} {c : ℝ} (hc : 0 ≤ c)
    (h11 : c ≤ ‖x1 - y1‖) (h12 : c ≤ ‖x1 - y2‖) (h21 : c ≤ ‖x2 - y1‖)
    (h22 : c ≤ ‖x2 - y2‖) :
    ENNReal.ofReal c ≤ WassersteinDRO.Duality.wassersteinDistance p (tp x1 x2) (tp y1 y2) := by
  unfold WassersteinDRO.Duality.wassersteinDistance
  have key : ENNReal.ofReal (c ^ p) ≤ ⨅ (π : Measure (E d × E d))
      (_ : π.map Prod.fst = tp x1 x2 ∧ π.map Prod.snd = tp y1 y2),
      ∫⁻ x : E d × E d, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π := by
    refine le_iInf₂ fun π hπ => ?_
    have hS : ∀ᵐ z ∂π, z.1 = x1 ∨ z.1 = x2 :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact tp_ae x1 x2)
    have hT : ∀ᵐ z ∂π, z.2 = y1 ∨ z.2 = y2 :=
      ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact tp_ae y1 y2)
    have huniv : π Set.univ = 1 := by
      have h := congrArg (fun m : Measure (E d) => m Set.univ) hπ.1
      simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
      rw [h, tp_univ]
    calc ENNReal.ofReal (c ^ p) = ∫⁻ _ : E d × E d, ENNReal.ofReal (c ^ p) ∂π := by
          simp [huniv]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hS, hT] with z h1 h2
          apply ENNReal.ofReal_le_ofReal
          apply Real.rpow_le_rpow hc _ hp.le
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> assumption
  calc ENNReal.ofReal c = (ENNReal.ofReal (c ^ p)) ^ (1 / p) := (rpow_back hp hc).symm
    _ ≤ _ := ENNReal.rpow_le_rpow key (by positivity)

lemma upper {d : ℕ} {p : ℝ} (hp : 0 < p) {x1 x2 y1 y2 : E d} {r : ℝ} (hr : 0 ≤ r)
    (h1 : ‖x1 - y1‖ ≤ r) (h2 : ‖x2 - y2‖ ≤ r) :
    WassersteinDRO.Duality.wassersteinDistance p (tp x1 x2) (tp y1 y2) ≤ ENNReal.ofReal r := by
  unfold WassersteinDRO.Duality.wassersteinDistance
  set π : Measure (E d × E d) :=
    (2⁻¹ : ENNReal) • Measure.dirac (x1, y1) + (2⁻¹ : ENNReal) • Measure.dirac (x2, y2) with hπdef
  have hm : π.map Prod.fst = tp x1 x2 ∧ π.map Prod.snd = tp y1 y2 := by
    constructor
    · rw [hπdef, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
      rfl
    · rw [hπdef, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd]
      rfl
  have a1 : ENNReal.ofReal (‖x1 - y1‖ ^ p) ≤ ENNReal.ofReal (r ^ p) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) h1 hp.le)
  have a2 : ENNReal.ofReal (‖x2 - y2‖ ^ p) ≤ ENNReal.ofReal (r ^ p) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) h2 hp.le)
  have hcost : ∫⁻ x : E d × E d, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π ≤ ENNReal.ofReal (r ^ p) := by
    rw [hπdef, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac]
    calc (2⁻¹ : ENNReal) • ENNReal.ofReal (‖(x1, y1).1 - (x1, y1).2‖ ^ p)
          + (2⁻¹ : ENNReal) • ENNReal.ofReal (‖(x2, y2).1 - (x2, y2).2‖ ^ p)
        ≤ (2⁻¹ : ENNReal) * ENNReal.ofReal (r ^ p) + (2⁻¹ : ENNReal) * ENNReal.ofReal (r ^ p) := by
          simp only [smul_eq_mul]
          gcongr
      _ = ENNReal.ofReal (r ^ p) := by rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  calc (⨅ (π : Measure (E d × E d))
        (_ : π.map Prod.fst = tp x1 x2 ∧ π.map Prod.snd = tp y1 y2),
        ∫⁻ x : E d × E d, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p)
      ≤ (ENNReal.ofReal (r ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow ((iInf₂_le π hm).trans hcost) (by positivity)
    _ = ENNReal.ofReal r := rpow_back hp hr

lemma nb {d : ℕ} (i j : Fin d) (a b : ℝ) :
    ‖a • EuclideanSpace.single i (1 : ℝ) + b • EuclideanSpace.single j (1 : ℝ)‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  simp [norm_smul, EuclideanSpace.norm_single]

lemma coord_le {d : ℕ} (v : E d) (i : Fin d) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

end CompOT.NotHilbertian.P8ab0ad33

set_option maxHeartbeats 1000000 in
open CompOT.NotHilbertian in
theorem solution (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ¬ IsHilbertian (Wp d p) := by
  have hp0 : 0 < p := by rcases hp with h | h <;> rw [h] <;> norm_num
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set e0 : E d := EuclideanSpace.single i0 (1 : ℝ) with he0
  set e1 : E d := EuclideanSpace.single i1 (1 : ℝ) with he1
  have c00 : e0 i0 = 1 := by simp [e0]
  have c01 : e0 i1 = 0 := by simp [e0, hne.symm]
  have c10 : e1 i0 = 0 := by simp [e1, hne]
  have c11 : e1 i1 = 1 := by simp [e1]
  let A : Pp d p := ⟨P8ab0ad33.tp 0 (e0 + e1), P8ab0ad33.tp_mem p _ _⟩
  let B : Pp d p := ⟨P8ab0ad33.tp e0 e1, P8ab0ad33.tp_mem p _ _⟩
  let M1 : Pp d p := ⟨P8ab0ad33.tp ((1 / 2 : ℝ) • e0) ((1 / 2 : ℝ) • e0 + e1), P8ab0ad33.tp_mem p _ _⟩
  let M2 : Pp d p := ⟨P8ab0ad33.tp ((1 / 2 : ℝ) • e1) (e0 + (1 / 2 : ℝ) • e1), P8ab0ad33.tp_mem p _ _⟩
  -- upper bounds
  have uAM1 : Wp d p A M1 ≤ 1 / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) (P8ab0ad33.upper hp0 (by norm_num) ?_ ?_)
    · rw [show (0 : E d) - (1 / 2 : ℝ) • e0 = (-(1 / 2) : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
    · rw [show (e0 + e1) - ((1 / 2 : ℝ) • e0 + e1) = (1 / 2 : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
  have uM1B : Wp d p M1 B ≤ 1 / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) (P8ab0ad33.upper hp0 (by norm_num) ?_ ?_)
    · rw [show (1 / 2 : ℝ) • e0 - e0 = (-(1 / 2) : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
    · rw [show ((1 / 2 : ℝ) • e0 + e1) - e1 = (1 / 2 : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
  have uAM2 : Wp d p A M2 ≤ 1 / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) (P8ab0ad33.upper hp0 (by norm_num) ?_ ?_)
    · rw [show (0 : E d) - (1 / 2 : ℝ) • e1 = (0 : ℝ) • e0 + (-(1 / 2) : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
    · rw [show (e0 + e1) - (e0 + (1 / 2 : ℝ) • e1) = (0 : ℝ) • e0 + (1 / 2 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
  have uM2B : Wp d p M2 B ≤ 1 / 2 := by
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    show WassersteinDRO.Duality.wassersteinDistance p
      (P8ab0ad33.tp ((1 / 2 : ℝ) • e1) (e0 + (1 / 2 : ℝ) • e1)) (P8ab0ad33.tp e0 e1) ≤ _
    rw [P8ab0ad33.tp_comm e0 e1]
    refine P8ab0ad33.upper hp0 (by norm_num) ?_ ?_
    · rw [show (1 / 2 : ℝ) • e1 - e1 = (0 : ℝ) • e0 + (-(1 / 2) : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
    · rw [show (e0 + (1 / 2 : ℝ) • e1) - e0 = (0 : ℝ) • e0 + (1 / 2 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
  -- finiteness for the lower-bound pairs
  have fAB : WassersteinDRO.Duality.wassersteinDistance p (P8ab0ad33.tp 0 (e0 + e1)) (P8ab0ad33.tp e0 e1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (P8ab0ad33.upper (r := 1) hp0 (by norm_num) ?_ ?_)
    · rw [show (0 : E d) - e0 = (-1 : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num)
    · rw [show (e0 + e1) - e1 = (1 : ℝ) • e0 + (0 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num)
  have fMM : WassersteinDRO.Duality.wassersteinDistance p
      (P8ab0ad33.tp ((1 / 2 : ℝ) • e0) ((1 / 2 : ℝ) • e0 + e1))
      (P8ab0ad33.tp ((1 / 2 : ℝ) • e1) (e0 + (1 / 2 : ℝ) • e1)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (P8ab0ad33.upper (r := 1) hp0 (by norm_num) ?_ ?_)
    · rw [show (1 / 2 : ℝ) • e0 - (1 / 2 : ℝ) • e1 = (1 / 2 : ℝ) • e0 + (-(1 / 2) : ℝ) • e1 by
        module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
    · rw [show ((1 / 2 : ℝ) • e0 + e1) - (e0 + (1 / 2 : ℝ) • e1)
          = (-(1 / 2) : ℝ) • e0 + (1 / 2 : ℝ) • e1 by module]
      exact (P8ab0ad33.nb i0 i1 _ _).trans (by norm_num [abs_of_pos])
  -- lower bounds
  have lAB : 1 ≤ Wp d p A B := by
    have h := P8ab0ad33.lower (c := 1) hp0 (x1 := (0 : E d)) (x2 := e0 + e1) (y1 := e0) (y2 := e1)
      (by norm_num)
      ((by simp [c00] : (1 : ℝ) ≤ |((0 : E d) - e0) i0|).trans (P8ab0ad33.coord_le _ _))
      ((by simp [c11] : (1 : ℝ) ≤ |((0 : E d) - e1) i1|).trans (P8ab0ad33.coord_le _ _))
      ((by simp [c01, c11] : (1 : ℝ) ≤ |((e0 + e1) - e0) i1|).trans (P8ab0ad33.coord_le _ _))
      ((by simp [c00, c10] : (1 : ℝ) ≤ |((e0 + e1) - e1) i0|).trans (P8ab0ad33.coord_le _ _))
    exact (ENNReal.ofReal_le_iff_le_toReal fAB).1 h
  have lMM : 1 / 2 ≤ Wp d p M1 M2 := by
    have h := P8ab0ad33.lower (c := 1 / 2) hp0 (x1 := (1 / 2 : ℝ) • e0) (x2 := (1 / 2 : ℝ) • e0 + e1)
      (y1 := (1 / 2 : ℝ) • e1) (y2 := e0 + (1 / 2 : ℝ) • e1)
      (by norm_num)
      ((by simp [c00, c10] : (1 / 2 : ℝ) ≤ |((1 / 2 : ℝ) • e0 - (1 / 2 : ℝ) • e1) i0|).trans
        (P8ab0ad33.coord_le _ _))
      ((by simp [c00, c10]; norm_num [abs_of_pos] :
          (1 / 2 : ℝ) ≤ |((1 / 2 : ℝ) • e0 - (e0 + (1 / 2 : ℝ) • e1)) i0|).trans (P8ab0ad33.coord_le _ _))
      ((by simp [c00, c10] : (1 / 2 : ℝ) ≤ |(((1 / 2 : ℝ) • e0 + e1) - (1 / 2 : ℝ) • e1) i0|).trans
        (P8ab0ad33.coord_le _ _))
      ((by simp [c00, c10]; norm_num [abs_of_pos] :
          (1 / 2 : ℝ) ≤ |(((1 / 2 : ℝ) • e0 + e1) - (e0 + (1 / 2 : ℝ) • e1)) i0|).trans
        (P8ab0ad33.coord_le _ _))
    exact (ENNReal.ofReal_le_iff_le_toReal fMM).1 h
  -- Hilbert-space contradiction
  rintro ⟨H, _, _, _, φ, hφ⟩
  rw [hφ] at uAM1 uM1B uAM2 uM2B lAB lMM
  set a := φ A
  set b := φ B
  set m1 := φ M1
  set m2 := φ M2
  have par1 := parallelogram_law_with_norm ℝ (a - m1) (m1 - b)
  have par2 := parallelogram_law_with_norm ℝ (a - m2) (m2 - b)
  have s1 : a - m1 + (m1 - b) = a - b := by abel
  have s2 : a - m2 + (m2 - b) = a - b := by abel
  rw [s1] at par1
  rw [s2] at par2
  have n1 := norm_nonneg (a - m1)
  have n2 := norm_nonneg (m1 - b)
  have n3 := norm_nonneg (a - m2)
  have n4 := norm_nonneg (m2 - b)
  have w1 : ‖a - m1 - (m1 - b)‖ = 0 := by
    have := norm_nonneg (a - m1 - (m1 - b))
    nlinarith
  have w2 : ‖a - m2 - (m2 - b)‖ = 0 := by
    have := norm_nonneg (a - m2 - (m2 - b))
    nlinarith
  have hdiff : (a - m2 - (m2 - b)) - (a - m1 - (m1 - b)) = (2 : ℝ) • (m1 - m2) := by module
  have := norm_sub_le (a - m2 - (m2 - b)) (a - m1 - (m1 - b))
  rw [hdiff, w1, w2, norm_smul] at this
  norm_num at this
  linarith
