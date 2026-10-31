-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_unbounded_genuine_record_scale_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:24:05.372196+00:00
-- url     : https://prove2.me/submissions/e4824e6f-b251-462a-b009-66166a74a812

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_raw_prefix_iff_strict_exit
import Theorems.Thm_AvramDividend_Classical_killedRecord_discount_scale_sandwich_of_raw_exit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Genuine Standing-free reflected-record discount is sandwiched by q-scale ratios. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (hha : h < a) :
    ENNReal.ofReal (W (a - h) / W a) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ∧
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P) ≤
    ENNReal.ofReal (W a / W (a + h)) := by
  classical
  let T : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTime X h ω
  let u : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let G : Set Ω := {ω | T ω ≠ ⊤}
  let w : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-(q * (T ω).toReal)))
  have hu (ω : Ω) (hω : ω ∈ G) :
      (u ω : ℝ≥0∞) =
        (⨅ (s : ℝ≥0) (_ : h < X.X s ω), (s : ℝ≥0∞)) := by
    change T ω ≠ ⊤ at hω
    change ((T ω).toNNReal : ℝ≥0∞) = T ω
    exact ENNReal.coe_toNNReal hω
  have hRaw (d : ℝ) (hd : 0 < -d) (ω : Ω) :
      (ω ∈ G ∧ (∀ t : ℝ≥0, t < u ω → d ≤ X.X t ω)) ↔
      T ω < twoSidedExitDownTime X d ω := by
    constructor
    · rintro ⟨hf, hp⟩
      have hh' := avram_wave3_01_raw_prefix_iff_strict_exit
        X (-d) h hd hh.le ω (u ω) (hu ω hf)
      have hiff : (∀ t : ℝ≥0, t < u ω → d ≤ X.X t ω) ↔
          T ω < twoSidedExitDownTime X d ω := by
        simpa only [neg_neg, T, twoSidedExitUpTime, hu ω hf] using hh'
      exact hiff.mp hp
    · intro hv
      have hf : ω ∈ G := by
        change T ω ≠ ⊤
        exact ne_top_of_lt hv
      have hh' := avram_wave3_01_raw_prefix_iff_strict_exit
        X (-d) h hd hh.le ω (u ω) (hu ω hf)
      have hiff : (∀ t : ℝ≥0, t < u ω → d ≤ X.X t ω) ↔
          T ω < twoSidedExitDownTime X d ω := by
        simpa only [neg_neg, T, twoSidedExitUpTime, hu ω hf] using hh'
      exact ⟨hf, hiff.mpr hv⟩
  have hLeft : (∫⁻ ω, if ω ∈ G ∧
        (∀ t : ℝ≥0, t < u ω → h - a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      twoSidedExitExpectation X q a (a - h) := by
    have hupper : a - (a - h) = h := by ring
    have hlower : -(a - h) = h - a := by ring
    unfold twoSidedExitExpectation
    simp only [hupper, hlower]
    apply lintegral_congr
    intro ω
    by_cases he : T ω < twoSidedExitDownTime X (h - a) ω
    · have hs := (hRaw (h - a) (by linarith) ω).mpr he
      simp only [if_pos hs, if_pos he, w, T]
    · have hs : ¬ (ω ∈ G ∧
          ∀ t : ℝ≥0, t < u ω → h - a ≤ X.X t ω) :=
        fun hbad => he ((hRaw (h - a) (by linarith) ω).mp hbad)
      dsimp only [T] at he
      simp only [if_neg hs, if_neg he]
  have hRight : (∫⁻ ω, if ω ∈ G ∧
        (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
      then w ω else 0 ∂P) =
      twoSidedExitExpectation X q (a + h) a := by
    have hupper : a + h - a = h := by ring
    unfold twoSidedExitExpectation
    simp only [hupper]
    apply lintegral_congr
    intro ω
    by_cases he : T ω < twoSidedExitDownTime X (-a) ω
    · have hs := (hRaw (-a) (by linarith) ω).mpr he
      simp only [if_pos hs, if_pos he, w, T]
    · have hs : ¬ (ω ∈ G ∧
          ∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω) :=
        fun hbad => he ((hRaw (-a) (by linarith) ω).mp hbad)
      dsimp only [T] at he
      simp only [if_neg hs, if_neg he]
  have hScaleL : twoSidedExitExpectation X q a (a - h) =
      ENNReal.ofReal (W (a - h) / W a) :=
    (chat04_twoSidedExitExpectation_eq_corrected X q a (a - h)).trans
      (unbounded_corrected_exit_scale_identity X q hq W hW hnbv a
        (a - h) ha (by linarith) (by linarith))
  have hScaleR : twoSidedExitExpectation X q (a + h) a =
      ENNReal.ofReal (W a / W (a + h)) :=
    (chat04_twoSidedExitExpectation_eq_corrected X q (a + h) a).trans
      (unbounded_corrected_exit_scale_identity X q hq W hW hnbv
        (a + h) a (by linarith) ha.le (by linarith))
  have hSand :=
    killedRecord_discount_scale_sandwich_of_raw_exit X W a h ha hh u G
      hu w (by convert hLeft.trans hScaleL using 1 <;> apply lintegral_congr <;> intro ω <;> split_ifs <;> rfl)
        (by convert hRight.trans hScaleR using 1 <;> apply lintegral_congr <;> intro ω <;> split_ifs <;> rfl)
  have hMiddle :
      (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
        then w ω else 0 ∂P) =
      (∫⁻ ω, if T ω < barrierRuinTime X a ω
        then w ω else 0 ∂P) := by
    apply lintegral_congr
    intro ω
    by_cases he : T ω < barrierRuinTime X a ω
    · have hf : ω ∈ G := by
        change T ω ≠ ⊤
        exact ne_top_of_lt he
      have hs : ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω :=
        ⟨hf, by rw [hu ω hf]; exact he⟩
      simp only [if_pos hs, if_pos he]
    · have hs : ¬ (ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω) := by
        rintro ⟨hf, hlt⟩
        apply he
        rw [hu ω hf] at hlt
        exact hlt
      simp only [if_neg hs, if_neg he]
  constructor
  · calc
      _ ≤ (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
        then w ω else 0 ∂P) := by
          convert hSand.1 using 1 <;> apply lintegral_congr <;> intro ω <;> split_ifs <;> rfl
      _ = _ := by simpa only [T, w] using hMiddle
  · calc
      _ = (∫⁻ ω, if ω ∈ G ∧
          (u ω : ℝ≥0∞) < barrierRuinTime X a ω
        then w ω else 0 ∂P) := by simpa only [T, w] using hMiddle.symm
      _ ≤ _ := by
        convert hSand.2 using 1 <;> apply lintegral_congr <;> intro ω <;> split_ifs <;> rfl
