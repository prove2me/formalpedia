-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_physical_single_mark_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:00:01.5779+00:00
-- url     : https://prove2.me/submissions/d3471267-84da-49f4-95b5-66b305628692

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_nonzero_jump_strictly_negative
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (J : Ω → ℝ) (hSupport : ∀ᵐ ω ∂P, ∃ S :
    Finset ℝ≥0, (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧ J ω = ∑ u ∈ S, (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω)
    u)) (g : SimpleFunc ℝ ℝ) (hg : ∀ y, g y ≤ 0) (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ) (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ Iio (0 : ℝ)) (hDisj : ∀ i ∈
    Finset.range K, ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j)) (hTransfer : ∀ w : ℝ → ℝ, (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ g.range, w y) (hFibre : ∀ i ∈
    Finset.range K, B i = Iio (0 : ℝ) ∩ g ⁻¹' {c i}) : let f : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, c i * (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal
    Measurable f ∧
    (∀ᵐ ω ∂P, f ω ≤ 0) ∧ (∀ᵐ ω ∂P, ∀ S : Finset ℝ≥0, (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧ X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) → f ω = ∑ u ∈ S, g (X.X u ω -
    Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) := by
  classical
  let mark : Ω → ℝ≥0 → ℝ := fun ω u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ mark ω u ≠ 0}).map
      (fun u : ℝ≥0 => (u, mark ω u)))
  let f : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range K, c i * (NX ω (Ioc 0 t ×ˢ B i)).toReal
  have hfMeas : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro i hi
    have hc := avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
      X 0 t (B i) (hB i hi).1
    exact measurable_const.mul
      (ENNReal.measurable_toReal.comp (hc.mono (𝓕.le t) le_rfl))
  have hPath (ω : Ω) (S : Finset ℝ≥0)
      (hs : ∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧ mark ω u ≠ 0) :
      f ω = ∑ u ∈ S, g (mark ω u) := by
    have hCount (i : ℕ) (hi : i ∈ Finset.range K) :
        (NX ω (Ioc 0 t ×ˢ B i)).toReal =
          ((S.filter (fun u => mark ω u ∈ B i)).card : ℝ) := by
      let SB := S.filter (fun u => mark ω u ∈ B i)
      have hSB : ∀ u, u ∈ SB ↔
          0 < u ∧ u ≤ t ∧ mark ω u ≠ 0 ∧ mark ω u ∈ B i := by
        intro u
        simp only [SB, Finset.mem_filter]
        constructor
        · intro h
          rcases (hs u).mp h.1 with ⟨hp, ht, hj⟩
          exact ⟨hp, ht, hj, h.2⟩
        · rintro ⟨hp, ht, hj, hb⟩
          exact ⟨(hs u).mpr ⟨hp, ht, hj⟩, hb⟩
      have hRaw :=
        avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
          X ω t (B i) (hB i hi).1 SB hSB 0 t (zero_le : (0 : ℝ≥0) ≤ t) le_rfl
      have hfilt : SB.filter (fun u => 0 < u ∧ u ≤ t) = SB := by
        apply Finset.filter_eq_self.mpr
        intro u hu
        exact ⟨((hSB u).mp hu).1, ((hSB u).mp hu).2.1⟩
      have hReal := congrArg ENNReal.toReal hRaw
      simpa only [mark, NX, SB, hfilt, ENNReal.toReal_natCast] using hReal
    have hVal (u : ℝ≥0) (hu : u ∈ S) :
        (∑ i ∈ Finset.range K,
          if mark ω u ∈ B i then c i else 0) = g (mark ω u) := by
      have hs0 := (hs u).mp hu
      have hneg :=
        avram_p2_c_borel_original_nonzero_jump_strictly_negative
          X ω u hs0.1 hs0.2.2
      have hneg' : mark ω u < 0 := hneg
      calc
        (∑ i ∈ Finset.range K,
            if mark ω u ∈ B i then c i else 0) =
          ∑ i ∈ Finset.range K,
            if g (mark ω u) = c i then c i else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hFibre i hi]
          simp [hneg', eq_comm]
        _ = ∑ z ∈ g.range,
              if g (mark ω u) = z then z else 0 :=
          (hTransfer (fun z : ℝ => if g (mark ω u) = z then z else 0))
        _ = g (mark ω u) := by
          simp [Finset.sum_ite_eq, g.mem_range_self]
    calc
      f ω = ∑ i ∈ Finset.range K,
          c i * ((S.filter (fun u => mark ω u ∈ B i)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hCount i hi]
      _ = ∑ u ∈ S, ∑ i ∈ Finset.range K,
            if mark ω u ∈ B i then c i else 0 := by
        simp_rw [Finset.card_filter, Nat.cast_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        ext u
        simp [mul_ite]
      _ = ∑ u ∈ S, g (mark ω u) :=
        Finset.sum_congr rfl hVal
  refine ⟨hfMeas, ?_, ?_⟩
  · filter_upwards [hSupport] with ω h
    obtain ⟨S, hs, _⟩ := h
    change f ω ≤ 0
    rw [hPath ω S hs]
    exact Finset.sum_nonpos (fun u hu => hg _)
  · filter_upwards [] with ω
    intro S hs
    exact hPath ω S hs
