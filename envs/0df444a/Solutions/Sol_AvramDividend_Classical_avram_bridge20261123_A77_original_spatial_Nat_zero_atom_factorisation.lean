-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_zero_atom_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:47:37.304426+00:00
-- url     : https://prove2.me/submissions/7e27f399-f8dd-4d67-b442-340512a89d59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (K : Fin n → Ω → ℕ)
    (hK : ∀ i, Measurable (K i))
    (hReal : ∀ᵐ ω ∂P, ∀ i,
      (K i ω : ℝ) =
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i)).toReal) :
    P {ω : Ω | ∀ i, K i ω = 0} =
      ∏ i : Fin n, P {ω : Ω | K i ω = 0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hExact :=
    avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
      X hFinite t n B hMeas hNeg K hK hReal
  have hUnionSet :
      (Ioc (0 : ℝ≥0) t ×ˢ (⋃ i : Fin n, B i)) =
        ⋃ i : Fin n, Ioc 0 t ×ˢ B i := by
    ext p
    simp only [Set.mem_prod, Set.mem_iUnion]
    aesop
  have hVoidEvent (ω : Ω) :
      (NX ω (Ioc 0 t ×ˢ (⋃ i, B i)) = 0) ↔
        (∀ i, NX ω (Ioc 0 t ×ˢ B i) = 0) := by
    rw [hUnionSet, measure_iUnion_null_iff]
  have hJoint :
      P {ω : Ω | ∀ i, K i ω = 0} =
        P {ω : Ω | NX ω (Ioc 0 t ×ˢ (⋃ i, B i)) = 0} := by
    apply measure_congr
    filter_upwards [hExact] with ω hω
    apply propext
    change (∀ i, K i ω = 0) ↔
      (NX ω (Ioc 0 t ×ˢ (⋃ i, B i)) = 0)
    rw [hVoidEvent]
    apply forall_congr'
    intro i
    rw [← hω i]
    simp
  have hSingle (i : Fin n) :
      P {ω : Ω | K i ω = 0} =
        P {ω : Ω | NX ω (Ioc 0 t ×ˢ B i) = 0} := by
    apply measure_congr
    filter_upwards [hExact] with ω hω
    apply propext
    change (K i ω = 0) ↔ (NX ω (Ioc 0 t ×ˢ B i) = 0)
    rw [← hω i]
    simp
  have hVoid :=
    avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
      X hFinite t B Finset.univ
      (by simpa using fun i (_ : i ∈ Finset.univ) => hMeas i)
      (by simpa using fun i (_ : i ∈ Finset.univ) => hNeg i)
      (by simpa using fun i (_ : i ∈ Finset.univ) =>
        fun j (_ : j ∈ Finset.univ) => hPair i j)
  have hR :
      (P {ω : Ω | ∀ i, K i ω = 0}).toReal =
        (∏ i : Fin n, P {ω : Ω | K i ω = 0}).toReal := by
    rw [ENNReal.toReal_prod]
    calc
      (P {ω : Ω | ∀ i, K i ω = 0}).toReal =
        (P {ω : Ω | NX ω (Ioc 0 t ×ˢ (⋃ i, B i)) = 0}).toReal := by
          rw [hJoint]
      _ = ∏ i : Fin n,
        (P {ω : Ω | NX ω (Ioc 0 t ×ˢ B i) = 0}).toReal := by
          simpa only [Finset.mem_univ, iUnion_true] using hVoid
      _ = ∏ i : Fin n, (P {ω : Ω | K i ω = 0}).toReal := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hSingle i]
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_lt_top P _).ne
    (ENNReal.prod_lt_top (fun i hi => measure_lt_top P _)).ne).mp hR
