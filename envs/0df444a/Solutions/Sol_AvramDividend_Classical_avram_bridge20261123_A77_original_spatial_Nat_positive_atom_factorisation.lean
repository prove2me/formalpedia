-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_positive_atom_factorisation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:10:40.630676+00:00
-- url     : https://prove2.me/submissions/db750955-e31b-46d5-b13f-14c125d14a9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_positive_atom_at_least_two_marks
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
    ∀ counts : Fin n → ℕ, counts ≠ (fun _ => 0) →
      P {ω : Ω | ∀ i, K i ω = counts i} =
        ∏ i : Fin n, P {ω : Ω | K i ω = counts i} := by
  classical
  by_cases hn : 2 ≤ n
  · exact avram_bridge20261123_A77_positive_atom_at_least_two_marks
      X hFinite t n hn B hMeas hNeg hPair K hK hReal
  · have hn1 : n ≤ 1 := by omega
    letI : Subsingleton (Fin n) := ⟨fun i j => by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega⟩
    letI : IsProbabilityMeasure P := X.isProbability
    have hIndep : iIndepFun K P := iIndepFun.of_subsingleton
    intro counts _
    have hAtom := hIndep.measure_inter_preimage_eq_mul
      (Finset.univ : Finset (Fin n))
      (sets := fun i => ({counts i} : Set ℕ))
      (by intro i hi; exact measurableSet_singleton (counts i))
    have hPreimage :
        (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          K i ⁻¹' ({counts i} : Set ℕ)) =
        {ω : Ω | ∀ i, K i ω = counts i} := by
      ext ω
      simp
    rw [hPreimage] at hAtom
    have hSingle (i : Fin n) :
        K i ⁻¹' ({counts i} : Set ℕ) =
          {ω : Ω | K i ω = counts i} := by
      ext ω
      simp
    simp_rw [hSingle] at hAtom
    exact hAtom
