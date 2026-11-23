-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:39:02.033045+00:00
-- url     : https://prove2.me/submissions/3051c9d2-3eb8-4701-b894-99ae071ab439
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_all_atom_factorisation
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
    iIndepFun K P := by
  letI : IsProbabilityMeasure P := X.isProbability
  exact avram_bridge20261123_A77_finite_Nat_joint_atoms_imply_independent
    P n K hK
    (avram_bridge20261123_A77_original_spatial_Nat_count_all_atom_factorisation
      X hFinite t n B hMeas hNeg hPair K hK hReal)
