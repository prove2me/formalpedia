-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_negative_Borel_spatial_counts_jointly_independent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:29:26.317708+00:00
-- url     : https://prove2.me/submissions/133f2a98-c6c0-496d-9450-50335d0aa1a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
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
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      iIndepFun (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P := by
  classical
  dsimp only
  obtain ⟨K, r, hK, hLaw, hReal, hRate⟩ :=
    avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
      X hFinite t n B hMeas hNeg hPair
  have hExact :=
    avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
      X hFinite t n B hMeas hNeg K hK hReal
  have hIndependent :=
    avram_bridge20261123_A77_original_spatial_Nat_count_independence_core
      X hFinite t n B hMeas hNeg hPair K hK hReal
  have hCast : iIndepFun
      (fun i : Fin n => fun ω : Ω => (K i ω : ℝ≥0∞)) P := by
    exact hIndependent.comp
      (fun _ => fun k : ℕ => (k : ℝ≥0∞))
      (fun _ => by fun_prop)
  exact (iIndepFun_congr (fun i => (ae_all_iff.mp hExact) i)).mp hCast
