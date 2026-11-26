-- Prove2me | solution 1 for FourierJacobi.Measure.localField_coordinates_determinant_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:14.637994+00:00
-- url     : https://prove2.me/submissions/20e28ada-c54c-4cb3-92c2-7c1828eefa22

import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_FourierJacobi_Valuations_LocalField
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Measure_NullSets
import Theorems.Thm_FourierJacobi_Measure_coordinates_determinant_ae
import Theorems.Thm_FourierJacobi_Measure_localField_haar_nullSingletonClass

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) :
    ∀ᵐ p : K × K ∂μ.prod μ,
      p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ^ 2 - p.1 * z ≠ 0 := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  let : NullSingletonClass μ := localField_haar_nullSingletonClass K μ
  exact coordinates_determinant_ae μ μ z
end FourierJacobi.Measure
