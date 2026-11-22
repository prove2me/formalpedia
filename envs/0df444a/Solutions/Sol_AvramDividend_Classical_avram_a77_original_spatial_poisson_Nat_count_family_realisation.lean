-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_spatial_poisson_Nat_count_family_realisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:42:32.29128+00:00
-- url     : https://prove2.me/submissions/e8646ac6-1773-43b4-a3be-7f5708d8f3d4

/- Source-faithful original negative mark counts to finite Nat-valued
   Poisson representative family. Spatial independence stays an explicit
   premise on the original physical marked-jump counting measure.
   No independent auxiliary sample source is manufactured. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0)
    (hJoint : ∀ (n : ℕ) (B : Fin n → Set ℝ),
      (∀ i, MeasurableSet (B i)) →
      (∀ i, B i ⊆ Iio (0 : ℝ)) →
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      iIndepFun (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P)
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : Fin n → Ω → ℕ) (r : Fin n → ℝ≥0),
      (∀ i, Measurable (K i)) ∧
      iIndepFun K P ∧
      (∀ i, HasLaw (K i) (poissonMeasure (r i)) P) ∧
      (∀ᵐ ω ∂P, ∀ i, (K i ω : ℝ) =
        (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∧
      (∀ i, (r i : ℝ) =
        ((t : ℝ≥0∞) * X.ν (B i)).toReal) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hCases : ∀ i : Fin n,
      ∃ (K : Ω → ℕ) (r : ℝ≥0),
        Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
        (∀ᵐ ω ∂P, (K ω : ℝ) =
          (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∧
        (r : ℝ) = ((t : ℝ≥0∞) * X.ν (B i)).toReal := by
    intro i
    exact hCountLaw (B i) (hMeas i) (hNeg i)
  choose K r hK hLaw hEq hr using hCases
  have hIndepRaw : iIndepFun
      (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P :=
    hJoint n B hMeas hNeg hPair
  have hIndepNat : iIndepFun
      (fun i : Fin n => fun ω : Ω =>
        Nat.floor ((NX ω (Ioc 0 t ×ˢ B i)).toReal)) P := by
    have hComp := hIndepRaw.comp
      (fun _ : Fin n => fun x : ℝ≥0∞ => Nat.floor (x.toReal))
      (fun _ => Nat.measurable_floor.comp ENNReal.measurable_toReal)
    change iIndepFun
      (fun i : Fin n => fun ω : Ω =>
        Nat.floor ((NX ω (Ioc 0 t ×ˢ B i)).toReal)) P at hComp
    exact hComp
  have hNatEq : ∀ i : Fin n,
      (fun ω : Ω => Nat.floor
        ((NX ω (Ioc 0 t ×ˢ B i)).toReal)) =ᵐ[P] K i := by
    intro i
    filter_upwards [hEq i] with ω hω
    change Nat.floor ((NX ω (Ioc 0 t ×ˢ B i)).toReal) = K i ω
    rw [← hω]
    simp
  have hKIndep : iIndepFun K P := hIndepNat.congr hNatEq
  refine ⟨K, r, hK, hKIndep, hLaw, ?_, hr⟩
  exact Filter.eventually_all.mpr hEq
