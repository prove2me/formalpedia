-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_closed_cash_interior_w_commutator_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:19:45.039731+00:00
-- url     : https://prove2.me/submissions/b5ed325e-5c7c-4165-8aef-ecdd141eb95c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_closed_cash_wjump_commutator_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_mixed_commutator_eq_w_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On a cap-safe original drift-upshift grid, the accepted
physical cash/source inequality has the exact w nonlinear jump
kernel and w mixed commutator required by F2's C1 mesh limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u → u 0 = 0 →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
      (∀ i : ℕ, i < n →
        C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω +
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal) →
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let z : ℕ → ℝ := fun i => Y (u i)
    let c : ℕ → ℝ := fun i =>
      ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
    let j : ℕ → ℝ := fun i =>
      ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
      else 0
    E (u n) * w (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal ≤
      w x +
        (∑ i ∈ Finset.range n,
          (E (u (i + 1)) - E (u i)) * V (Y (u (i + 1)))) +
        ((∑ i ∈ Finset.range n,
          E (u i) * (V (z i + c i) - V (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i - j i) - w (z i))) +
         (∑ i ∈ Finset.range n,
          E (u i) * (w (z i + c i - j i) - w (z i + c i) -
            w (z i - j i) + w (z i)))) := by
  intro V E
  have hCash :=
    avram_p3_2_original_closed_cash_wjump_commutator_budget
      X hBV x hx C hC hxc q hq w hw_cont hw_smooth hw_grad D hD
  filter_upwards [hCash] with ω hω
  intro u n hu hu0 hPre hUp
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let z : ℕ → ℝ := fun i => Y (u i)
  let c : ℕ → ℝ := fun i =>
    ((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift
  let j : ℕ → ℝ := fun i =>
    ∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
      Function.leftLim (fun t : ℝ≥0 => X.X t ω) v - X.X v ω
    else 0
  have hActive : ∀ i : ℕ, i < n →
      u i = 0 ∨ (u i : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    cases i with
    | zero => exact Or.inl hu0
    | succ k =>
        have hk : k < n := by omega
        simpa only [Nat.succ_eq_add_one] using hPre k hk
  have hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal := by
    intro i hi
    by_cases hTop : C = ⊤
    · exact Or.inl hTop
    · right
      have hClosed :=
        (avram_p4_d_dividend_postrightpayment_reserve_closed_cap
          X x C hxc D hD ω (u i) (hActive i hi)).2
      exact (ENNReal.ofReal_le_iff_le_toReal hTop).mp hClosed
  have hMixed :=
    avram_p3_2_original_physical_mixed_commutator_eq_w_grid
      X ω x D w C q u n hu hCap hUp
  have hBase := hω u n hu hu0 hPre
  dsimp only at hBase hMixed ⊢
  calc
    _ ≤ _ := hBase
    _ = _ := by rw [hMixed]
