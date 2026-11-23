-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.oneLevel_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:39.11619+00:00
-- url     : https://prove2.me/submissions/f8853879-d8df-47c3-880d-048f781447d4

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_exists_reps
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_budget_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_budget_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution : OneLevelOfSteps := by
  intro hSplit hSchur hDiag hOne hMulti E W _ D ep C₄ hG hKer hW hA2 hA13 hEW hP hEL hEB hLat hep
    h4 hv0 hv1 T ε hε σ i hi1 hi hσ w hw
  have hwW : w ∈ D.Wall := (Finset.mem_filter.1 hw).1
  have hwc : D.cnt w ≤ 4 * D.K * (D.r + 1 - i) := (Finset.mem_filter.1 hw).2
  have hwt : 0 < D.wt w := hW w
  have he : 0 ≤ D.e i := (hA13 i 1 le_rfl hi1 hi).1.1
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have hb0 : 0 ≤ 2 ^ D.f * ep := by positivity

  have hS : ∀ s, 1 ≤ s → s ≤ i → ∀ M : ℝ,
      (∀ w' ∈ D.Wb (D.cnt w + D.K), D.Dg T ε i s w' ≤ M) →
      D.Sf ε i w (Xs T i s) / D.wt w ≤ (1 + 3 ^ D.f * ep) * M := by
    intro s hs hsi M hM
    have hN : D.cnt w + D.K ≤ D.Ntop := by
      have := budget_top D.K D.r i s (D.cnt w) 1 hsi hi hwc (by omega)
      simpa [Data.Ntop] using this
    have h := hSchur E W D ep hG hKer hW hA2 hEL hLat T ε hε i s hs hsi hi w hwW hN M hM
    have h2 := hM w (Finset.mem_filter.2 ⟨hwW, Nat.le_add_right _ _⟩)
    calc D.Sf ε i w (Xs T i s) / D.wt w ≤ D.Dg T ε i s w + 3 ^ D.f * ep * M := h
      _ ≤ M + 3 ^ D.f * ep * M := by linarith
      _ = (1 + 3 ^ D.f * ep) * M := by ring

  have h1 : D.Sf ε i w (Xs T i 1) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) := by
    apply hS 1 le_rfl hi1
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - 1 + 1) 1) (T.Sg (i - 1 + 1) 1)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i 1 le_rfl hi1 hi w' R hR1
    have hii : i - 1 + 1 = i := by omega
    rw [hii] at hd hR2
    have hT : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hB : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1 - (i - 1)) :=
      budget_step D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hN : D.cnt w' + D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + D.K),
        D.N0 ε (i - 1) w'' (T.X (i - 1)) (D.Kr (i - 1)) ≤ σ (i - 1) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - 1) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have ho := hOne E W D ep hG hKer hW hA13 hEW hP hLat T ε hε i hi1 hi w' hw'W hN R hR2
      (σ (i - 1) ^ 2) hlow
    have hw0 := hlow w' (Finset.mem_filter.2 ⟨hw'W, Nat.le_add_right _ _⟩)
    calc D.Dg T ε i 1 w' ≤ _ := hd
      _ ≤ _ := ho
      _ ≤ (1 + D.e i) * (σ (i - 1) ^ 2 + 2 ^ D.f * ep * σ (i - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2) := by ring

  have h2 : ∀ s, 2 ≤ s → s ≤ i → D.Sf ε i w (Xs T i s) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) := by
    intro s hs hsi
    apply hS s (by omega) hsi
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - s + 1) s) (T.Sg (i - s + 1) s)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i s (by omega) hsi hi w' R hR1
    have hT : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hB : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1 - (i - s)) :=
      budget_step D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hsK : (s + 2) * D.K = D.K + (s + 1) * D.K := by ring
    have hN : D.cnt w' + (s + 1) * D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + (s + 1) * D.K),
        D.N0 ε (i - s) w'' (T.X (i - s)) (D.Kr (i - s)) ≤ σ (i - s) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - s) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have hm := hMulti E W D C₄ hG hKer hW hA13 hEB h4 hv0 T ε hε i s hs hsi hi w' hw'W hN
      (hv1 _ _ (by omega) (by omega) (by omega)) R hR2 (σ (i - s) ^ 2) hlow
    exact hd.trans hm

  have hsplit := hSplit E W D hG hKer T ε hε i hi1 w
  have hIcc : Icc 1 i = insert 1 (Icc 2 i) := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : (1 : ℕ) ∉ Icc 2 i := by simp
  have hfirst : √(D.Q T ε i w) ≤ ∑ s ∈ Icc 1 i, √(D.Sf ε i w (Xs T i s) / D.wt w) := by
    have : ∀ x : ℝ, √(x / D.wt w) = √x / √(D.wt w) := fun x => Real.sqrt_div' x hwt.le
    simp only [Data.Q, this, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right hsplit (Real.sqrt_nonneg _)
  refine hfirst.trans ?_
  rw [hIcc, Finset.sum_insert hnot]
  apply add_le_add
  · have hσ0 : 0 ≤ σ (i - 1) := (hσ (i - 1) (by omega)).1
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + 2 ^ D.f * ep) * (1 + D.e i) * σ (i - 1) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0,
      Real.sqrt_mul' _ (by linarith : 0 ≤ 1 + D.e i)]
  · apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hσ0 : 0 ≤ σ (i - s) := (hσ (i - s) (by omega)).1
    refine (Real.sqrt_le_sqrt (h2 s hs.1 hs.2)).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + D.e i) * C₄ ^ (D.f * s) *
          (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * σ (i - s) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0]
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
