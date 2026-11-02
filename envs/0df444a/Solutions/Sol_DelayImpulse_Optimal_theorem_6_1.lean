-- Prove2me | solution 1 for DelayImpulse.Optimal.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:20:48.94038+00:00
-- url     : https://prove2.me/submissions/a9546b3a-fe48-4913-a7e0-5579bd21b57e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme
import Theorems.Thm_DelayImpulse_Optimal_proposition_4_1
import Theorems.Thm_DelayImpulse_Optimal_proposition_4_2_i
import Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_value
import Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_upper
import Theorems.Thm_DelayImpulse_Optimal_theorem_6_1_star_exists

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open DelayImpulse.Optimal

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D) :
    (∃ (Yn On : ℕ → Fam Ω l) (O : Fam Ω l), IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On ∧
      IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O) ∧
    ∀ (Yn On : ℕ → Fam Ω l) (O : Fam Ω l), IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On →
      IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O →
      (∃ δ : Strategy Ω l, IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ) ∧
      ∀ δ : Strategy Ω l, IsStarStrategy (ReflectedBSDE.Existence.augmentedFiltration P hB) P D (Ylim Yn) O δ →
        IsAdmissible (ReflectedBSDE.Existence.augmentedFiltration P hB) P D δ ∧
        (∀ᵐ ω ∂P, Ylim Yn (fun _ => 0) (fun _ => 0) 0 ω = J P D δ) ∧
        ∀ δ' : Strategy Ω l, IsAdmissible (ReflectedBSDE.Existence.augmentedFiltration P hB) P D δ' → J P D δ' ≤ J P D δ := by
  -- the first hitting time after `a` is never before `a`
  have hit_ge : ∀ (Oc Yc : ℝ≥0 → Ω → ℝ) (a : Ω → WithTop ℝ≥0) (ω : Ω),
      a ω ≤ firstHit Oc Yc a ω := by
    intro Oc Yc a ω
    unfold firstHit
    split_ifs with h
    · obtain ⟨s, hs⟩ := h
      cases ha : a ω with
      | top => rw [ha] at hs; exact absurd hs.1 (not_le.mpr (WithTop.coe_lt_top s))
      | coe a' =>
        rw [ha] at hs
        refine WithTop.coe_le_coe.mpr (le_csInf ⟨s, hs⟩ fun x hx => ?_)
        exact WithTop.coe_le_coe.mp hx.1
    · exact le_top
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨Yn, On, hS⟩, -, -⟩ := proposition_4_1 P B hB D hD
    have hidx : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB)
        (fun _ : Ω => (0 : WithTop ℝ≥0)) (fun _ : Ω => (0 : Fin l → ℝ)) :=
      { stop := isStoppingTime_const _ 0
        meas := measurable_const
        finite := (Set.finite_singleton (0 : Fin l → ℝ)).subset Set.range_const_subset }
    obtain ⟨-, -, -, ⟨O, hO⟩, -⟩ :=
      proposition_4_2_i P B hB D hD Yn On hS _ _ hidx
    exact ⟨Yn, On, O, hS, hO⟩
  · intro Yn On O hS hO
    refine ⟨theorem_6_1_star_exists P B hB D hD Yn On hS O hO, fun δ hδ => ?_⟩
    have hval := theorem_6_1_value P B hB D hD Yn On hS O hO δ hδ
    refine ⟨?_, hval, fun δ' hδ' => ?_⟩
    · refine ⟨hδ.stop, hδ.meas, hδ.mem, fun n => ?_⟩
      filter_upwards [hδ.hit_succ n] with ω hω
      rw [hω]
      exact hit_ge _ _ (fun ω => δ.τ n ω + (D.Δ : WithTop ℝ≥0)) ω
    · have hup := theorem_6_1_upper P B hB D hD Yn On hS δ' hδ'
      obtain ⟨ω, h1, h2⟩ := (hval.and hup).exists
      rw [← h1]
      exact h2
