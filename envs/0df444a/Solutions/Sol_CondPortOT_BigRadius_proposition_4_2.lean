-- Prove2me | solution 1 for CondPortOT.BigRadius.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:25:50.201176+00:00
-- url     : https://prove2.me/submissions/ca352d30-6c8a-473f-b769-f536aedf3e94

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
import Theorems.Thm_CondPortOT_BigRadius_condExp_le_sup
import Theorems.Thm_CondPortOT_BigRadius_exists_measure_condExp_eq
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ < ENNReal.ofReal ρ) (L : Y → ℝ) :
    CondPortOT.SingUninf.worstCasePos DX DY xh yh x0 γ ρ L = ⨆ y, (L y : EReal) := by
  have hmeas : MeasurableSet (CondPortOT.SingUninf.fiber (Y := Y) DX x0 γ) := by
    have hc : Continuous fun x => DX x x0 :=
      hA.contX.comp (continuous_id.prodMk continuous_const)
    exact (isClosed_le hc continuous_const).measurableSet.prod MeasurableSet.univ
  apply le_antisymm
  · unfold CondPortOT.SingUninf.worstCasePos
    refine iSup₂_le fun Q hQ => ?_
    haveI := hQ.1.1
    exact CondPortOT.BigRadius.condExp_le_sup Q _ hmeas hQ.2 L
  · refine iSup_le fun y0 => ?_
    obtain ⟨Q, hQ, hpos, hEq⟩ := CondPortOT.BigRadius.exists_measure_condExp_eq DX DY hN xh yh
      x0 γ hγ hA ρ hρ L y0
    rw [← hEq]
    unfold CondPortOT.SingUninf.worstCasePos
    exact le_iSup₂_of_le (f := fun (Q : Measure (X × Y)) (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧
      0 < Q (CondPortOT.SingUninf.fiber DX x0 γ)) =>
        CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 γ) L) Q ⟨hQ, hpos⟩ le_rfl
