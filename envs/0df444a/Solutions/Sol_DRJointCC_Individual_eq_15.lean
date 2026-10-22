-- Prove2me | solution 1 for DRJointCC.Individual.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:23:39.283825+00:00
-- url     : https://prove2.me/submissions/983ef7a8-7e0b-4ed7-9f69-99f2f5d77cbb

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open DRJointCC.Individual

theorem solution {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L) :
    ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ 0} ↔
      wcVaR ε μ Sig L ≤ 0 := by
  constructor
  · intro h
    unfold wcVaR
    have := iInf₂_le (f := fun (γ : ℝ) (_ : ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ γ}) => (γ : EReal))
      (0 : ℝ) h
    simpa using this
  · intro h
    refine le_iInf₂ (fun P hP => ?_)
    have hprob : IsProbabilityMeasure P := hP.1.1
    -- for every δ > 0 the constraint holds at level δ
    have hδ : ∀ n : ℕ, ENNReal.ofReal (1 - ε) ≤ P {ξ | L ξ ≤ 1 / ((n : ℝ) + 1)} := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hlt : wcVaR ε μ Sig L < ((1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
        lt_of_le_of_lt h (by exact_mod_cast hpos)
      unfold wcVaR at hlt
      obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hc, hlt'⟩ := iInf_lt_iff.mp hγ
      have hγδ : γ ≤ 1 / ((n : ℝ) + 1) := by
        have : (γ : EReal) < ((1 / ((n : ℝ) + 1) : ℝ) : EReal) := hlt'
        exact (EReal.coe_lt_coe_iff.mp this).le
      calc ENNReal.ofReal (1 - ε) ≤ P {ξ | L ξ ≤ γ} := hc.trans (iInf₂_le P hP)
        _ ≤ P {ξ | L ξ ≤ 1 / ((n : ℝ) + 1)} := measure_mono (fun ξ hξ => le_trans hξ hγδ)
    have hset : {ξ | L ξ ≤ 0} = ⋂ n : ℕ, {ξ | L ξ ≤ 1 / ((n : ℝ) + 1)} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hξ n
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hξ
        refine le_of_forall_pos_le_add (fun δ hδ0 => ?_)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ0
        have := hξ n
        linarith
    have hanti : Antitone (fun n : ℕ => {ξ : Fin k → ℝ | L ξ ≤ 1 / ((n : ℝ) + 1)}) := by
      intro m n hmn ξ hξ
      have hξ' : L ξ ≤ 1 / ((n : ℝ) + 1) := hξ
      show L ξ ≤ 1 / ((m : ℝ) + 1)
      refine le_trans hξ' ?_
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    have hlim := tendsto_measure_iInter_atTop
      (μ := P) (s := fun n : ℕ => {ξ : Fin k → ℝ | L ξ ≤ 1 / ((n : ℝ) + 1)})
      (fun n => (measurableSet_le hL measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top P _⟩
    rw [hset]
    exact ge_of_tendsto' hlim hδ
