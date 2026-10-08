-- Prove2me | solution 1 for DataDrivenRO.Guarantee.part_b_witness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:44:16.959993+00:00
-- url     : https://prove2.me/submissions/1a82d735-d24e-4327-aa2e-7cc81cee859d

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory Filter Topology

namespace DataDrivenRO.Guarantee.PBW

lemma meas_le {d : ℕ} (P : Measure (Fin d → ℝ)) (v : Fin d → ℝ) (c : ℝ) :
    MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ v ≤ c} := by
  have hc : Continuous (fun u : Fin d → ℝ => u ⬝ᵥ v) := by fun_prop
  exact measurableSet_le hc.measurable measurable_const

lemma not_mem_of_lt_VaR {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε1 : ε < 1) (v : Fin d → ℝ) (σ : ℝ) (hσ : σ < VaR P ε v) :
    P {u | u ⬝ᵥ v ≤ σ} < ENNReal.ofReal (1 - ε) := by
  by_contra hcon
  rw [not_lt] at hcon
  set S : Set ℝ := {y : ℝ | ENNReal.ofReal (1 - ε) ≤ P {u | u ⬝ᵥ v ≤ y}} with hS
  have hVaR : VaR P ε v = sInf S := rfl
  have hσS : σ ∈ S := hcon
  by_cases hb : BddBelow S
  · have := csInf_le hb hσS
    linarith
  · -- S is unbounded below and upward closed: contradiction with continuity of measure
    have hup : ∀ y z, y ∈ S → y ≤ z → z ∈ S := by
      intro y z hy hyz
      refine le_trans hy (measure_mono ?_)
      intro u hu
      exact le_trans hu hyz
    have hall : ∀ y, y ∈ S := by
      intro y
      rw [not_bddBelow_iff] at hb
      obtain ⟨z, hz, hzy⟩ := hb y
      exact hup z y hz hzy.le
    let s : ℕ → Set (Fin d → ℝ) := fun n => {u | u ⬝ᵥ v ≤ -(n : ℝ)}
    have hanti : Antitone s := by
      intro m n hmn u hu
      simp only [s, Set.mem_setOf_eq] at hu ⊢
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hint : (⋂ n, s n) = ∅ := by
      ext u
      simp only [s, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨n, hn⟩ := exists_nat_gt (-(u ⬝ᵥ v))
      have := h n
      linarith
    have ht := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (meas_le P v _).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
    rw [hint, measure_empty] at ht
    have hge : ∀ n, ENNReal.ofReal (1 - ε) ≤ (P ∘ s) n := fun n => hall (-(n : ℝ))
    have h0 : ENNReal.ofReal (1 - ε) ≤ 0 := ge_of_tendsto' ht hge
    have hpos : (0 : ENNReal) < ENNReal.ofReal (1 - ε) := ENNReal.ofReal_pos.mpr (by linarith)
    exact absurd h0 (not_le.mpr hpos)

end DataDrivenRO.Guarantee.PBW

open MeasureTheory DataDrivenRO.Guarantee in
theorem solution {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Set (Fin d → ℝ)) (hne : U.Nonempty)
    (v : Fin d → ℝ) (hbdd : BddAbove ((fun u => u ⬝ᵥ v) '' U)) (t : ℝ) (ht : 0 < t)
    (hgap : RobustMDP.Shared.supportFunction U v ≤ VaR P ε v - t)
    (f : (Fin d → ℝ) → (Fin 1 → ℝ) → ℝ) (hfdef : ∀ u x, f u x = u ⬝ᵥ v - x 0)
    (xstar : Fin 1 → ℝ) (hxstar : xstar = fun _ => RobustMDP.Shared.supportFunction U v) :
    (∀ u ∈ U, f u xstar ≤ 0) ∧ ENNReal.ofReal ε < P {u | 0 < f u xstar} := by
  set σ := RobustMDP.Shared.supportFunction U v with hσdef
  have hσ : σ = sSup ((fun u => u ⬝ᵥ v) '' U) := rfl
  subst hxstar
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [hfdef]
    have : u ⬝ᵥ v ≤ σ := by
      rw [hσ]; exact le_csSup hbdd ⟨u, hu, rfl⟩
    linarith
  · have hlt : σ < VaR P ε v := by linarith
    have hA := DataDrivenRO.Guarantee.PBW.not_mem_of_lt_VaR P ε hε1 v σ hlt
    have hset : {u | 0 < f u (fun _ => σ)} = {u : Fin d → ℝ | u ⬝ᵥ v ≤ σ}ᶜ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, hfdef, not_le]
      constructor <;> intro h <;> linarith
    rw [hset, prob_compl_eq_one_sub (DataDrivenRO.Guarantee.PBW.meas_le P v σ)]
    set a := P {u : Fin d → ℝ | u ⬝ᵥ v ≤ σ}
    have ha_top : a ≠ ⊤ := measure_ne_top P _
    have hsum : ENNReal.ofReal ε + ENNReal.ofReal (1 - ε) = 1 := by
      rw [← ENNReal.ofReal_add hε0.le (by linarith)]
      simp
    have h1 : ENNReal.ofReal ε + a < 1 := by
      calc ENNReal.ofReal ε + a < ENNReal.ofReal ε + ENNReal.ofReal (1 - ε) :=
            ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hA
        _ = 1 := hsum
    exact (ENNReal.cancel_of_ne ha_top).lt_tsub_iff_right.mpr h1
