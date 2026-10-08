-- Prove2me | solution 1 for FoundationsML.PAC.finite_consistent_learning_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:08:20.699297+00:00
-- url     : https://prove2.me/submissions/d24d5bf9-1dfa-434b-a228-69b5d6a6a967

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

set_option autoImplicit false

open MeasureTheory

namespace FoundationsML.PAC.Aux552

lemma agree_of_emp_zero {X Y : Type*} {m : ℕ} (hm : 0 < m) (S : Fin m → X) (c h : X → Y)
    (h0 : EmpiricalError S c h = 0) : ∀ i, h (S i) = c (S i) := by
  unfold EmpiricalError at h0
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have h1 := Nat.cast_eq_zero.mp h0
    have h2 := Finset.card_eq_zero.mp h1
    simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] at h2
    exact h2
  · exact absurd h0 hm'

lemma pi_agree_le {X Y : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Y) (hmeas : MeasurableSet {x | h x ≠ c x}) (ε : ℝ)
    (hgt : ε < GeneralizationError D c h) (m : ℕ) :
    Measure.pi (fun _ : Fin m => D) {S : Fin m → X | ∀ i, h (S i) = c (S i)}
      ≤ ENNReal.ofReal (Real.exp (-ε * m)) := by
  have hset : {S : Fin m → X | ∀ i, h (S i) = c (S i)}
      = Set.pi Set.univ (fun _ => {x | h x ≠ c x}ᶜ) := by
    ext S; simp
  rw [hset, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  set r := GeneralizationError D c h with hr
  have hr' : r = (D {x | h x ≠ c x}).toReal := by rw [hr]; rfl
  have hcompl : D {x | h x ≠ c x}ᶜ = ENNReal.ofReal (1 - r) := by
    rw [prob_compl_eq_one_sub hmeas, hr', ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hr1 : r ≤ 1 := by
    rw [hr']
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  rw [hcompl, ← ENNReal.ofReal_pow (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 - r) ^ m ≤ (Real.exp (-r)) ^ m := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-r); linarith
    _ = Real.exp (-r * m) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-ε * m) := by
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith

end FoundationsML.PAC.Aux552

open MeasureTheory FoundationsML.PAC in
theorem solution
    {X Y : Type*} [MeasurableSpace X] (H : Finset (X → Y)) (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Y) (hc : c ∈ H)
    (hH_meas : ∀ h ∈ H, MeasurableSet {x | h x ≠ c x})
    (A : ∀ m : ℕ, (Fin m → X) → (X → Y))
    (hA_mem : ∀ m (S : Fin m → X), A m S ∈ H)
    (hA_consistent : ∀ m (S : Fin m → X), EmpiricalError S c (A m S) = 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm0 : 0 < m) (hm : Real.log (H.card : ℝ) + Real.log (1 / δ) ≤ ε * m) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε}).toReal := by
  classical
  set μ := Measure.pi (fun _ : Fin m => D) with hμ
  set T := {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε} with hTdef
  set Hb := H.filter (fun h => ε < GeneralizationError D c h) with hHb
  have hB : Tᶜ ⊆ ⋃ h ∈ Hb, {S : Fin m → X | ∀ i, h (S i) = c (S i)} := by
    intro S hS
    simp only [hTdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hS
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, hHb, Finset.mem_filter]
    exact ⟨A m S, ⟨hA_mem m S, hS⟩,
      Aux552.agree_of_emp_zero hm0 S c _ (hA_consistent m S)⟩
  have hBle : μ Tᶜ ≤ ENNReal.ofReal δ := by
    calc μ Tᶜ ≤ μ (⋃ h ∈ Hb, {S : Fin m → X | ∀ i, h (S i) = c (S i)}) := measure_mono hB
      _ ≤ ∑ h ∈ Hb, μ {S : Fin m → X | ∀ i, h (S i) = c (S i)} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ h ∈ Hb, ENNReal.ofReal (Real.exp (-ε * m)) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [hHb, Finset.mem_filter] at hh
          exact Aux552.pi_agree_le D c h (hH_meas h hh.1) ε hh.2 m
      _ = Hb.card * ENNReal.ofReal (Real.exp (-ε * m)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ H.card * ENNReal.ofReal (Real.exp (-ε * m)) := by
          have hcf := Finset.card_filter_le H (fun h => ε < GeneralizationError D c h)
          gcongr
      _ = ENNReal.ofReal (H.card * Real.exp (-ε * m)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          have hcard : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr ⟨c, hc⟩
          have h1 : Real.log (H.card * (1 / δ)) ≤ ε * m := by
            rw [Real.log_mul hcard.ne' (by positivity)]; exact hm
          have h2 : (H.card : ℝ) * (1 / δ) ≤ Real.exp (ε * m) := by
            rw [← Real.exp_log (by positivity : (0 : ℝ) < H.card * (1 / δ))]
            exact Real.exp_le_exp.mpr h1
          have h3 : Real.exp (ε * m) * Real.exp (-ε * m) = 1 := by
            rw [← Real.exp_add]; simp
          have hepos := Real.exp_pos (-ε * m)
          calc (H.card : ℝ) * Real.exp (-ε * m)
              = ((H.card : ℝ) * (1 / δ)) * Real.exp (-ε * m) * δ := by
                field_simp
            _ ≤ Real.exp (ε * m) * Real.exp (-ε * m) * δ := by gcongr
            _ = δ := by rw [h3, one_mul]
  have hsum : (1 : ENNReal) ≤ μ T + μ Tᶜ := by
    have hu : μ Set.univ = 1 := measure_univ
    rw [← hu, ← Set.union_compl_self T]
    exact measure_union_le _ _
  have hT : ENNReal.ofReal (1 - δ) ≤ μ T := by
    rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
    calc 1 - ENNReal.ofReal δ ≤ 1 - μ Tᶜ := tsub_le_tsub_left hBle _
      _ ≤ μ T := tsub_le_iff_right.mpr hsum
  have hfin : μ T ≠ ⊤ := measure_ne_top _ _
  calc 1 - δ = (ENNReal.ofReal (1 - δ)).toReal := by
        rw [ENNReal.toReal_ofReal (by linarith)]
    _ ≤ (μ T).toReal := ENNReal.toReal_mono hfin hT
