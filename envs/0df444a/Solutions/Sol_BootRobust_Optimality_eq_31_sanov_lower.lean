-- Prove2me | solution 1 for BootRobust.Optimality.eq_31_sanov_lower
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:14:38.411192+00:00
-- url     : https://prove2.me/submissions/3128d92a-628d-4439-82e3-e33040688d6e

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting
import Theorems.Thm_DROOptimal_Predictor_theorem_1_lower

open MeasureTheory

theorem br3_simp_comp {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ)
    (hf : f ∈ stdSimplex ℝ β) : (fun a => f (e a)) ∈ stdSimplex ℝ α := by
  refine ⟨fun a => hf.1 _, ?_⟩
  rw [Fintype.sum_equiv e (fun a => f (e a)) f (fun _ => rfl)]
  exact hf.2

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι) (hDtrpos : ∀ i, 0 < Dtr i)
    (C : Set (ι → ℝ)) (D : ι → ℝ) (hDC : D ∈ BootRobust.Optimality.relInt C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ((BootRobust.Perf.bootDist D Dtr).toReal + ε)))) ≤
        BootRobust.Optimality.bootLaw Dtr n {ω | BootRobust.Optimality.empDist ω ∈ C} := by
  classical
  intro ε hε
  obtain ⟨hDsimp, U, hU, hDU, hUC⟩ := hDC
  set d := Fintype.card ι
  let e : ι ≃ Fin d := Fintype.equivFin ι
  have hPsimp := br3_simp_comp e.symm Dtr hDtr
  let P : DROOptimal.Predictor.Δ d := ⟨fun j => Dtr (e.symm j), hPsimp⟩
  have hPpos : ∀ j, 0 < (P : Fin d → ℝ) j := fun j => hDtrpos _
  let Dset : Set (DROOptimal.Predictor.Δ d) := {Q | (fun i => (Q : Fin d → ℝ) (e i)) ∈ U}
  have hopen : IsOpen Dset := by
    exact hU.preimage (continuous_pi (fun i => (continuous_apply (e i)).comp continuous_subtype_val))
  have hmeas : MeasurableSet Dset := hopen.measurableSet
  let P0 : DROOptimal.Predictor.Δ d := ⟨fun j => D (e.symm j), br3_simp_comp e.symm D hDsimp⟩
  have hP0 : P0 ∈ interior Dset := by
    rw [hopen.interior_eq]
    show (fun i => D (e.symm (e i))) ∈ U
    simpa using hDU
  set b := ∑ i, D i * Real.log (D i / Dtr i) with hb
  have hBfin : BootRobust.Perf.bootDist D Dtr = (b : EReal) := by
    unfold BootRobust.Perf.bootDist
    rw [if_pos]
    intro i hi; exact absurd hi (hDtrpos i).ne'
  have hrel : DROOptimal.Predictor.relEntropy P0 P = (b : EReal) := by
    unfold DROOptimal.Predictor.relEntropy
    rw [if_pos]
    · congr 1
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    · intro i hi; exact absurd hi (hPpos i).ne'
  have hs : (⨅ Q ∈ interior Dset, DROOptimal.Predictor.relEntropy Q P) < ((b + ε : ℝ) : EReal) := by
    refine lt_of_le_of_lt (biInf_le _ hP0) ?_
    rw [hrel]; exact_mod_cast (by linarith)
  have key := DROOptimal.Predictor.theorem_1_lower P hPpos Dset hmeas (b + ε) hs
  -- the measure of an event under the bootstrap law
  have hlaw : ∀ (n : ℕ) (S : Set (Fin n → ι)), BootRobust.Optimality.bootLaw Dtr n S =
      ∑ ω : Fin n → ι, if ω ∈ S then ∏ t, ENNReal.ofReal (Dtr (ω t)) else 0 := by
    intro n S
    let m : Measure ι := ∑ i, ENNReal.ofReal (Dtr i) • Measure.dirac i
    haveI : IsFiniteMeasure m := by
      constructor
      simp [m]
    have hm : ∀ j : ι, m {j} = ENNReal.ofReal (Dtr j) := by
      intro j
      simp only [m, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Measure.dirac_apply' _ (measurableSet_singleton j), Set.indicator]
        intro h; exact absurd h hij
      · simp
    have h1 : BootRobust.Optimality.bootLaw Dtr n S =
        BootRobust.Optimality.bootLaw Dtr n (↑(S.toFinset)) := by simp
    rw [h1, ← sum_measure_singleton, ← Finset.sum_filter]
    have hfs : S.toFinset = Finset.univ.filter (· ∈ S) := by ext; simp
    rw [hfs]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    show Measure.pi (fun _ : Fin n => m) {ω} = _
    rw [Measure.pi_singleton]
    simp only [hm]
  filter_upwards [key] with n hn
  rw [hBfin, EReal.toReal_coe, hlaw]
  have hle : Real.exp (-((n:ℝ) * (b + ε))) ≤ DROOptimal.Predictor.empProb P n Dset := by
    rw [mul_comm]; exact hn
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  unfold DROOptimal.Predictor.empProb DROOptimal.Predictor.pathProb
  let E : (Fin n → ι) ≃ (Fin n → Fin d) := (Equiv.refl (Fin n)).arrowCongr e
  have hsum : (∑ ω' : Fin n → Fin d, if DROOptimal.Predictor.EmpiricalIn ω' Dset
      then ∏ t, (P : Fin d → ℝ) (ω' t) else 0)
      = ∑ ω : Fin n → ι, if DROOptimal.Predictor.EmpiricalIn (fun t => e (ω t)) Dset
      then ∏ t, Dtr (ω t) else 0 := by
    refine (Fintype.sum_equiv E _ _ (fun ω => ?_)).symm
    show _ = if DROOptimal.Predictor.EmpiricalIn (fun t => e (ω t)) Dset
      then ∏ t, Dtr (e.symm (e (ω t))) else 0
    simp
  rw [hsum, ENNReal.ofReal_sum_of_nonneg (fun ω _ => by
    split_ifs
    · exact Finset.prod_nonneg (fun t _ => (hDtrpos _).le)
    · exact le_rfl)]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases hE : DROOptimal.Predictor.EmpiricalIn (fun t => e (ω t)) Dset
  · have hC : ω ∈ {ω | BootRobust.Optimality.empDist ω ∈ C} := by
      obtain ⟨h, hU'⟩ := hE
      have hv : (fun i => DROOptimal.Predictor.empiricalVec (fun t => e (ω t)) (e i)) =
          BootRobust.Optimality.empDist ω := by
        funext i
        simp [DROOptimal.Predictor.empiricalVec, BootRobust.Optimality.empDist]
      have h2 := br3_simp_comp e _ h
      have hU'' : (fun i => DROOptimal.Predictor.empiricalVec (fun t => e (ω t)) (e i)) ∈ U := hU'
      rw [hv] at h2 hU''
      exact hUC ⟨hU'', h2⟩
    rw [if_pos hE, if_pos hC, ENNReal.ofReal_prod_of_nonneg (fun t _ => (hDtrpos _).le)]
  · rw [if_neg hE]; simp
