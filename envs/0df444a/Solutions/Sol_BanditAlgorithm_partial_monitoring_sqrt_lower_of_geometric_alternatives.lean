-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_sqrt_lower_of_geometric_alternatives
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:00:55.608696+00:00
-- url     : https://prove2.me/submissions/f36f94d6-139b-4fc8-9715-6a96329913c9

import Theorems.Thm_BanditAlgorithm_pmSignalMeasure_eq_symmetric_perturbation_of_fiber_sum
import Theorems.Thm_BanditAlgorithm_pmSignalMeasure_kl_le_symmetric_perturbation
import Theorems.Thm_BanditAlgorithm_pmStochMeasure_kl_toReal_le_expected_outside_count
import Theorems.Thm_BanditAlgorithm_pmStochPseudoRegret_pair_tradeoff_of_uniform_kl_bound
import Theorems.Thm_BanditAlgorithm_pmStochPseudoRegret_le_worst_pmRegret
import Mathlib.Data.Real.Pointwise
import Mathlib.Topology.Order.Compact

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal

namespace BanditAlgorithm

private theorem exists_common_exp_tradeoff
    {P : Type*} [Nonempty P] (W : P → ℝ)
    (A B D : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hpolicy : ∀ p : P, ∃ x : ℝ, 0 ≤ x ∧
      A * x + B * Real.exp (-D * x) ≤ 2 * W p) :
    ∃ x : ℝ, 0 ≤ x ∧
      A * x + B * Real.exp (-D * x) ≤ 2 * ⨅ p : P, W p := by
  let f : ℝ → ℝ := fun x => A * x + B * Real.exp (-D * x)
  let M : ℝ := B / A
  have hM : 0 ≤ M := div_nonneg hB hA.le
  have hf : Continuous f := by
    fun_prop
  obtain ⟨x₀, hx₀, hxmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, le_rfl, hM⟩ hf.continuousOn
  refine ⟨x₀, hx₀.1, ?_⟩
  rw [Real.mul_iInf_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_ciInf
  intro p
  obtain ⟨x, hx, hfx⟩ := hpolicy p
  have hxmin' : f x₀ ≤ f x := by
    by_cases hxM : x ≤ M
    · exact hxmin ⟨hx, hxM⟩
    · have hzmem : (0 : ℝ) ∈ Icc 0 M := ⟨le_rfl, hM⟩
      calc
        f x₀ ≤ f 0 := hxmin hzmem
        _ ≤ f x := by
          have hA0 : A ≠ 0 := ne_of_gt hA
          have hAM : A * M = B := by
            dsimp [M]
            field_simp
          have hAx : B ≤ A * x := by
            have : M < x := lt_of_not_ge hxM
            nlinarith
          have hexp : 0 ≤ B * Real.exp (-(D * x)) :=
            mul_nonneg hB (Real.exp_pos _).le
          dsimp [f]
          simp only [mul_zero, neg_mul, Real.exp_zero, mul_one, zero_add]
          linarith
  exact hxmin'.trans hfx

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (hgeom : ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * Real.sqrt n ≤ pmMinimaxRegret G n := by
  classical
  rcases hgeom with ⟨a, b, u, q, ε, δ, hab, hε, hδ, hqsum, habq, hpert⟩
  have hhalfpos : 0 < δ / 2 := by linarith
  have hhalfle : δ / 2 ≤ δ := by linarith
  have hhalf := hpert (δ / 2) hhalfpos hhalfle
  dsimp only at hhalf
  have huminus : (fun i => u i - (δ / 2) * q i) ∈ stdSimplex ℝ (Fin d) := hhalf.1.1
  have huplus : (fun i => u i + (δ / 2) * q i) ∈ stdSimplex ℝ (Fin d) := hhalf.2.1.1
  have hd : d ≠ 0 := by
    intro hd0
    subst d
    simpa using huminus.2
  letI : NeZero d := ⟨hd⟩
  have hmargin : ∀ i : Fin d, (δ / 2) * |q i| ≤ u i := by
    intro i
    by_cases hqi : 0 ≤ q i
    · rw [abs_of_nonneg hqi]
      exact sub_nonneg.mp (huminus.1 i)
    · rw [abs_of_neg (lt_of_not_ge hqi)]
      have hp := huplus.1 i
      dsimp only at hp
      linarith
  let ρ : ℝ := min (δ / 4) ε
  let C : ℝ := (8 / (δ / 2)) * ∑ i, |q i|
  have hρ : 0 < ρ := lt_min (by linarith) hε
  have hρδ : ρ ≤ δ / 4 := min_le_left _ _
  have hρε : ρ ≤ ε := min_le_right _ _
  have hC : 0 ≤ C := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨ρ / 16 * Real.exp (-(C * ρ ^ 2)), by positivity, 1, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hsqrtone : 1 ≤ Real.sqrt (n : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  let Δ : ℝ := ρ / Real.sqrt (n : ℝ)
  have hΔpos : 0 < Δ := div_pos hρ hsqrtpos
  have hΔρ : Δ ≤ ρ := by
    dsimp [Δ]
    exact (div_le_self hρ.le hsqrtone)
  have hΔδ : Δ ≤ δ := le_trans hΔρ (hρδ.trans (by linarith))
  have hΔmargin : Δ ≤ (δ / 2) / 2 := by
    calc Δ ≤ ρ := hΔρ
      _ ≤ δ / 4 := hρδ
      _ = (δ / 2) / 2 := by ring
  have hΔε : Δ ≤ ε := hΔρ.trans hρε
  have henv := hpert Δ hΔpos hΔδ
  dsimp only at henv
  let ua : Fin d → ℝ := fun i => u i - Δ * q i
  let ub : Fin d → ℝ := fun i => u i + Δ * q i
  have hua : ua ∈ stdSimplex ℝ (Fin d) := henv.1.1
  have hub : ub ∈ stdSimplex ℝ (Fin d) := henv.2.1.1
  have humass : ∑ i, u i = 1 := by
    have hm := huminus.2
    rw [Finset.sum_sub_distrib] at hm
    have hmq : ∑ i, (δ / 2) * q i = 0 := by
      rw [← Finset.mul_sum, hqsum, mul_zero]
    linarith
  let N : Finset (Fin k) :=
    Finset.univ.filter (fun c => c ∈ pmNeighbourhood G a b)
  have hmemN (c : Fin k) : c ∈ N ↔ c ∈ pmNeighbourhood G a b := by
    simp [N]
  have hgap (v : Fin d → ℝ) (c r : Fin k) :
      pmExpectedLoss G v c - pmExpectedLoss G v r =
        ∑ i, (G.L c i - G.L r i) * v i := by
    unfold pmExpectedLoss
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have haopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a := by
    intro c
    rw [hgap]
    have hc := henv.1.2 c
    have hneg :
        (∑ i, (G.L c i - G.L a i) * ua i) =
          -(∑ i, (G.L a i - G.L c i) * ua i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hneg]
    exact neg_nonneg.mpr hc
  have hbopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b := by
    intro c
    rw [hgap]
    have hc := henv.2.1.2 c
    have hneg :
        (∑ i, (G.L c i - G.L b i) * ub i) =
          -(∑ i, (G.L b i - G.L c i) * ub i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hneg]
    exact neg_nonneg.mpr hc
  have houta : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a := by
    intro c hc
    rw [hgap]
    exact (henv.2.2.1 c (by simpa using (not_congr (hmemN c)).mp hc)).1
  have houtb : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b := by
    intro c hc
    rw [hgap]
    exact (henv.2.2.1 c (by simpa using (not_congr (hmemN c)).mp hc)).2
  have hinside : ∀ c : Fin k, c ∈ N →
      (pmExpectedLoss G ua c - pmExpectedLoss G ua a) +
        (pmExpectedLoss G ub c - pmExpectedLoss G ub b) = Δ := by
    intro c hc
    rw [hgap, hgap]
    exact henv.2.2.2 c ((hmemN c).mp hc)
  let B : ℝ≥0∞ := ENNReal.ofReal (C * Δ ^ 2)
  have hbound_identity :
      (8 * Δ ^ 2 / (δ / 2)) * ∑ i, |q i| = C * Δ ^ 2 := by
    dsimp [C]
    ring
  let N0 : Finset (Fin k) := ∅
  have heq0 : ∀ c : Fin k, c ∈ N0 →
      pmSignalMeasure G ua c = pmSignalMeasure G ub c := by
    simp [N0]
  have hle0 : ∀ c : Fin k, c ∉ N0 →
      klDiv (pmSignalMeasure G ua c) (pmSignalMeasure G ub c) ≤ B := by
    intro c hc
    have hs := pmSignalMeasure_kl_le_symmetric_perturbation
      G c u q hhalfpos hΔpos.le hΔmargin hmargin hqsum humass
    rw [hbound_identity] at hs
    simpa [ua, ub, B] using hs
  have hfin : ∀ c : Fin k,
      klDiv (pmSignalMeasure G ua c) (pmSignalMeasure G ub c) ≠ ⊤ := by
    intro c
    exact ne_top_of_le_ne_top (by simp [B]) (hle0 c (by simp [N0]))
  have hBtop : B ≠ ⊤ := by simp [B]
  let π₀ : PMPolicy k 𝕊 := {
    select := fun _ => Kernel.const _ (Measure.dirac a)
    markov := by
      intro t
      infer_instance }
  letI : Nonempty (PMPolicy k 𝕊) := ⟨π₀⟩
  have hpolicy : ∀ π : PMPolicy k 𝕊, ∃ x : ℝ, 0 ≤ x ∧
      ε / 2 * x + ((n : ℝ) * Δ / 8) * Real.exp (-(C * Δ ^ 2 * n)) ≤
        2 * (⨆ i : Fin n → Fin d, pmRegret G π n i) := by
    intro π
    have hKLreal := pmStochMeasure_kl_toReal_le_expected_outside_count
      G π ua ub hua hub N0 B hBtop hfin heq0 hle0 n
    have hBreal : B.toReal = C * Δ ^ 2 := by
      dsimp [B]
      rw [ENNReal.toReal_ofReal]
      exact mul_nonneg hC (sq_nonneg Δ)
    rw [hBreal] at hKLreal
    have hcount :
        (∫ h, ∑ t : Fin n, (if (h t).1 ∉ N0 then (1 : ℝ) else 0)
          ∂pmStochMeasure G π ua hua n) = (n : ℝ) := by
      simp [N0]
    rw [hcount] at hKLreal
    have hmass (t : ℕ) (h : PMHistory k 𝕊 t) :
        ∑ c ∈ Finset.univ.filter (fun c => c ∉ N0),
            (π.select t h) {c} ≤ 1 := by
      calc
        ∑ c ∈ Finset.univ.filter (fun c => c ∉ N0),
            (π.select t h) {c} =
            (π.select t h) (Finset.univ.filter (fun c => c ∉ N0) : Set (Fin k)) := by
              simp
        _ ≤ (π.select t h) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hterm_ne (t : ℕ) :
        (∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N0),
          (π.select t h) {c} ∂pmStochMeasure G π ua hua t) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (show (1 : ℝ≥0∞) ≠ ⊤ by simp)
      exact calc
        (∫⁻ h, ∑ c ∈ Finset.univ.filter (fun c => c ∉ N0),
            (π.select t h) {c} ∂pmStochMeasure G π ua hua t) ≤
            ∫⁻ _h : PMHistory k 𝕊 t, (1 : ℝ≥0∞)
              ∂pmStochMeasure G π ua hua t := lintegral_mono (hmass t)
        _ = 1 := by simp
    have hKLraw := pmStochMeasure_kl_le_outside_selection
      G π ua ub hua hub N0 B hfin heq0 hle0 n
    have hKLfin : klDiv (pmStochMeasure G π ua hua n)
        (pmStochMeasure G π ub hub n) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ hKLraw
      apply ENNReal.mul_ne_top hBtop
      exact ENNReal.sum_ne_top.mpr fun t ht => hterm_ne t
    obtain ⟨x, hx, hxtrade⟩ :=
      pmStochPseudoRegret_pair_tradeoff_of_uniform_kl_bound
      G π ua ub hua hub a b N ε (C * Δ ^ 2 * n) Δ hΔpos hΔε haopt hbopt houta houtb
        hinside hKLfin hKLreal
    have hxtrade' :
        ε / 2 * x + ((n : ℝ) * Δ / 8) * Real.exp (-(C * Δ ^ 2 * n)) ≤
          pmStochPseudoRegret G π ua hua n a +
            pmStochPseudoRegret G π ub hub n b := by
      simpa only [neg_mul] using hxtrade
    refine ⟨x, hx, hxtrade'.trans ?_⟩
    have haR := pmStochPseudoRegret_le_worst_pmRegret G π ua hua n a
    have hbR := pmStochPseudoRegret_le_worst_pmRegret G π ub hub n b
    linarith
  have hcommon := exists_common_exp_tradeoff
    (fun π : PMPolicy k 𝕊 => ⨆ i : Fin n → Fin d, pmRegret G π n i)
    (ε / 2) ((n : ℝ) * Δ / 8 * Real.exp (-(C * Δ ^ 2 * n))) 0
    (by linarith) (by positivity) (by norm_num) (by
      intro π
      obtain ⟨x, hx, htrade⟩ := hpolicy π
      exact ⟨x, hx, by simpa using htrade⟩)
  obtain ⟨x, hx, htrade⟩ := hcommon
  have hmain : (n : ℝ) * Δ / 8 * Real.exp (-(C * Δ ^ 2 * n)) ≤
      2 * pmMinimaxRegret G n := by
    have hleft : (n : ℝ) * Δ / 8 ≤ ε / 2 * x +
        (n : ℝ) * Δ / 8 := by
      exact le_add_of_nonneg_left (mul_nonneg (by linarith) hx)
    have hleft' : (n : ℝ) * Δ / 8 * Real.exp (-(C * Δ ^ 2 * n)) ≤
        ε / 2 * x + (n : ℝ) * Δ / 8 * Real.exp (-(C * Δ ^ 2 * n)) :=
      le_add_of_nonneg_left (mul_nonneg (by linarith) hx)
    exact hleft'.trans (by simpa [pmMinimaxRegret] using htrade)
  have hD : C * Δ ^ 2 * (n : ℝ) = C * ρ ^ 2 := by
    dsimp [Δ]
    field_simp
    ring_nf at hsqrtsq ⊢
    nlinarith
  have hnΔ : (n : ℝ) * Δ = ρ * Real.sqrt n := by
    dsimp [Δ]
    field_simp
    nlinarith
  rw [hD] at hmain
  rw [hnΔ] at hmain
  change ρ / 16 * Real.exp (-(C * ρ ^ 2)) * Real.sqrt n ≤ pmMinimaxRegret G n
  have hfactor : 0 < Real.exp (-(C * ρ ^ 2)) := Real.exp_pos _
  nlinarith

end BanditAlgorithm
