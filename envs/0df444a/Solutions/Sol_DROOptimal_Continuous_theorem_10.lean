-- Prove2me | solution 1 for DROOptimal.Continuous.theorem_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:17:26.576053+00:00
-- url     : https://prove2.me/submissions/da6f4c13-ef17-4ce4-93ec-55b14718ed33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting
import Theorems.Thm_DROOptimal_Continuous_proposition_6
import Theorems.Thm_DROOptimal_Continuous_eq_41
import Theorems.Thm_DROOptimal_Continuous_theorem_9_upper
import Theorems.Thm_DROOptimal_Continuous_theorem_9_lower
import Theorems.Thm_DROOptimal_Continuous_proposition_1_ii_general

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DROOptimal.Continuous

theorem solution {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r : ℝ) :
    (0 ≤ r → Feasible5 γ r (drPredictor γ r)) ∧
      (0 < r → StronglyOptimal5 γ r (drPredictor γ r)) := by
  have : CompactSpace ↥Ξ := isCompact_iff_compactSpace.mp hΞ
  -- continuity of `γ x ·`
  have hγx : ∀ x : ↥X, Continuous (γ x) := fun x =>
    hγ.comp (continuous_const.prodMk continuous_id)
  -- integrability of `γ x` against any probability measure
  have hint : ∀ (x : ↥X) (ℙ : DROOptimal.Continuous.Dist Ξ), Integrable (γ x) (ℙ : Measure ↥Ξ) := by
    intro x ℙ
    obtain ⟨C, hC⟩ := (isCompact_range (hγx x).norm).bddAbove
    exact Integrable.of_bound (hγx x).aestronglyMeasurable C
      (Eventually.of_forall fun ξ => hC ⟨ξ, rfl⟩)
  have hbdd : ∀ x : ↥X, BddAbove (Set.range (γ x)) := fun x =>
    (isCompact_range (hγx x)).bddAbove
  have hle_worst : ∀ (x : ↥X) (ξ : ↥Ξ), γ x ξ ≤ worstCost γ x := fun x ξ =>
    le_ciSup (hbdd x) ξ
  -- the cost is bounded above by the worst-case cost
  have hcost_le : ∀ (x : ↥X) (ℙ : DROOptimal.Continuous.Dist Ξ), cost γ x ℙ ≤ worstCost γ x := by
    intro x ℙ
    have := integral_mono (hint x ℙ) (integrable_const (worstCost γ x)) (hle_worst x)
    simpa [cost] using this
  -- `ĉ_r(x, ℙ') ≥ c(x, ℙ')` for `r ≥ 0`
  have hmem_self : ∀ (r : ℝ) (ℙ' : DROOptimal.Continuous.Dist Ξ), ℙ' ∈ {ℙ : DROOptimal.Continuous.Dist Ξ | relEnt ℙ' ℙ ≤ ENNReal.ofReal r} := by
    intro r ℙ'
    simp only [Set.mem_ofPred_eq, relEnt, InformationTheory.klDiv_self, zero_le]
  have hdr_ge : ∀ (r : ℝ) (x : ↥X) (ℙ' : DROOptimal.Continuous.Dist Ξ), cost γ x ℙ' ≤ drPredictor γ r x ℙ' := by
    intro r x ℙ'
    apply le_csSup
    · refine ⟨worstCost γ x, ?_⟩
      rintro _ ⟨ℙ, _, rfl⟩
      exact hcost_le x ℙ
    · exact ⟨ℙ', hmem_self r ℙ', rfl⟩
  -- the worst-case set is measurable
  have hWmeas : ∀ x : ↥X, MeasurableSet (worstSet γ x) := fun x =>
    (isClosed_eq (hγx x) continuous_const).measurableSet
  -- a distribution supported on the worst-case set has cost equal to the worst-case cost
  have hcost_worst : ∀ (x : ↥X) (ℙ : DROOptimal.Continuous.Dist Ξ), (ℙ : Measure ↥Ξ) (worstSet γ x)ᶜ = 0 →
      cost γ x ℙ = worstCost γ x := by
    intro x ℙ h0
    have hae : γ x =ᵐ[(ℙ : Measure ↥Ξ)] fun _ => worstCost γ x := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null ?_ h0
      intro ξ hξ hW
      exact hξ hW
    simp [cost, integral_congr_ae hae]
  have hF : 0 ≤ r → Feasible5 γ r (drPredictor γ r) := by
    intro hr
    have hcont := DROOptimal.Continuous.proposition_6 hX hΞ γ hγ r hr
    refine ⟨hcont, fun x ℙ₀ => ?_⟩
    by_cases hcase : (ℙ₀ : Measure ↥Ξ) (worstSet γ x) < 1
    · -- Case 2
      set D : Set (DROOptimal.Continuous.Dist Ξ) := {ℙ' | drPredictor γ r x ℙ' < cost γ x ℙ₀} with hD
      have hcx : Continuous (fun ℙ' : DROOptimal.Continuous.Dist Ξ => drPredictor γ r x ℙ') :=
        hcont.comp (continuous_const.prodMk continuous_id)
      have hclosed : IsClosed {ℙ' : DROOptimal.Continuous.Dist Ξ | drPredictor γ r x ℙ' ≤ cost γ x ℙ₀} :=
        isClosed_le hcx continuous_const
      have hcl : closure D ⊆ {ℙ' : DROOptimal.Continuous.Dist Ξ | drPredictor γ r x ℙ' ≤ cost γ x ℙ₀} :=
        closure_minimal (fun ℙ' h => show drPredictor γ r x ℙ' ≤ cost γ x ℙ₀ from le_of_lt h) hclosed
      have hinf : ENNReal.ofReal r ≤ ⨅ ℙ' ∈ closure D, relEnt ℙ' ℙ₀ := by
        refine le_iInf₂ fun ℙ' h' => ?_
        exact DROOptimal.Continuous.eq_41 hX hΞ γ hγ r hr x ℙ₀ hcase ℙ' (hcl h')
      have hup := DROOptimal.Continuous.theorem_9_upper hΞ ℙ₀ D
      intro r' hr'
      exact hup r' (lt_of_lt_of_le hr' hinf)
    · -- Case 1
      have h1 : (ℙ₀ : Measure ↥Ξ) (worstSet γ x) = 1 :=
        le_antisymm prob_le_one (not_lt.mp hcase)
      have h0 : (ℙ₀ : Measure ↥Ξ) (worstSet γ x)ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff (hWmeas x)]; exact h1
      have hc0 := hcost_worst x ℙ₀ h0
      have hzero : ∀ T, sampleProb ℙ₀ T (fun ℙ' => drPredictor γ r x ℙ' < cost γ x ℙ₀) = 0 := by
        intro T
        unfold sampleProb
        split_ifs with hT
        · refine measure_mono_null (t := ⋃ t : Fin T, Function.eval t ⁻¹' (worstSet γ x)ᶜ) ?_ ?_
          · intro ω hω
            simp only [Set.mem_ofPred_eq] at hω
            by_contra hnot
            simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_compl_iff,
              not_exists, not_not] at hnot
            have hemp0 : ((empirical ω hT : DROOptimal.Continuous.Dist Ξ) : Measure ↥Ξ) (worstSet γ x)ᶜ = 0 := by
              show empiricalMeasure ω (worstSet γ x)ᶜ = 0
              simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finsetSum,
                Finset.sum_apply, smul_eq_mul]
              rw [Finset.sum_eq_zero, mul_zero]
              intro t _
              rw [Measure.dirac_apply' _ (hWmeas x).compl]
              simp [hnot t]
            have := hcost_worst x _ hemp0
            have := hdr_ge r x (empirical ω hT)
            linarith
          · refine measure_iUnion_null fun t => ?_
            rw [(measurePreserving_eval (fun _ : Fin T => (ℙ₀ : Measure ↥Ξ)) t).measure_preimage
              (hWmeas x).compl.nullMeasurableSet]
            exact h0
        · rfl
      intro r' _
      exact Eventually.of_forall fun T => (hzero T).le.trans zero_le
  refine ⟨hF, fun hr => ?_⟩
  · ---------------- Strong optimality ----------------
    have hfeas : Feasible5 γ r (drPredictor γ r) := hF hr.le
    refine ⟨hfeas, fun ĉ hĉ x ℙ' => ?_⟩
    by_contra hlt
    push Not at hlt
    -- a model `ℙ` in the ball with `c(x, ℙ) > ĉ(x, ℙ')`
    unfold drPredictor at hlt
    obtain ⟨_, ⟨ℙ, hℙ, rfl⟩, hgt⟩ :=
      exists_lt_of_lt_csSup (Set.Nonempty.image _ ⟨ℙ', hmem_self r ℙ'⟩) hlt
    simp only [Set.mem_ofPred_eq] at hℙ
    -- the segment `ℙ(t) = (1 - t) ℙ' + t ℙ`
    set a := cost γ x ℙ'
    set b := cost γ x ℙ
    have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), ĉ x ℙ' < (1 - t) * a + t * b := by
      have hc : Continuous (fun t : ℝ => (1 - t) * a + t * b) := by fun_prop
      have ht : Tendsto (fun t : ℝ => (1 - t) * a + t * b) (𝓝[<] (1 : ℝ)) (𝓝 b) := by
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
        simpa using this
      exact ht.eventually (lt_mem_nhds hgt)
    obtain ⟨t, ht, ht01⟩ := (hev.and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
    obtain ⟨ht0, ht1⟩ := ht01
    -- build the mixture as a probability measure
    let μt : Measure ↥Ξ :=
      ENNReal.ofReal (1 - t) • (ℙ' : Measure ↥Ξ) + ENNReal.ofReal t • (ℙ : Measure ↥Ξ)
    have hμt : IsProbabilityMeasure μt := by
      constructor
      simp only [μt, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by linarith) ht0.le]
      simp
    let ℙt : DROOptimal.Continuous.Dist Ξ := ⟨μt, hμt⟩
    have hcost_t : cost γ x ℙt = (1 - t) * a + t * b := by
      show ∫ ξ, γ x ξ ∂μt = _
      simp only [μt]
      rw [integral_add_measure ((hint x ℙ').smul_measure ENNReal.ofReal_ne_top)
        ((hint x ℙ).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
        integral_smul_measure, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0.le]
      simp [a, b, cost, smul_eq_mul]
    -- relative entropy bound via convexity
    have hconv := DROOptimal.Continuous.proposition_1_ii_general hΞ ℙ' ℙ' ℙ' ℙ t ⟨ht0.le, ht1.le⟩
    have hfirst : ENNReal.ofReal (1 - t) • (ℙ' : Measure ↥Ξ) + ENNReal.ofReal t • (ℙ' : Measure ↥Ξ)
        = (ℙ' : Measure ↥Ξ) := by
      rw [← add_smul, ← ENNReal.ofReal_add (by linarith) ht0.le]
      simp
    rw [hfirst] at hconv
    have hrelt : relEnt ℙ' ℙt < ENNReal.ofReal r := by
      have h1 : relEnt ℙ' ℙt ≤ ENNReal.ofReal t * ENNReal.ofReal r := by
        have hself : relEnt ℙ' ℙ' = 0 := by simp [relEnt, InformationTheory.klDiv_self]
        calc relEnt ℙ' ℙt = InformationTheory.klDiv (ℙ' : Measure ↥Ξ) μt := rfl
          _ ≤ _ := hconv
          _ = ENNReal.ofReal t * relEnt ℙ' ℙ := by rw [hself]; simp
          _ ≤ _ := by gcongr
      refine lt_of_le_of_lt h1 ?_
      rw [← ENNReal.ofReal_mul ht0.le]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by nlinarith)
    -- the disappointment set of `ĉ` under `ℙt` is open and contains `ℙ'`
    set D : Set (DROOptimal.Continuous.Dist Ξ) := {Q | ĉ x Q < cost γ x ℙt} with hD
    have hcx : Continuous (fun Q : DROOptimal.Continuous.Dist Ξ => ĉ x Q) :=
      hĉ.1.comp (continuous_const.prodMk continuous_id)
    have hopen : IsOpen D := isOpen_lt hcx continuous_const
    have hmem : ℙ' ∈ D := by
      show ĉ x ℙ' < cost γ x ℙt
      rw [hcost_t]; exact ht
    have hinf : (⨅ Q ∈ interior D, relEnt Q ℙt) < ENNReal.ofReal r := by
      refine lt_of_le_of_lt ?_ hrelt
      exact iInf₂_le ℙ' (by rw [hopen.interior_eq]; exact hmem)
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hinf
    obtain ⟨r', hr'1, hr'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hs'2
    have hlow := DROOptimal.Continuous.theorem_9_lower hΞ ℙt D s' hs'1
    have hupp := hĉ.2 x ℙt r' hr'2
    have hsr : (s' : ℝ) < (r' : ℝ) := by exact_mod_cast (ENNReal.coe_lt_coe.mp hr'1)
    obtain ⟨T, hT1, hT2, hT3⟩ := (hlow.and (hupp.and (eventually_gt_atTop 0))).exists
    have hle := le_trans hT1 hT2
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT3
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp] at hle
    nlinarith
