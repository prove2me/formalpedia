-- Prove2me | solution 1 for ConvStochDual.Existence.pp13_lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:15:03.994907+00:00
-- url     : https://prove2.me/submissions/3a8f2ed8-352a-4cb0-92c0-2cad6344872a

import Mathlib

open MeasureTheory Filter Topology

namespace CSDL22


/-- Pull-out on a set where the `G`-measurable factor is bounded. -/
theorem setIntegral_mul_condExp {Ω : Type*} (G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hG : G ≤ mΩ)
    (a v : Ω → ℝ) (ha : StronglyMeasurable[G] a) (hv : Integrable v P)
    (D : Set Ω) (hD : MeasurableSet[G] D) (N : ℝ) (hN : ∀ ω ∈ D, |a ω| ≤ N) :
    IntegrableOn (fun ω => a ω * v ω) D P ∧
    ∫ ω in D, a ω * v ω ∂P = ∫ ω in D, a ω * P[v | G] ω ∂P := by
  set φ : Ω → ℝ := D.indicator a with hφ
  have hφsm : StronglyMeasurable[G] φ := ha.indicator hD
  have hφb : ∀ ω, ‖φ ω‖ ≤ max N 0 := by
    intro ω
    by_cases h : ω ∈ D
    · simp only [hφ, Set.indicator_of_mem h, Real.norm_eq_abs]
      exact (hN ω h).trans (le_max_left _ _)
    · simp [hφ, Set.indicator_of_notMem h]
  have hDm : MeasurableSet D := hG _ hD
  have hint : Integrable (fun ω => φ ω * v ω) P :=
    hv.bdd_mul (hφsm.mono hG).aestronglyMeasurable (Eventually.of_forall hφb)
  have hint' : Integrable (fun ω => φ ω * P[v | G] ω) P :=
    integrable_condExp.bdd_mul (hφsm.mono hG).aestronglyMeasurable (Eventually.of_forall hφb)
  have e1 : (fun ω => φ ω * v ω) = D.indicator (fun ω => a ω * v ω) := by
    funext ω; by_cases h : ω ∈ D <;> simp [hφ, h]
  have e2 : (fun ω => φ ω * P[v | G] ω) = D.indicator (fun ω => a ω * P[v | G] ω) := by
    funext ω; by_cases h : ω ∈ D <;> simp [hφ, h]
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hDm, ← e1]; exact hint
  · rw [← integral_indicator hDm, ← integral_indicator hDm, ← e1, ← e2]
    have h1 : P[(φ * v) | G] =ᵐ[P] φ * P[v | G] :=
      condExp_stronglyMeasurable_mul_of_bound hG hφsm hv (max N 0) (Eventually.of_forall hφb)
    calc ∫ ω, φ ω * v ω ∂P = ∫ ω, P[(φ * v) | G] ω ∂P := (integral_condExp hG).symm
      _ = ∫ ω, (φ * P[v | G]) ω ∂P := integral_congr_ae h1
      _ = ∫ ω, φ ω * P[v | G] ω ∂P := rfl


theorem ofReal_integral_le_lintegral {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  have h1 : ∫ ω, f ω ∂μ ≤ ∫ ω, max (f ω) 0 ∂μ :=
    integral_mono hf hf.pos_part (fun ω => le_max_left _ _)
  have h2 : ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) = ∫⁻ ω, ENNReal.ofReal (max (f ω) 0) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hf.pos_part
      (Eventually.of_forall fun ω => le_max_right _ _)
  have h3 : (fun ω => ENNReal.ofReal (max (f ω) 0)) = fun ω => ENNReal.ofReal (f ω) := by
    funext ω; rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]; exact max_eq_left (by simp)
  calc ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal h1
    _ = _ := by rw [h2, h3]

/-- The localization step of Lemma 22. -/
theorem step {Ω : Type*} (G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (hG : G ≤ mΩ)
    {ι : Type*} (I : Finset ι) (x v : ι → Ω → ℝ)
    (hx : ∀ i ∈ I, StronglyMeasurable[G] (x i)) (hv : ∀ i, Integrable (v i) P)
    (hpos : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ I, x i ω * v i ω) ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (∑ i ∈ I, x i ω * P[v i | G] ω) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ I, x i ω * v i ω) ∂P ∧
    (Integrable (fun ω => ∑ i ∈ I, x i ω * P[v i | G] ω) P →
      Integrable (fun ω => ∑ i ∈ I, x i ω * v i ω) P ∧
      ∫ ω, ∑ i ∈ I, x i ω * v i ω ∂P = ∫ ω, ∑ i ∈ I, x i ω * P[v i | G] ω ∂P) := by
  set S : Ω → ℝ := fun ω => ∑ i ∈ I, x i ω * v i ω with hS
  set S' : Ω → ℝ := fun ω => ∑ i ∈ I, x i ω * P[v i | G] ω with hS'
  -- the localizing sets
  set B : ℕ → Set Ω := fun N => {ω | ∀ i ∈ I, |x i ω| ≤ N} with hB
  have hBG : ∀ N, MeasurableSet[G] (B N) := by
    intro N
    have : B N = ⋂ i ∈ I, {ω | |x i ω| ≤ N} := by ext ω; simp [hB]
    rw [this]
    exact Finset.measurableSet_biInter (m := G) I fun i hi =>
      (continuous_abs.measurable.comp (hx i hi).measurable) measurableSet_Iic
  have hBm : ∀ N, MeasurableSet (B N) := fun N => hG _ (hBG N)
  have hBmono : Monotone B := by
    intro N M hNM ω hω i hi
    exact (hω i hi).trans (by exact_mod_cast hNM)
  have hBU : (⋃ N, B N) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ i ∈ I, |x i ω|)
    refine ⟨N, fun i hi => ?_⟩
    exact (Finset.single_le_sum (f := fun i => |x i ω|) (fun j _ => abs_nonneg _) hi).trans hN
  have hBdir : Directed (· ⊆ ·) B := hBmono.directed_le
  -- key identity
  have key : ∀ N (A : Set Ω), MeasurableSet[G] A →
      IntegrableOn S (A ∩ B N) P ∧ IntegrableOn S' (A ∩ B N) P ∧
      ∫ ω in A ∩ B N, S ω ∂P = ∫ ω in A ∩ B N, S' ω ∂P := by
    intro N A hA
    have hD : MeasurableSet[G] (A ∩ B N) := hA.inter (hBG N)
    have hb : ∀ i ∈ I, ∀ ω ∈ A ∩ B N, |x i ω| ≤ N := fun i hi ω hω => hω.2 i hi
    have h := fun i (hi : i ∈ I) =>
      setIntegral_mul_condExp G hG (x i) (v i) (hx i hi) (hv i) (A ∩ B N) hD N (hb i hi)
    have hi1 : IntegrableOn S (A ∩ B N) P := by
      have := integrable_finset_sum' I (fun i hi => (h i hi).1)
      have e : (∑ i ∈ I, fun ω => x i ω * v i ω) = S := by
        funext ω; simp [hS]
      rw [e] at this; exact this
    have hi2' : ∀ i ∈ I, IntegrableOn (fun ω => x i ω * P[v i | G] ω) (A ∩ B N) P := by
      intro i hi
      have hφ := (setIntegral_mul_condExp G hG (x i) (P[v i | G]) (hx i hi) integrable_condExp
        (A ∩ B N) hD N (hb i hi)).1
      exact hφ
    have hi2 : IntegrableOn S' (A ∩ B N) P := by
      have := integrable_finset_sum' I hi2'
      have e : (∑ i ∈ I, fun ω => x i ω * P[v i | G] ω) = S' := by
        funext ω; simp [hS']
      rw [e] at this; exact this
    refine ⟨hi1, hi2, ?_⟩
    simp only [hS, hS']
    rw [integral_finset_sum I (fun i hi => (h i hi).1), integral_finset_sum I hi2']
    exact Finset.sum_congr rfl fun i hi => (h i hi).2
  have hSmeas : AEStronglyMeasurable S P := by
    refine Finset.aestronglyMeasurable_fun_sum I fun i hi => ?_
    exact ((hx i hi).mono hG).aestronglyMeasurable.mul (hv i).aestronglyMeasurable
  have hS'sm : StronglyMeasurable[G] S' := by
    refine Finset.stronglyMeasurable_fun_sum I fun i hi => ?_
    exact (hx i hi).mul stronglyMeasurable_condExp
  have hBmeasU : ∀ (f : Ω → ENNReal), ∫⁻ ω, f ω ∂P = ⨆ N, ∫⁻ ω in B N, f ω ∂P := by
    intro f
    rw [← setLIntegral_iUnion_of_directed f hBdir, hBU, Measure.restrict_univ]
  refine ⟨?_, ?_⟩
  · -- part (a)
    have hA : MeasurableSet[G] {ω | 0 < S' ω} := hS'sm.measurable measurableSet_Ioi
    rw [hBmeasU]
    refine iSup_le fun N => ?_
    obtain ⟨hi1, hi2, heq⟩ := key N _ hA
    have hAm : MeasurableSet {ω | 0 < S' ω} := hG _ hA
    have e1 : (fun ω => ENNReal.ofReal (S' ω)) =
        {ω | 0 < S' ω}.indicator (fun ω => ENNReal.ofReal (S' ω)) := by
      funext ω
      by_cases h : 0 < S' ω
      · simp [Set.indicator_of_mem (show ω ∈ {ω | 0 < S' ω} from h)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < S' ω} from h)]
        exact ENNReal.ofReal_eq_zero.2 (not_lt.1 h)
    calc ∫⁻ ω in B N, ENNReal.ofReal (S' ω) ∂P
        = ∫⁻ ω in {ω | 0 < S' ω} ∩ B N, ENNReal.ofReal (S' ω) ∂P := by
          conv_lhs => rw [e1]
          rw [lintegral_indicator hAm, Measure.restrict_restrict hAm]
      _ = ENNReal.ofReal (∫ ω in {ω | 0 < S' ω} ∩ B N, S' ω ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal hi2]
          exact (ae_restrict_iff' (hAm.inter (hBm N))).2
            (Eventually.of_forall fun ω hω => hω.1.le)
      _ = ENNReal.ofReal (∫ ω in {ω | 0 < S' ω} ∩ B N, S ω ∂P) := by rw [heq]
      _ ≤ ∫⁻ ω in {ω | 0 < S' ω} ∩ B N, ENNReal.ofReal (S ω) ∂P :=
          ofReal_integral_le_lintegral _ hi1
      _ ≤ ∫⁻ ω, ENNReal.ofReal (S ω) ∂P := setLIntegral_le_lintegral _ _
  · -- part (b)
    intro hint'
    set C : ℝ := (∫⁻ ω, ENNReal.ofReal (S ω) ∂P).toReal + ∫ ω, |S' ω| ∂P with hC
    have hneg : ∫⁻ ω, ENNReal.ofReal (-S ω) ∂P ≤ ENNReal.ofReal C := by
      rw [hBmeasU]
      refine iSup_le fun N => ?_
      obtain ⟨hi1, hi2, heq⟩ := key N Set.univ MeasurableSet.univ
      rw [Set.univ_inter] at hi1 hi2 heq
      have e1 : (fun ω => ENNReal.ofReal (-S ω)) =
          fun ω => ENNReal.ofReal (max (S ω) 0 - S ω) := by
        funext ω
        rcases le_total (S ω) 0 with h | h
        · rw [max_eq_right h]; simp
        · rw [max_eq_left h, sub_self, ENNReal.ofReal_zero]
          exact ENNReal.ofReal_eq_zero.2 (by linarith)
      have hpp : ∫ ω in B N, max (S ω) 0 ∂P ≤ (∫⁻ ω, ENNReal.ofReal (S ω) ∂P).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => max (S ω) 0) (Eventually.of_forall fun ω => le_max_right _ _)
          hi1.pos_part.aestronglyMeasurable]
        have h3 : (fun ω => ENNReal.ofReal (max (S ω) 0)) = fun ω => ENNReal.ofReal (S ω) := by
          funext ω; rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]; exact max_eq_left (by simp)
        rw [h3]
        exact ENNReal.toReal_mono hpos (setLIntegral_le_lintegral _ _)
      have hS'b : -∫ ω in B N, S' ω ∂P ≤ ∫ ω, |S' ω| ∂P := by
        calc -∫ ω in B N, S' ω ∂P ≤ |∫ ω in B N, S' ω ∂P| := neg_le_abs _
          _ ≤ ∫ ω in B N, |S' ω| ∂P := abs_integral_le_integral_abs
          _ ≤ ∫ ω, |S' ω| ∂P := setIntegral_le_integral hint'.abs
              (Eventually.of_forall fun ω => abs_nonneg _)
      rw [e1, ← ofReal_integral_eq_lintegral_ofReal (f := fun ω => max (S ω) 0 - S ω)
        (by exact hi1.pos_part.sub hi1)
        (Eventually.of_forall fun ω => sub_nonneg.2 (le_max_left _ _))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_sub hi1.pos_part hi1, heq, hC]
      linarith
    have hfin : HasFiniteIntegral S P := by
      unfold HasFiniteIntegral
      have e : (fun ω => ‖S ω‖ₑ) = fun ω => ENNReal.ofReal (S ω) + ENNReal.ofReal (-S ω) := by
        funext ω
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total (S ω) 0 with h | h
        · rw [abs_of_nonpos h, ENNReal.ofReal_eq_zero.2 h, zero_add]
        · rw [abs_of_nonneg h, ENNReal.ofReal_eq_zero.2 (by linarith : -S ω ≤ 0), add_zero]
      rw [e, lintegral_add_left' hSmeas.aemeasurable.ennreal_ofReal]
      exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos,
        lt_of_le_of_lt hneg ENNReal.ofReal_lt_top⟩
    have hSint : Integrable S P := ⟨hSmeas, hfin⟩
    refine ⟨hSint, ?_⟩
    have t1 := tendsto_setIntegral_of_monotone (μ := P) (f := S) hBm hBmono
      (by rw [hBU]; exact hSint.integrableOn)
    have t2 := tendsto_setIntegral_of_monotone (μ := P) (f := S') hBm hBmono
      (by rw [hBU]; exact hint'.integrableOn)
    rw [hBU, Measure.restrict_univ] at t1 t2
    have heqN : (fun N => ∫ ω in B N, S ω ∂P) = fun N => ∫ ω in B N, S' ω ∂P := by
      funext N
      have := (key N Set.univ MeasurableSet.univ).2.2
      rwa [Set.univ_inter] at this
    rw [heqN] at t1
    exact tendsto_nhds_unique t1 t2

end CSDL22

open CSDL22 in
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {T n : ℕ} (τ : Fin n → Fin (T + 1))
    (𝔽 : Fin (T + 1) → MeasurableSpace Ω)
    (h𝔽le : ∀ t, 𝔽 t ≤ mΩ) (h𝔽mono : Monotone 𝔽)
    (x v : Ω → Fin n → ℝ)
    (hx : ∀ i, ∃ g : Ω → ℝ, StronglyMeasurable[𝔽 (τ i)] g ∧ (fun ω => x ω i) =ᵐ[P] g)
    (hv : ∀ i, Integrable (fun ω => v ω i) P)
    (hperp : ∀ i, P[fun ω => v ω i | 𝔽 (τ i)] =ᵐ[P] 0)
    (hpos : ∫⁻ ω, ENNReal.ofReal (∑ i, x ω i * v ω i) ∂P ≠ ⊤) :
    Integrable (fun ω => ∑ i, x ω i * v ω i) P ∧ ∫ ω, ∑ i, x ω i * v ω i ∂P = 0 := by
  choose g hg hxg using hx
  have Q : ∀ k : ℕ, ∀ w : Ω → Fin n → ℝ, (∀ i, Integrable (fun ω => w ω i) P) →
      (∀ i, (τ i : ℕ) < k → P[fun ω => w ω i | 𝔽 (τ i)] =ᵐ[P] 0) →
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k),
        g i ω * w ω i) ∂P ≠ ⊤ →
      Integrable (fun ω => ∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k),
        g i ω * w ω i) P ∧
      ∫ ω, ∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k), g i ω * w ω i ∂P = 0 := by
    intro k
    induction k with
    | zero =>
      intro w _ _ _
      simp
    | succ k ih =>
      intro w hw hperpw hposw
      by_cases hk : k ≤ T
      · set t : Fin (T + 1) := ⟨k, by omega⟩ with ht
        set I := Finset.univ.filter (fun i => (τ i : ℕ) < k + 1) with hI
        have hgG : ∀ i ∈ I, StronglyMeasurable[𝔽 t] (g i) := by
          intro i hi
          have hi' : (τ i : ℕ) < k + 1 := (Finset.mem_filter.1 hi).2
          exact (hg i).mono (h𝔽mono (show τ i ≤ t from by
            rw [Fin.le_iff_val_le_val]; simp [ht]; omega))
        obtain ⟨ha, hb⟩ := step (𝔽 t) (h𝔽le t) I (fun i => g i) (fun i ω => w ω i) hgG
          (fun i => hw i) hposw
        set w' : Ω → Fin n → ℝ := fun ω i => P[fun ω => w ω i | 𝔽 t] ω with hw'
        have hzero : ∀ᵐ ω ∂P, ∀ i, (τ i : ℕ) = k → P[fun ω => w ω i | 𝔽 t] ω = 0 := by
          rw [ae_all_iff]
          intro i
          by_cases hik : (τ i : ℕ) = k
          · have htt : τ i = t := Fin.ext (by simp [ht, hik])
            have := hperpw i (by omega)
            rw [htt] at this
            filter_upwards [this] with ω hω _
            simpa using hω
          · exact Eventually.of_forall fun ω h => absurd h hik
        have hae : (fun ω => ∑ i ∈ I, g i ω * P[fun ω => w ω i | 𝔽 t] ω) =ᵐ[P]
            (fun ω => ∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k), g i ω * w' ω i) := by
          filter_upwards [hzero] with ω hω
          rw [hI, Finset.sum_filter, Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h1 : (τ i : ℕ) < k
          · rw [if_pos (by omega), if_pos h1]
          · rw [if_neg h1]
            by_cases h2 : (τ i : ℕ) < k + 1
            · rw [if_pos h2, hω i (by omega), mul_zero]
            · rw [if_neg h2]
        have hw'i : ∀ i, Integrable (fun ω => w' ω i) P := fun i => integrable_condExp
        have hperp' : ∀ i, (τ i : ℕ) < k → P[fun ω => w' ω i | 𝔽 (τ i)] =ᵐ[P] 0 := by
          intro i hi
          have hle : 𝔽 (τ i) ≤ 𝔽 t := h𝔽mono (show τ i ≤ t from by
            rw [Fin.le_iff_val_le_val]; simp [ht]; omega)
          exact (condExp_condExp_of_le hle (h𝔽le t)).trans (hperpw i (by omega))
        have hpos' : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k),
            g i ω * w' ω i) ∂P ≠ ⊤ := by
          have hl : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ I, g i ω * P[fun ω => w ω i | 𝔽 t] ω) ∂P =
              ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < k),
                g i ω * w' ω i) ∂P :=
            lintegral_congr_ae (hae.mono fun ω hω => by exact congrArg ENNReal.ofReal hω)
          refine ne_top_of_le_ne_top hposw ?_
          rw [← hl]
          exact ha
        obtain ⟨hintk, hintegk⟩ := ih w' hw'i hperp' hpos'
        obtain ⟨hint, heq⟩ := hb ((integrable_congr hae).2 hintk)
        refine ⟨hint, ?_⟩
        rw [heq, integral_congr_ae hae, hintegk]
      · have hfil : Finset.univ.filter (fun i => (τ i : ℕ) < k + 1) =
            Finset.univ.filter (fun i => (τ i : ℕ) < k) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have := (τ i).isLt
          omega
        rw [hfil] at hposw ⊢
        exact ih w hw (fun i hi => hperpw i (by omega)) hposw
  have hfil : Finset.univ.filter (fun i => (τ i : ℕ) < T + 1) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact (τ i).isLt
  have hxae : (fun ω => ∑ i, x ω i * v ω i) =ᵐ[P]
      (fun ω => ∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < T + 1), g i ω * v ω i) := by
    have : ∀ᵐ ω ∂P, ∀ i, x ω i = g i ω := ae_all_iff.2 fun i => hxg i
    filter_upwards [this] with ω hω
    rw [hfil]
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  have hpos2 : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < T + 1),
      g i ω * v ω i) ∂P ≠ ⊤ := by
    have hl2 : ∫⁻ ω, ENNReal.ofReal (∑ i, x ω i * v ω i) ∂P =
        ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => (τ i : ℕ) < T + 1),
          g i ω * v ω i) ∂P :=
      lintegral_congr_ae (hxae.mono fun ω hω => by exact congrArg ENNReal.ofReal hω)
    rwa [← hl2]
  obtain ⟨h1, h2⟩ := Q (T + 1) v hv (fun i _ => hperp i) hpos2
  exact ⟨(integrable_congr hxae).2 h1, by rw [integral_congr_ae hxae, h2]⟩
