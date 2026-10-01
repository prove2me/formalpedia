-- Prove2me | solution 1 for FoundationsML.OnlineLearning.online_to_batch_conversion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:46:31.679335+00:00
-- url     : https://prove2.me/submissions/0a40a1f0-67d0-4b84-87a4-ace7acbf4ec6

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_GeneralizationError
import Definitions.Def_FoundationsML_OnlineLearning_OnlineHypothesis

set_option autoImplicit false

open MeasureTheory

namespace P2M42602aaa

open FoundationsML.OnlineLearning

universe u

variable {X : Type u} [MeasurableSpace X]

lemma lossm (L : ℝ → ℝ → ℝ) (hLmeas : Measurable (Function.uncurry L)) (h : X → ℝ)
    (hh : Measurable h) : Measurable (fun p : X × ℝ => L (h p.1) p.2) :=
  hLmeas.comp ((hh.comp measurable_fst).prodMk measurable_snd)

lemma hoeff (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (L : ℝ → ℝ → ℝ) (M : ℝ)
    (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hLmeas : Measurable (Function.uncurry L)) (h : X → ℝ) (hh : Measurable h)
    (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (lam * (GeneralizationError D L h - L (h p.1) p.2))) ∂D
      ≤ ENNReal.ofReal (Real.exp (M ^ 2 * lam ^ 2 / 8)) := by
  set Y : X × ℝ → ℝ := fun p => GeneralizationError D L h - L (h p.1) p.2 with hY
  have hLm := lossm L hLmeas h hh
  have hYm : Measurable Y := measurable_const.sub hLm
  have hb : ∀ᵐ p ∂D, Y p ∈ Set.Icc (GeneralizationError D L h - M) (GeneralizationError D L h) :=
    Filter.Eventually.of_forall fun p =>
      ⟨by simp only [Y]; linarith [hLb (h p.1) p.2], by simp only [Y]; linarith [hLnn (h p.1) p.2]⟩
  have hLi : Integrable (fun p : X × ℝ => L (h p.1) p.2) D :=
    Integrable.of_mem_Icc 0 M hLm.aemeasurable (Filter.Eventually.of_forall fun p => ⟨hLnn _ _, hLb _ _⟩)
  have hc : ∫ p, Y p ∂D = 0 := by
    simp only [Y]
    rw [integral_sub (integrable_const _) hLi]
    simp [GeneralizationError]
  have key := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hYm.aemeasurable hb hc hlam
  have hint : Integrable (fun p => Real.exp (lam * Y p)) D :=
    ProbabilityTheory.integrable_exp_mul_of_mem_Icc hYm.aemeasurable hb
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  calc _ = ProbabilityTheory.mgf Y D lam := rfl
    _ ≤ _ := key
    _ = _ := by
      congr 1
      have : GeneralizationError D L h - (GeneralizationError D L h - M) = M := by ring
      rw [this, coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs]
      ring

lemma oh_succ {n : ℕ} (A : (n : ℕ) → (Fin n → X × ℝ) → (X → ℝ)) (s : X × ℝ)
    (rest : Fin n → X × ℝ) (t : Fin n) :
    OnlineHypothesis A (Fin.cons s rest : Fin (n + 1) → X × ℝ) t.succ
      = OnlineHypothesis (fun m S' => A (m + 1) (Fin.cons s S')) rest t := by
  unfold OnlineHypothesis
  show A (t.val + 1) _ = A (t.val + 1) _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have : (Fin.castLE (Nat.le_of_lt t.succ.isLt) j.succ : Fin (n + 1))
        = (Fin.castLE (Nat.le_of_lt t.isLt) j).succ := Fin.ext rfl
    rw [this, Fin.cons_succ, Fin.cons_succ]

lemma oh_zero {n : ℕ} (A : (n : ℕ) → (Fin n → X × ℝ) → (X → ℝ)) (S : Fin (n + 1) → X × ℝ) :
    OnlineHypothesis A S 0 = A 0 (fun i => i.elim0) := by
  unfold OnlineHypothesis
  show A 0 _ = A 0 _
  congr 1
  funext i
  exact i.elim0

lemma key_ind (D : Measure (X × ℝ)) [IsProbabilityMeasure D] (L : ℝ → ℝ → ℝ) (M : ℝ)
    (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hLmeas : Measurable (Function.uncurry L)) (lam : ℝ) (hlam : 0 < lam) :
    ∀ (n : ℕ) (A : (n : ℕ) → (Fin n → X × ℝ) → (X → ℝ)), (∀ m S', Measurable (A m S')) →
    ∫⁻ S, ENNReal.ofReal (Real.exp (lam * ∑ t : Fin n,
        (GeneralizationError D L (OnlineHypothesis A S t)
          - L (OnlineHypothesis A S t (S t).1) (S t).2))) ∂(Measure.pi fun _ : Fin n => D)
      ≤ ENNReal.ofReal (Real.exp (M ^ 2 * lam ^ 2 / 8)) ^ n := by
  intro n
  induction n with
  | zero =>
    intro A _
    simp
  | succ n ih =>
    intro A hA
    set K := ENNReal.ofReal (Real.exp (M ^ 2 * lam ^ 2 / 8))
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) 0
    rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    refine (lintegral_prod_le _).trans ?_
    have hsymm : ∀ (s : X × ℝ) (rest : Fin n → X × ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X × ℝ) 0).symm (s, rest)
          = (Fin.cons s rest : Fin (n + 1) → X × ℝ) := by
      intro s rest
      simp only [MeasurableEquiv.piFinSuccAbove]
      first | rfl | simp [Fin.consEquiv]
    simp_rw [hsymm]
    set h0 : X → ℝ := A 0 (fun i => i.elim0)
    have hstep : ∀ s : X × ℝ,
        ∫⁻ rest, ENNReal.ofReal (Real.exp (lam * ∑ t : Fin (n + 1),
          (GeneralizationError D L (OnlineHypothesis A (Fin.cons s rest : Fin (n + 1) → X × ℝ) t)
            - L (OnlineHypothesis A (Fin.cons s rest : Fin (n + 1) → X × ℝ) t
                ((Fin.cons s rest : Fin (n + 1) → X × ℝ) t).1)
                ((Fin.cons s rest : Fin (n + 1) → X × ℝ) t).2)))
          ∂(Measure.pi fun j : Fin n => D)
        ≤ ENNReal.ofReal (Real.exp (lam * (GeneralizationError D L h0 - L (h0 s.1) s.2))) * K ^ n := by
      intro s
      have hrw : ∀ rest : Fin n → X × ℝ,
          ENNReal.ofReal (Real.exp (lam * ∑ t : Fin (n + 1),
          (GeneralizationError D L (OnlineHypothesis A (Fin.cons s rest : Fin (n + 1) → X × ℝ) t)
            - L (OnlineHypothesis A (Fin.cons s rest : Fin (n + 1) → X × ℝ) t
                ((Fin.cons s rest : Fin (n + 1) → X × ℝ) t).1)
                ((Fin.cons s rest : Fin (n + 1) → X × ℝ) t).2)))
          = ENNReal.ofReal (Real.exp (lam * (GeneralizationError D L h0 - L (h0 s.1) s.2)))
            * ENNReal.ofReal (Real.exp (lam * ∑ t : Fin n,
              (GeneralizationError D L (OnlineHypothesis (fun m S' => A (m + 1) (Fin.cons s S')) rest t)
                - L (OnlineHypothesis (fun m S' => A (m + 1) (Fin.cons s S')) rest t (rest t).1)
                    (rest t).2))) := by
        intro rest
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Fin.sum_univ_succ]
        congr 2
        simp only [oh_succ, oh_zero, Fin.cons_zero, Fin.cons_succ]
        ring
      simp_rw [hrw]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (ih _ (fun m S' => hA _ _))
    refine (lintegral_mono hstep).trans ?_
    rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    calc _ ≤ K * K ^ n := mul_le_mul' (hoeff D L M hLnn hLb hLmeas h0 (hA _ _) lam hlam) le_rfl
      _ = K ^ (n + 1) := (pow_succ' K n).symm

end P2M42602aaa

open MeasureTheory FoundationsML.OnlineLearning in
theorem solution
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hLconv : ∀ y', ConvexOn ℝ Set.univ (fun y => L y y'))
    (hLmeas : Measurable (Function.uncurry L))
    (T : ℕ) (hT : 0 < T) (A : (n : ℕ) → (Fin n → X × ℝ) → (X → ℝ))
    (hAmeas : ∀ (n : ℕ) (S' : Fin n → X × ℝ), Measurable (A n S'))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin T => D)
      {S : Fin T → X × ℝ |
        GeneralizationError D L
            (fun x => (1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t x) ≤
          (1 / (T : ℝ)) * ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 +
            M * Real.sqrt (2 * Real.log (1 / δ) / T)}).toReal := by
  classical
  rcases le_or_gt 1 δ with h1 | h1
  · exact (sub_nonpos.2 h1).trans ENNReal.toReal_nonneg
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  rcases hM.eq_or_lt with hM0 | hMpos
  · subst hM0
    have hL0 : ∀ y y', L y y' = 0 := fun y y' => le_antisymm (hLb y y') (hLnn y y')
    have hset : {S : Fin T → X × ℝ |
        GeneralizationError D L
            (fun x => (1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t x) ≤
          (1 / (T : ℝ)) * ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 +
            0 * Real.sqrt (2 * Real.log (1 / δ) / T)} = Set.univ := by
      ext S
      simp [GeneralizationError, hL0]
    rw [hset, measure_univ]
    simp
    linarith
  set μ := Measure.pi (fun _ : Fin T => D) with hμ
  set G : Set (Fin T → X × ℝ) := {S : Fin T → X × ℝ |
        GeneralizationError D L
            (fun x => (1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t x) ≤
          (1 / (T : ℝ)) * ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 +
            M * Real.sqrt (2 * Real.log (1 / δ) / T)} with hG
  set s := Real.sqrt (2 * Real.log (1 / δ) / T) with hsdef
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ h1
  have hlog : 0 < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]; linarith
  have hs2 : s ^ 2 = 2 * Real.log (1 / δ) / T := Real.sq_sqrt (by positivity)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  set lam := 4 * s / M with hlamdef
  have hlam : 0 < lam := by positivity
  set B := toMeasurable μ G
  have hB : MeasurableSet B := measurableSet_toMeasurable μ G
  have hGB : G ⊆ B := subset_toMeasurable μ G
  have hμG : μ G = μ B := (measure_toMeasurable G).symm
  set Z : (Fin T → X × ℝ) → ℝ := fun S => ∑ t : Fin T,
    (GeneralizationError D L (OnlineHypothesis A S t)
      - L (OnlineHypothesis A S t (S t).1) (S t).2) with hZ
  have hint : ∀ h : X → ℝ, Measurable h → Integrable (fun p : X × ℝ => L (h p.1) p.2) D :=
    fun h hh => Integrable.of_mem_Icc 0 M (P2M42602aaa.lossm L hLmeas h hh).aemeasurable
      (Filter.Eventually.of_forall fun p => ⟨hLnn _ _, hLb _ _⟩)
  have hjensen : ∀ S : Fin T → X × ℝ, GeneralizationError D L
      (fun x => (1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t x)
      ≤ (1 / (T : ℝ)) * ∑ t : Fin T, GeneralizationError D L (OnlineHypothesis A S t) := by
    intro S
    have hm : ∀ t, Measurable (OnlineHypothesis A S t) := fun t => hAmeas _ _
    have havg : Measurable (fun x => (1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t x) :=
      measurable_const.mul (Finset.measurable_sum _ fun t _ => hm t)
    unfold GeneralizationError
    rw [Finset.mul_sum]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun t _ => (hint _ (hm t)).const_mul _)]
    apply integral_mono (hint _ havg) (integrable_finsetSum _ (fun t _ => (hint _ (hm t)).const_mul _))
    intro p
    have hw : ∑ _i : Fin T, (1 / (T : ℝ)) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have := (hLconv p.2).map_sum_le (t := Finset.univ) (w := fun _ => 1 / (T : ℝ))
      (p := fun t => OnlineHypothesis A S t p.1) (fun _ _ => by positivity) hw
      (fun _ _ => Set.mem_univ _)
    show L ((1 / (T : ℝ)) * ∑ t : Fin T, OnlineHypothesis A S t p.1) p.2
      ≤ ∑ i : Fin T, 1 / (T : ℝ) * L (OnlineHypothesis A S i p.1) p.2
    rw [Finset.mul_sum]
    simpa only [smul_eq_mul] using this
  have hpt : ∀ S, S ∈ Bᶜ → (T : ℝ) * (M * s) < Z S := by
    intro S hS
    have hSG : S ∉ G := fun h => hS (hGB h)
    simp only [hG, Set.mem_ofPred_eq, not_le] at hSG
    have hj := hjensen S
    have hZS : Z S = ∑ t : Fin T, GeneralizationError D L (OnlineHypothesis A S t)
        - ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 := Finset.sum_sub_distrib _ _
    rw [hZS]
    have h3 : (1 / (T : ℝ)) * ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 + M * s
        < (1 / (T : ℝ)) * ∑ t : Fin T, GeneralizationError D L (OnlineHypothesis A S t) :=
      lt_of_lt_of_le hSG hj
    have h4 := mul_lt_mul_of_pos_left h3 hTpos
    have e1 : ∀ a : ℝ, (T : ℝ) * ((1 / (T : ℝ)) * a) = a := fun a => by field_simp
    rw [mul_add, e1, e1] at h4
    linarith
  have hBc : μ Bᶜ ≤ ENNReal.ofReal δ := by
    calc μ Bᶜ = ∫⁻ S, Bᶜ.indicator 1 S ∂μ := (lintegral_indicator_one hB.compl).symm
      _ ≤ ∫⁻ S, ENNReal.ofReal (Real.exp (-(lam * (T * (M * s)))))
            * ENNReal.ofReal (Real.exp (lam * Z S)) ∂μ := by
          apply lintegral_mono
          intro S
          by_cases hS : S ∈ Bᶜ
          · rw [Set.indicator_of_mem hS, Pi.one_apply]
            show (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (-(lam * (T * (M * s)))))
              * ENNReal.ofReal (Real.exp (lam * Z S))
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
              ← Real.exp_add, ENNReal.one_le_ofReal]
            apply Real.one_le_exp
            nlinarith [hpt S hS]
          · rw [Set.indicator_of_notMem hS]
            exact bot_le
      _ = ENNReal.ofReal (Real.exp (-(lam * (T * (M * s)))))
            * ∫⁻ S, ENNReal.ofReal (Real.exp (lam * Z S)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (-(lam * (T * (M * s)))))
            * ENNReal.ofReal (Real.exp (M ^ 2 * lam ^ 2 / 8)) ^ T := by
          exact mul_le_mul' le_rfl (P2M42602aaa.key_ind D L M hLnn hLb hLmeas lam hlam T A hAmeas)
      _ = ENNReal.ofReal (Real.exp (-(lam * (T * (M * s))) + T * (M ^ 2 * lam ^ 2 / 8))) := by
          rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          have e : lam * M = 4 * s := by
            rw [hlamdef]; field_simp
          have e2 : -(lam * (T * (M * s))) + T * (M ^ 2 * lam ^ 2 / 8)
              = -((lam * M) * T * s) + T * (lam * M) ^ 2 / 8 := by ring
          have e3 : -(lam * (T * (M * s))) + T * (M ^ 2 * lam ^ 2 / 8)
              = 4 * Real.log δ := by
            rw [e2, e]
            have : -(4 * s * T * s) + T * (4 * s) ^ 2 / 8 = -(2 * T * s ^ 2) := by ring
            rw [this, hs2, one_div, Real.log_inv]
            field_simp
            ring
          rw [e3]
          calc Real.exp (4 * Real.log δ) ≤ Real.exp (Real.log δ) := by
                apply Real.exp_le_exp.2; linarith
            _ = δ := Real.exp_log hδ
  rw [hμG]
  have hsum : μ B + μ Bᶜ = 1 := by rw [measure_add_measure_compl hB, measure_univ]
  have hBt : (μ B).toReal = 1 - (μ Bᶜ).toReal := by
    have := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [ENNReal.toReal_one] at this
    linarith
  have hle : (μ Bᶜ).toReal ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ.le hBc
  linarith
