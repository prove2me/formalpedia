-- Prove2me | solution 1 for FoundationsML.OnlineLearning.online_to_batch_martingale_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:56:04.069712+00:00
-- url     : https://prove2.me/submissions/db30afe3-3b99-475e-863c-f345a39c6d6a

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_GeneralizationError
import Definitions.Def_FoundationsML_OnlineLearning_OnlineHypothesis

set_option autoImplicit false

open MeasureTheory

namespace P763bf45d

/-- Sum of the history-adapted increments. -/
noncomputable def Vsum {α : Type*} (g : (n : ℕ) → (Fin n → α) → α → ℝ) (n : ℕ)
    (S : Fin n → α) : ℝ :=
  ∑ t : Fin n, g t.val (fun i => S (Fin.castLE (Nat.le_of_lt t.isLt) i)) (S t)

theorem Vsum_succ {α : Type*} (g : (n : ℕ) → (Fin n → α) → α → ℝ) (n : ℕ)
    (S : Fin (n + 1) → α) :
    Vsum g (n + 1) S = Vsum g n (Fin.init S) + g n (Fin.init S) (S (Fin.last n)) := by
  rw [Vsum, Fin.sum_univ_castSucc]
  rfl

theorem lintegral_pi_snoc_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (n : ℕ) (Φ : (Fin n → α) → α → ENNReal) :
    ∫⁻ S, Φ (Fin.init S) (S (Fin.last n)) ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) ≤
      ∫⁻ p, ∫⁻ s, Φ p s ∂ν ∂(Measure.pi (fun _ : Fin n => ν)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) (Fin.last n)
  set Ψ : α × (Fin n → α) → ENNReal := fun q => Φ q.2 q.1
  have hS : ∀ S : Fin (n + 1) → α, Φ (Fin.init S) (S (Fin.last n)) = Ψ (e S) := by
    intro S
    have he : e S = (S (Fin.last n), Fin.removeNth (Fin.last n) S) := rfl
    simp only [Ψ, he, Fin.removeNth_last]
  calc ∫⁻ S, Φ (Fin.init S) (S (Fin.last n)) ∂(Measure.pi (fun _ : Fin (n + 1) => ν))
      = ∫⁻ S, Ψ (e S) ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) := by
        congr 1; funext S; exact hS S
    _ = ∫⁻ q, Ψ q ∂(ν.prod (Measure.pi (fun _ : Fin n => ν))) :=
        hmp.lintegral_comp_emb e.measurableEmbedding Ψ
    _ = ∫⁻ q, Ψ q.swap ∂((Measure.pi (fun _ : Fin n => ν)).prod ν) :=
        ((Measure.measurePreserving_swap).lintegral_comp_emb
          (MeasurableEquiv.prodComm).measurableEmbedding Ψ).symm
    _ ≤ ∫⁻ p, ∫⁻ s, Ψ (p, s).swap ∂ν ∂(Measure.pi (fun _ : Fin n => ν)) :=
        lintegral_prod_le _

theorem lintegral_exp_Vsum_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : (n : ℕ) → (Fin n → α) → α → ℝ) (lam c : ℝ)
    (hg : ∀ n p, ∫⁻ s, ENNReal.ofReal (Real.exp (lam * g n p s)) ∂ν ≤ ENNReal.ofReal c) :
    ∀ n : ℕ, ∫⁻ S, ENNReal.ofReal (Real.exp (lam * Vsum g n S))
      ∂(Measure.pi (fun _ : Fin n => ν)) ≤ ENNReal.ofReal c ^ n := by
  intro n
  induction n with
  | zero => simp [Vsum]
  | succ n ih =>
    have hF : ∀ S : Fin (n + 1) → α, ENNReal.ofReal (Real.exp (lam * Vsum g (n + 1) S)) =
        ENNReal.ofReal (Real.exp (lam * Vsum g n (Fin.init S))) *
          ENNReal.ofReal (Real.exp (lam * g n (Fin.init S) (S (Fin.last n)))) := by
      intro S
      rw [Vsum_succ, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp_rw [hF]
    refine (lintegral_pi_snoc_le ν n (fun p s => ENNReal.ofReal (Real.exp (lam * Vsum g n p)) *
      ENNReal.ofReal (Real.exp (lam * g n p s)))).trans ?_
    calc ∫⁻ p, ∫⁻ s, ENNReal.ofReal (Real.exp (lam * Vsum g n p)) *
          ENNReal.ofReal (Real.exp (lam * g n p s)) ∂ν ∂(Measure.pi (fun _ : Fin n => ν))
        ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (lam * Vsum g n p)) * ENNReal.ofReal c
            ∂(Measure.pi (fun _ : Fin n => ν)) := by
          refine lintegral_mono fun p => ?_
          dsimp only
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact hg n p
      _ = (∫⁻ p, ENNReal.ofReal (Real.exp (lam * Vsum g n p))
            ∂(Measure.pi (fun _ : Fin n => ν))) * ENNReal.ofReal c :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c ^ n * ENNReal.ofReal c := by gcongr
      _ = ENNReal.ofReal c ^ (n + 1) := (pow_succ _ _).symm

theorem chernoff {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (g : (n : ℕ) → (Fin n → α) → α → ℝ) (lam c ε : ℝ)
    (hlam : 0 ≤ lam)
    (hg : ∀ n p, ∫⁻ s, ENNReal.ofReal (Real.exp (lam * g n p s)) ∂ν ≤ ENNReal.ofReal c)
    (T : ℕ) (E : Set (Fin T → α)) (hE : MeasurableSet E) (hEV : ∀ S ∈ E, ε < Vsum g T S) :
    Measure.pi (fun _ : Fin T => ν) E ≤
      ENNReal.ofReal (Real.exp (-(lam * ε))) * ENNReal.ofReal c ^ T := by
  rw [← lintegral_indicator_one hE]
  calc ∫⁻ S, E.indicator 1 S ∂(Measure.pi (fun _ : Fin T => ν))
      ≤ ∫⁻ S, ENNReal.ofReal (Real.exp (-(lam * ε))) *
          ENNReal.ofReal (Real.exp (lam * Vsum g T S)) ∂(Measure.pi (fun _ : Fin T => ν)) := by
        refine lintegral_mono fun S => ?_
        dsimp only
        by_cases hS : S ∈ E
        · rw [Set.indicator_of_mem hS, Pi.one_apply,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          have : 0 ≤ -(lam * ε) + lam * Vsum g T S := by
            have := hEV S hS
            nlinarith
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_exp this)
        · rw [Set.indicator_of_notMem hS]
          exact bot_le
    _ = ENNReal.ofReal (Real.exp (-(lam * ε))) *
          ∫⁻ S, ENNReal.ofReal (Real.exp (lam * Vsum g T S)) ∂(Measure.pi (fun _ : Fin T => ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact lintegral_exp_Vsum_le ν g lam c hg T

theorem measure_ge_of_compl {β : Type*} [MeasurableSpace β] (μ : Measure β)
    [IsProbabilityMeasure μ] (G : Set β) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ E, MeasurableSet E → E ⊆ Gᶜ → μ E ≤ ENNReal.ofReal δ) :
    1 - δ ≤ (μ G).toReal := by
  set F := toMeasurable μ G
  have hF : MeasurableSet F := measurableSet_toMeasurable μ G
  have hGF : μ G = μ F := (measure_toMeasurable G).symm
  have hsub : Fᶜ ⊆ Gᶜ := Set.compl_subset_compl.mpr (subset_toMeasurable μ G)
  have hE := h Fᶜ hF.compl hsub
  have hcomp : μ F = 1 - μ Fᶜ := by
    rw [prob_compl_eq_one_sub hF, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  have hle : μ Fᶜ ≤ 1 := prob_le_one
  rw [hGF, hcomp, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one]
  have := ENNReal.toReal_le_of_le_ofReal hδ hE
  linarith

theorem aux_gap (T M s a b : ℝ) (hT : 0 < T)
    (h : ¬ (1 / T * a ≤ 1 / T * b + M * s)) : T * M * s < a - b := by
  have h1 : M * s < (1 / T) * (a - b) := by rw [mul_sub]; linarith [not_le.mp h]
  have h2 : T * ((1 / T) * (a - b)) = a - b := by field_simp
  calc T * M * s = T * (M * s) := by ring
    _ < T * ((1 / T) * (a - b)) := mul_lt_mul_of_pos_left h1 hT
    _ = a - b := h2

end P763bf45d

open MeasureTheory FoundationsML.OnlineLearning in
theorem solution
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hLmeas : Measurable (Function.uncurry L))
    (T : ℕ) (hT : 0 < T) (A : (n : ℕ) → (Fin n → X × ℝ) → (X → ℝ))
    (hAmeas : ∀ (n : ℕ) (S' : Fin n → X × ℝ), Measurable (A n S'))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin T => D)
      {S : Fin T → X × ℝ |
        (1 / (T : ℝ)) * ∑ t : Fin T, GeneralizationError D L (OnlineHypothesis A S t) ≤
          (1 / (T : ℝ)) * ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 +
            M * Real.sqrt (2 * Real.log (1 / δ) / T)}).toReal := by
  by_cases hδ1 : 1 ≤ δ
  · exact le_trans (by linarith) ENNReal.toReal_nonneg
  rw [not_le] at hδ1
  rcases eq_or_lt_of_le hM with hM0 | hMpos
  · subst hM0
    have hL0 : ∀ y y', L y y' = 0 := fun y y' => le_antisymm (hLb y y') (hLnn y y')
    simp [GeneralizationError, hL0]
    linarith
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  set ℓ := Real.log (1 / δ) with hℓ
  have hℓpos : 0 < ℓ := Real.log_pos (one_lt_one_div hδ hδ1)
  have hlogδ : Real.log δ = -ℓ := by rw [hℓ, one_div, Real.log_inv, neg_neg]
  set s := Real.sqrt (2 * ℓ / T) with hs
  have hs2 : s ^ 2 = 2 * ℓ / T := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set lam := 4 * s / M with hlam
  have hlampos : 0 < lam := by positivity
  set g : (n : ℕ) → (Fin n → X × ℝ) → X × ℝ → ℝ := fun n p x =>
    GeneralizationError D L (A n p) - L (A n p x.1) x.2 with hg
  set c := Real.exp ((M / 2) ^ 2 * lam ^ 2 / 2) with hc
  have hstep : ∀ n p, ∫⁻ x, ENNReal.ofReal (Real.exp (lam * g n p x)) ∂D ≤
      ENNReal.ofReal c := by
    intro n p
    have hmeasL : Measurable (fun x : X × ℝ => L (A n p x.1) x.2) :=
      hLmeas.comp (((hAmeas n p).comp measurable_fst).prodMk measurable_snd)
    have hmeas : Measurable (g n p) := measurable_const.sub hmeasL
    have hint : Integrable (fun x : X × ℝ => L (A n p x.1) x.2) D :=
      Integrable.of_mem_Icc 0 M hmeasL.aemeasurable
        (Filter.Eventually.of_forall (fun x => ⟨hLnn _ _, hLb _ _⟩))
    have hb : ∀ᵐ x ∂D, g n p x ∈ Set.Icc (GeneralizationError D L (A n p) - M)
        (GeneralizationError D L (A n p)) := by
      refine Filter.Eventually.of_forall (fun x => ⟨?_, ?_⟩) <;> simp only [hg] <;>
        linarith [hLnn (A n p x.1) x.2, hLb (A n p x.1) x.2]
    have hc0 : ∫ x, g n p x ∂D = 0 := by
      simp only [hg]
      rw [integral_sub (integrable_const _) hint, integral_const]
      simp [GeneralizationError]
    have hmgf := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hmeas.aemeasurable hb hc0
      hlampos
    rw [← ofReal_integral_eq_lintegral_ofReal
      (ProbabilityTheory.integrable_exp_mul_of_mem_Icc hmeas.aemeasurable hb)
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
    apply ENNReal.ofReal_le_ofReal
    refine hmgf.trans (le_of_eq ?_)
    rw [hc, show GeneralizationError D L (A n p) - (GeneralizationError D L (A n p) - M) = M by
      ring]
    congr 1
    push_cast
    rw [Real.norm_of_nonneg hM]
  set ε := (T : ℝ) * M * s with hε
  refine P763bf45d.measure_ge_of_compl _ _ δ hδ.le ?_
  intro E hE hEsub
  have hEV : ∀ S ∈ E, ε < P763bf45d.Vsum g T S := by
    intro S hS
    have hn := hEsub hS
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hn
    have hV : P763bf45d.Vsum g T S = ∑ t : Fin T, GeneralizationError D L (OnlineHypothesis A S t) -
        ∑ t : Fin T, L (OnlineHypothesis A S t (S t).1) (S t).2 := by
      rw [← Finset.sum_sub_distrib]
      rfl
    rw [hV]
    exact P763bf45d.aux_gap _ _ _ _ _ hTpos hn
  refine (P763bf45d.chernoff D g lam c ε hlampos.le hstep T E hE hEV).trans ?_
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_nat_mul, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_log hδ]
  apply Real.exp_le_exp.mpr
  have hM0 : M ≠ 0 := hMpos.ne'
  have e1 : lam * ε = 4 * (T * s ^ 2) := by rw [hlam, hε]; field_simp
  have e2 : (T : ℝ) * ((M / 2) ^ 2 * lam ^ 2 / 2) = 2 * (T * s ^ 2) := by
    rw [hlam]; field_simp; ring
  have e3 : (T : ℝ) * s ^ 2 = 2 * ℓ := by rw [hs2]; field_simp
  rw [e1, e2, e3, hlogδ]
  linarith
