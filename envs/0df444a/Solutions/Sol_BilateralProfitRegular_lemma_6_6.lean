-- Prove2me | solution 1 for BilateralProfitRegular.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T16:25:40.056107+00:00
-- url     : https://prove2.me/submissions/d035b278-fbd0-48c1-aaed-5e0d17b46e94

import Mathlib
import Definitions.Def_BilateralProfitRegular_ConvexBandit
import Definitions.Def_BilateralProfitRegular_Refinement
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Theorems.Thm_BilateralProfitRegular_lemma_6_2
import Definitions.Def_BilateralProfitRegular_InitRegular


section BundlePart000




namespace BilateralProfitRegular.RefineGeometry

open Set MechanismDesign.BilateralTrade BilateralProfit MeasureTheory

private theorem intT_subset_unitSq : intT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem onUnit_facts (E : Environment) (hE : OnUnit E) :
    (∀ a, 0 ≤ P E a ∧ P E a ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, P E a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, 0 < mu E a ↔ a ∈ intT) ∧
    (0 < muStar E ∧ muStar E ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, mu E a ≤ muStar E) ∧
    (∃ a ∈ intT, mu E a = muStar E) := by
  obtain ⟨_, _, hp, hf, _, _, _, _, hm, hs, hu, he, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  exact ⟨hp, hf, hm, hs, hu, he⟩

private theorem P_factor (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) :
    P E x = E.cdfS x.1 * (1 - E.cdfB x.2) :=
  (onUnit_facts E hE).2.1 x hx

private theorem mu_formula (E : Environment) (x : ℝ × ℝ) :
    mu E x = (x.2 - x.1) * P E x := rfl

private theorem mu_le_muStar (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) : mu E x ≤ muStar E :=
  (onUnit_facts E hE).2.2.2.2.1 x hx

private theorem cdfS_pos (E : Environment) (hE : OnUnit E) {p : ℝ} (hp : p ∈ Ioc 0 1) :
    0 < E.cdfS p := by
  have hf := E.fS_intervalIntegrable
  rw [hE.1, hE.2.1] at hf
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hp.1
  · apply hf.mono_set
    rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hp.2
  · intro t ht
    exact E.fS_pos t (by rw [hE.1, hE.2.1]; exact ⟨ht.1.le, ht.2.le.trans hp.2⟩)

private theorem tailB_eq_integral (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    1 - E.cdfB q = ∫ t in q..1, E.fB t := by
  have hf := E.fB_intervalIntegrable
  have ht := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at hf ht
  have h₁ := hf.mono_set (show uIcc 0 q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have h₂ := hf.mono_set (show uIcc q 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl)
  rw [Environment.cdfB, hE.2.2.1]
  linarith [intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private theorem tailB_pos (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Ico 0 1) :
    0 < 1 - E.cdfB q := by
  rw [tailB_eq_integral E hE ⟨hq.1, hq.2.le⟩]
  have hf := E.fB_intervalIntegrable
  rw [hE.2.2.1, hE.2.2.2] at hf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hq.2
  · apply hf.mono_set
    rw [uIcc_of_le hq.2.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl
  · intro t ht
    exact E.fB_pos t (by rw [hE.2.2.1, hE.2.2.2]; exact ⟨hq.1.trans ht.1.le, ht.2.le⟩)

private theorem intT_cdf_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < E.cdfS x.1 ∧ 0 < 1 - E.cdfB x.2 :=
  ⟨cdfS_pos E hE ⟨hx.1, (intT_subset_unitSq hx).1.2⟩,
    tailB_pos E hE ⟨(intT_subset_unitSq hx).2.1, hx.2.2⟩⟩

private theorem balance_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < balance E x :=
  Real.sqrt_pos.2 (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2)

private theorem balance_sq (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    balance E x ^ 2 = E.cdfS x.1 / (1 - E.cdfB x.2) :=
  Real.sq_sqrt (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2).le

private theorem auxProfit_pos (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < auxProfit E lam x := by
  have hm := intT_cdf_pos E hE hx
  unfold auxProfit
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hx.2.1))
    (pow_pos (add_pos (div_pos hlam hm.1) (div_pos (inv_pos.mpr hlam) hm.2)) _)

end BilateralProfitRegular.RefineGeometry
end BundlePart000


section BundlePart001




namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade Classical

private theorem param_mul_exp_log {lam target : ℝ} (hlam : 0 < lam) (htarget : 0 < target) :
    target * Real.exp (Real.log (lam / target)) = lam := by
  rw [Real.exp_log (div_pos hlam htarget)]
  field_simp

private theorem abs_log_div_calibrated_le {lam lam' target s : ℝ}
    (hlam : 0 < lam) (hlam' : 0 < lam') (htarget : 0 < target)
    (h : |Real.log (lam / target)| ≤ s) (h' : |Real.log (lam' / target)| ≤ s) :
    |Real.log (lam' / lam)| ≤ 2 * s := by
  have heq : Real.log (lam' / lam) =
      Real.log (lam' / target) + -Real.log (lam / target) := by
    rw [Real.log_div hlam'.ne' hlam.ne', Real.log_div hlam'.ne' htarget.ne',
      Real.log_div hlam.ne' htarget.ne']
    ring
  calc
    _ = |Real.log (lam' / target) + -Real.log (lam / target)| := congrArg abs heq
    _ ≤ |Real.log (lam' / target)| + |-Real.log (lam / target)| := abs_add_le _ _
    _ ≤ 2 * s := by simpa only [abs_neg, two_mul] using add_le_add h' h

/-- The deterministic successive-elimination guarantee, using the auxiliary-profit facts. -/
private theorem successive_elimination :
    (∀ (η : ℝ), 0 < η → η < 1 →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (N : ℕ) (cs : Fin N → Candidate),
        η < δ → δ ≤ muStar E → muStar E < 6 * δ → (∀ i, (cs i).Valid E δ) →
      ∀ istar : Fin N, (cs istar).NearOpt E η δ →
      ∀ (A : ℕ → Finset (Fin N)) (z y : ℕ → Fin N → ℝ × ℝ) (ρ rhat : ℕ → Fin N → ℝ),
        A 0 = Finset.univ → (∀ i, z 0 i = (cs i).root) →
        (∀ j i, i ∈ A (j + 1) ↔
          i ∈ A j ∧ ∀ l ∈ A j, rhat j l - 10 * (η + acc δ j) ≤ rhat j i) →
        (∀ j, ∀ i ∈ A (j + 1), z (j + 1) i = y j i) →
        (∀ i, ∀ ρ' : ℝ, CalibValid E η δ (cs i) (cs i).root ρ' →
          muStar E - auxProfit E (ρ' * balance E (cs i).root) (cs i).root ≤
            65 * (η + acc δ 0)) ∧
        ∀ j : ℕ,
          (∀ j' ≤ j, ∀ i ∈ A j',
            CalibValid E η δ (cs i) (z j' i) (ρ j' i) ∧ y j' i ∈ (cs i).region ∧
            (∀ x ∈ (cs i).region,
              auxProfit E (ρ j' i * balance E (z j' i)) x - acc δ j' ≤ rhat j' i) ∧
            rhat j' i ≤ auxProfit E (ρ j' i * balance E (z j' i)) (y j' i) + acc δ j') →
          istar ∈ A (j + 1) ∧
          ∀ i ∈ A (j + 1), ∀ ρ' : ℝ, CalibValid E η δ (cs i) (z (j + 1) i) ρ' →
            muStar E - auxProfit E (ρ' * balance E (z (j + 1) i)) (z (j + 1) i) ≤
              65 * (η + acc δ (j + 1))) := by
  have balance_positive (E : Environment) (hE : RegularUnit E) (x : ℝ × ℝ) (hx : x ∈ intT) :
      0 < balance E x :=
    RefineGeometry.balance_pos E hE.1 hx
  have profit_bounds (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
      (x : ℝ × ℝ) (hx : x ∈ intT) : 0 < auxProfit E lam x ∧ auxProfit E lam x ≤ muStar E := by
    obtain ⟨_, _, _, hpos, hupper, _, _⟩ := (lemma_6_2 E hE lam hlam).2 x hx
    exact ⟨hpos, hupper.trans (RefineGeometry.mu_le_muStar E hE.1 (RefineGeometry.intT_subset_unitSq hx))⟩
  have profit_stability (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
      (x : ℝ × ℝ) (hx : x ∈ intT) (θ : ℝ) :
      muStar E - auxProfit E (lam * Real.exp θ) x ≤
        2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 :=
    by
      obtain ⟨_, _, _, _, _, _, hstable⟩ := (lemma_6_2 E hE lam hlam).2 x hx
      exact hstable θ
  intro η hη _ E hE δ N cs hηδ hδmu hmu hvalid istar hnear A z y ρ rhat hA0 hz0 hA hz
  have hδ : 0 < δ := hη.trans hηδ
  have hmu_pos : 0 < muStar E := hδ.trans_le hδmu
  have hparam (i : Fin N) : 0 < (cs i).param E :=
    mul_pos (Real.exp_pos _) (balance_positive E hE _ ((hvalid i).1 (hvalid i).2.2.2.1))
  have hroot (i : Fin N) : (cs i).root ∈ intT := (hvalid i).1 (hvalid i).2.2.2.1
  have hacc (j : ℕ) : 0 ≤ acc δ j := by unfold acc; positivity
  have hacc_succ (j : ℕ) : acc δ j = 2 * acc δ (j + 1) := by
    unfold acc
    rw [pow_succ]
    ring
  constructor
  · intro i ρ' hρ'
    have hpos := (profit_bounds E hE _ (mul_pos hρ'.1 (balance_positive E hE _ (hroot i)))
      _ (hroot i)).1
    simp only [acc, pow_zero, mul_one]
    linarith
  have hstep : ∀ k : ℕ, istar ∈ A k →
        (∀ i ∈ A k, z k i ∈ (cs i).region) →
        (∀ i ∈ A k,
          CalibValid E η δ (cs i) (z k i) (ρ k i) ∧ y k i ∈ (cs i).region ∧
          (∀ x ∈ (cs i).region,
            auxProfit E (ρ k i * balance E (z k i)) x - acc δ k ≤ rhat k i) ∧
          rhat k i ≤ auxProfit E (ρ k i * balance E (z k i)) (y k i) + acc δ k) →
        istar ∈ A (k + 1) ∧
        ∀ i ∈ A (k + 1), ∀ ρ' : ℝ, CalibValid E η δ (cs i) (z (k + 1) i) ρ' →
          muStar E - auxProfit E (ρ' * balance E (z (k + 1) i)) (z (k + 1) i) ≤
            65 * (η + acc δ (k + 1)) := by
    intro k histar hre g
    let lam (i : Fin N) := ρ k i * balance E (z k i)
    have hlam (i : Fin N) (hi : i ∈ A k) : 0 < lam i :=
      mul_pos (g i hi).1.1 (balance_positive E hE _ ((hvalid i).1 (hre i hi)))
    have hy (i : Fin N) (hi : i ∈ A k) : y k i ∈ intT :=
      (hvalid i).1 (g i hi).2.1
    have hlow : muStar E - 3 * η - acc δ k ≤ rhat k istar := by
      obtain ⟨x, hx, hxlow⟩ := hnear _ (g istar histar).1.2
      rw [param_mul_exp_log (hlam istar histar) (hparam istar)] at hxlow
      linarith [(g istar histar).2.2.1 x hx]
    have hupp (i : Fin N) (hi : i ∈ A k) : rhat k i ≤ muStar E + acc δ k :=
      (g i hi).2.2.2.trans
        (add_le_add_left (profit_bounds E hE _ (hlam i hi) _ (hy i hi)).2 _)
    constructor
    · apply (hA k istar).2
      refine ⟨histar, fun i hi => ?_⟩
      linarith [hupp i hi, hacc k]
    · intro i hi ρ' hρ'
      obtain ⟨hik, hretained⟩ := (hA k i).1 hi
      rw [hz k i hi] at hρ' ⊢
      let lam' := ρ' * balance E (y k i)
      have hlam' : 0 < lam' := mul_pos hρ'.1 (balance_positive E hE _ (hy i hik))
      have hrefloss : muStar E - auxProfit E (lam i) (y k i) ≤ 16 * (η + acc δ k) := by
        linarith [hretained istar histar, (g i hik).2.2.2, hacc k]
      let θ := Real.log (lam' / lam i)
      have hθ : |θ| ≤ 2 * (1 / 1000 * Real.sqrt (η / δ)) :=
        abs_log_div_calibrated_le (hlam i hik) hlam' (hparam i) (g i hik).1.2 hρ'.2
      have hθsq : θ ^ 2 ≤ (1 / 250000 : ℝ) * (η / δ) := by
        calc
          θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
          _ ≤ (2 * (1 / 1000 * Real.sqrt (η / δ))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg θ) hθ 2
          _ = (1 / 250000 : ℝ) * (η / δ) := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hη.le hδ.le)]
            ring
      have herr : 2 * muStar E * θ ^ 2 ≤ (48 / 1000000 : ℝ) * η := by
        calc
          _ ≤ 2 * (6 * δ) * θ ^ 2 := by gcongr
          _ ≤ 2 * (6 * δ) * ((1 / 250000 : ℝ) * (η / δ)) := by gcongr
          _ = _ := by field_simp; ring
      have hstable := profit_stability E hE _ (hlam i hik) _ (hy i hik) θ
      change muStar E - auxProfit E (lam i * Real.exp (Real.log (lam' / lam i))) _ ≤ _ at hstable
      rw [param_mul_exp_log hlam' (hlam i hik)] at hstable
      change muStar E - auxProfit E lam' _ ≤ _
      linarith [hacc_succ k, hacc (k + 1)]

  intro j
  induction j with
  | zero =>
    intro hgood
    exact hstep 0 (hA0.symm ▸ Finset.mem_univ istar)
      (fun i _ => by simpa only [hz0 i] using (hvalid i).2.2.2.1) (hgood 0 le_rfl)
  | succ j ih =>
    intro hgood
    have hprev : istar ∈ A (j + 1) :=
      (ih (fun j' hj' => hgood j' (hj'.trans (Nat.le_succ _)))).1
    apply hstep (j + 1) hprev _ (hgood (j + 1) le_rfl)
    intro i hi
    rw [hz j i hi]
    exact (hgood j (Nat.le_succ _) i ((hA j i).1 hi).1).2.1

end BilateralProfitRegular
end BundlePart001


section BundlePart002


namespace BilateralProfitRegular.BanditAlg

open MeasureTheory ProbabilityTheory ENNReal Classical

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
variable (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω)

@[fun_prop]
private theorem measurable_snoc_pair {m : ℕ} :
    Measurable (fun p : (Fin m → X × ℝ) × (X × ℝ) => Fin.snoc (α := fun _ => X × ℝ) p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_snd :
      Measurable (Prod.snd : (Fin m → X × ℝ) × (X × ℝ) → X × ℝ))
  · simp only [Fin.snoc_castSucc]
    fun_prop

private theorem measurable_go (hν : ∀ τ, IsMarkovKernel (ν τ))
    {c : X → ℝ≥0∞} (hc : Measurable c)
    {f : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (hf : ∀ τ, Measurable (f τ))
    (k τ : ℕ) :
    Measurable (fun p : Ω × (Fin τ → X × ℝ) => alg.go ν c f k τ p.1 p.2) := by
  induction k generalizing τ with
  | zero =>
    exact (hf τ).comp measurable_snd
  | succ k ih =>
    simp only [go]
    let κ := (ν τ).comap (fun p : Ω × (Fin τ → X × ℝ) => (p.2, alg.query τ p.1 p.2))
      (measurable_snd.prodMk (alg.measurable_query τ))
    apply (hc.comp (alg.measurable_query τ)).add
    have hmap : Measurable (fun p : (Ω × (Fin τ → X × ℝ)) × ℝ =>
        (p.1.1, Fin.snoc (α := fun _ => X × ℝ) p.1.2 (alg.query τ p.1.1 p.1.2, p.2))) :=
      measurable_fst.fst.prodMk (measurable_snoc_pair.comp
        (measurable_fst.snd.prodMk (((alg.measurable_query τ).comp measurable_fst).prodMk
          measurable_snd)))
    have hm := Measurable.lintegral_kernel_prod_right' (κ := κ) ((ih (τ + 1)).comp hmap)
    simpa only [κ, Kernel.comap_apply, Function.comp_apply] using hm

private theorem go_zero_mono_on (K : Set X) (hK : alg.QueriesIn K)
    {f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (k τ : ℕ) (ω : Ω)
    (h : Fin τ → X × ℝ) (hh : ∀ i, (h i).1 ∈ K)
    (hfg : ∀ τ h, (∀ i, (h i).1 ∈ K) → f τ h ≤ g τ h) :
    alg.go ν 0 f k τ ω h ≤ alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero => simpa only [go] using hfg τ h hh
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    apply lintegral_mono
    intro v
    apply ih
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hK τ ω h
    · simpa only [Fin.snoc_castSucc] using hh j

private theorem measurable_terminal {n : ℕ} {f : (Fin n → X × ℝ) → ℝ≥0∞}
    (hf : Measurable f) (τ : ℕ) :
    Measurable (fun h : Fin τ → X × ℝ =>
      if hτ : τ = n then f (fun i => h (Fin.cast hτ.symm i)) else 0) := by
  split <;> rename_i h
  · subst τ
    simpa only [Fin.cast_eq_self] using hf
  · exact measurable_const

private theorem trajExp_mono_on (K : Set X) (hK : alg.QueriesIn K) {n : ℕ}
    {f g : (Fin n → X × ℝ) → ℝ≥0∞} (hfg : ∀ h, (∀ i, (h i).1 ∈ K) → f h ≤ g h) :
    alg.trajExp ν P n f ≤ alg.trajExp ν P n g := by
  unfold trajExp
  apply lintegral_mono
  intro ω
  apply alg.go_zero_mono_on ν K hK
  · exact fun i => i.elim0
  · intro τ h hh
    by_cases hτ : τ = n
    · simpa only [dif_pos hτ] using (hfg _ (fun i => hh (Fin.cast hτ.symm i)))
    · simp [hτ]

private theorem go_zero_const {f : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞}
    (hν : ∀ τ, IsMarkovKernel (ν τ))
    (d : ℝ≥0∞) (n k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ)
    (ht : k + τ = n) (hf : ∀ h, f n h = d) : alg.go ν 0 f k τ ω h = d := by
  induction k generalizing τ with
  | zero =>
    simp only [zero_add] at ht
    subst τ
    exact hf h
  | succ k ih =>
    have := hν τ
    have ht' : k + (τ + 1) = n := by omega
    simp only [go, Pi.zero_apply, zero_add, ih (τ + 1) _ ht', lintegral_const, measure_univ, mul_one]

private theorem trajExp_const (hν : ∀ τ, IsMarkovKernel (ν τ)) [IsProbabilityMeasure P]
    (n : ℕ) (d : ℝ≥0∞) : alg.trajExp ν P n (fun _ => d) = d := by
  unfold trajExp
  have hω : ∀ ω, alg.go ν 0 (fun τ _ => if τ = n then d else 0) n 0 ω Fin.elim0 = d :=
    fun ω => alg.go_zero_const ν hν d n n 0 ω Fin.elim0 (by simp) (by simp)
  simp only [dite_eq_ite]
  change ∫⁻ ω, alg.go ν 0 (fun τ _ => if τ = n then d else 0) n 0 ω Fin.elim0 ∂P = d
  simp only [hω, lintegral_const, measure_univ, mul_one]

private theorem go_zero_upper (k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ)
    (f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞) (a : ℝ≥0∞)
    (hf : ∀ τ, Measurable (f τ)) (hg : ∀ τ, Measurable (g τ))
    (hν : ∀ τ, IsMarkovKernel (ν τ)) :
    alg.go ν 0 (fun s h => a * f s h + g s h) k τ ω h ≤
      a * alg.go ν 0 f k τ ω h + alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero => rfl
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    refine (lintegral_mono (fun v => ih _ _)).trans ?_
    have hh : Measurable fun v : ℝ =>
        (ω, Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v)) := by
      apply measurable_const.prodMk
      exact measurable_snoc_pair.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hmf := (alg.measurable_go ν hν (c := 0) measurable_const hf k (τ + 1)).comp hh
    have hmg := (alg.measurable_go ν hν (c := 0) measurable_const hg k (τ + 1)).comp hh
    change Measurable (fun v => alg.go ν 0 f k (τ + 1) ω
      (Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v))) at hmf
    change Measurable (fun v => alg.go ν 0 g k (τ + 1) ω
      (Fin.snoc (α := fun _ => X × ℝ) h (alg.query τ ω h, v))) at hmg
    rw [lintegral_add_right _ hmg, lintegral_const_mul _ hmf]

private theorem trajExp_upper (hν : ∀ τ, IsMarkovKernel (ν τ))
    {n : ℕ} {f g : (Fin n → X × ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (a : ℝ≥0∞) :
    alg.trajExp ν P n (fun h => a * f h + g h) ≤
      a * alg.trajExp ν P n f + alg.trajExp ν P n g := by
  let F (τ : ℕ) (h : Fin τ → X × ℝ) :=
    if hτ : τ = n then f (fun i => h (Fin.cast hτ.symm i)) else 0
  let G (τ : ℕ) (h : Fin τ → X × ℝ) :=
    if hτ : τ = n then g (fun i => h (Fin.cast hτ.symm i)) else 0
  have hlift : (fun τ (h : Fin τ → X × ℝ) =>
      if hτ : τ = n then
        a * f (fun i => h (Fin.cast hτ.symm i)) + g (fun i => h (Fin.cast hτ.symm i))
      else 0) = fun τ h => a * F τ h + G τ h := by
    ext τ h
    by_cases ht : τ = n <;> simp [F, G, ht]
  unfold trajExp
  rw [hlift]
  let EF (ω : Ω) := alg.go ν 0 F n 0 ω Fin.elim0
  let EG (ω : Ω) := alg.go ν 0 G n 0 ω Fin.elim0
  calc
    _ ≤ ∫⁻ ω, a * EF ω + EG ω ∂P :=
      lintegral_mono fun ω => alg.go_zero_upper ν n 0 ω Fin.elim0 F G a
        (measurable_terminal hf) (measurable_terminal hg) hν
    _ = _ := by
      change _ = a * (∫⁻ ω, EF ω ∂P) + (∫⁻ ω, EG ω ∂P)
      rw [lintegral_add_right, lintegral_const_mul]
      · exact (alg.measurable_go ν hν (c := 0) measurable_const (measurable_terminal hf) n 0).comp
          (measurable_id.prodMk (measurable_const (a := Fin.elim0)))
      · exact (alg.measurable_go ν hν (c := 0) measurable_const (measurable_terminal hg) n 0).comp
          (measurable_id.prodMk (measurable_const (a := Fin.elim0)))

private theorem go_zero_mono_terminal
    {f g : (τ : ℕ) → (Fin τ → X × ℝ) → ℝ≥0∞} (n k τ : ℕ) (ω : Ω)
    (h : Fin τ → X × ℝ) (ht : k + τ = n) (hfg : ∀ h, f n h ≤ g n h) :
    alg.go ν 0 f k τ ω h ≤ alg.go ν 0 g k τ ω h := by
  induction k generalizing τ with
  | zero =>
    simp only [zero_add] at ht
    subst τ
    exact hfg h
  | succ k ih =>
    simp only [go, Pi.zero_apply, zero_add]
    exact lintegral_mono fun v => ih _ _ (by omega)

private theorem go_cost_sum (hν : ∀ τ, IsMarkovKernel (ν τ)) {c : X → ℝ≥0∞}
    (k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ) :
    alg.go ν 0 (fun τ h => ∑ i : Fin τ, c (h i).1) k τ ω h =
      (∑ i : Fin τ, c (h i).1) + alg.go ν c (fun _ _ => 0) k τ ω h := by
  induction k generalizing τ with
  | zero => simp [go]
  | succ k ih =>
    have := hν τ
    simp only [go, Pi.zero_apply, zero_add, ih, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, add_assoc]

private theorem trajExp_sum_eq_regret (hν : ∀ τ, IsMarkovKernel (ν τ)) {L : X → ℝ}
    (n : ℕ) (K : Set X) :
    alg.trajExp ν P n (fun h => ∑ i, ENNReal.ofReal (L (h i).1 - sInf (L '' K))) =
      alg.regret ν P n L K := by
  let c := fun x => ENNReal.ofReal (L x - sInf (L '' K))
  unfold trajExp regret
  apply lintegral_congr
  intro ω
  have hs := alg.go_cost_sum ν hν (c := c) n 0 ω Fin.elim0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hs
  rw [← hs]
  apply le_antisymm
  all_goals
    apply alg.go_zero_mono_terminal ν n n 0 ω Fin.elim0 (by simp)
    intro h
    simp [c]

end BilateralProfitRegular.BanditAlg
end BundlePart002


section BundlePart003


namespace BilateralProfitRegular.BanditAlg

open MeasureTheory ProbabilityTheory ENNReal Classical
open scoped NNReal

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
variable (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω)

/-- Cumulative deviation of the observations from their conditional means. -/
private noncomputable def runDeviation {m : ℕ} (L : X → ℝ) (h : Fin m → X × ℝ) : ℝ :=
  ∑ i, ((h i).2 - L (h i).1)

private theorem measurable_runDeviation {m : ℕ} {L : X → ℝ} (hL : Measurable L) :
    Measurable (runDeviation (m := m) L) :=
  Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).snd.sub (hL.comp (measurable_pi_apply i).fst)

omit [MeasurableSpace X] in
private theorem runDeviation_snoc (L : X → ℝ) {m : ℕ} (h : Fin m → X × ℝ) (x : X) (v : ℝ) :
    runDeviation L (Fin.snoc (α := fun _ => X × ℝ) h (x, v)) =
      runDeviation L h + (v - L x) := by
  simp only [runDeviation, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

private theorem observation_mgf {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {B m : ℝ} (hB : 0 ≤ B) (hmeas : μ (Set.Icc 0 B)ᶜ = 0) (hm : ∫ y, y ∂μ = m)
    (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (t * (y - m))) ∂μ ≤
      ENNReal.ofReal (Real.exp (B ^ 2 * t ^ 2 / 8)) := by
  have hY : ∀ᵐ y ∂μ, id y ∈ Set.Icc 0 B := (ae_iff.2 hmeas)
  have hs := hasSubgaussianMGF_of_mem_Icc measurable_id.aemeasurable hY
  change HasSubgaussianMGF (fun y : ℝ => y - ∫ y, y ∂μ) _ μ at hs
  rw [hm] at hs
  have hg := hs.mgf_le t
  change (∫ y, Real.exp (t * (y - m)) ∂μ) ≤ _ at hg
  have hpow : (((‖B - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = B ^ 2 * t ^ 2 / 8 := by
    simp [Real.norm_eq_abs, abs_of_nonneg hB]
    ring
  rw [hpow] at hg
  have he := ofReal_le_ofReal hg
  rw [ofReal_integral_eq_lintegral_ofReal (hs.integrable_exp_mul t)
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)] at he
  exact he

private theorem go_mgf_le {L : X → ℝ} (K : Set X) (hK : alg.QueriesIn K)
    (hν : ν.MeanOn L K) {B : ℝ} (hB : 0 ≤ B) (hv : ν.ValuesIn K (Set.Icc 0 B))
    (t : ℝ) (k τ : ℕ) (ω : Ω) (h : Fin τ → X × ℝ) :
    alg.go ν 0 (fun _ h => ENNReal.ofReal (Real.exp (t * runDeviation L h))) k τ ω h ≤
      ENNReal.ofReal (Real.exp (t * runDeviation L h + k * (B ^ 2 * t ^ 2 / 8))) := by
  induction k generalizing τ with
  | zero => simp [go]
  | succ k ih =>
    have := hν.1 τ
    let x := alg.query τ ω h
    have hx := hK τ ω h
    simp only [go, Pi.zero_apply, zero_add]
    refine (lintegral_mono (fun v => ih _ _)).trans ?_
    let a := Real.exp (t * runDeviation L h + k * (B ^ 2 * t ^ 2 / 8))
    have heq (v : ℝ) :
        ENNReal.ofReal (Real.exp (t * runDeviation L (Fin.snoc (α := fun _ => X × ℝ) h (x, v)) +
            k * (B ^ 2 * t ^ 2 / 8))) =
          ENNReal.ofReal a * ENNReal.ofReal (Real.exp (t * (v - L x))) := by
      rw [runDeviation_snoc, ← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    change (∫⁻ v, ENNReal.ofReal (Real.exp (t * runDeviation L
      (Fin.snoc (α := fun _ => X × ℝ) h (x, v)) + k * (B ^ 2 * t ^ 2 / 8))) ∂(ν τ (h, x))) ≤ _
    simp_rw [heq]
    rw [lintegral_const_mul _ (by fun_prop)]
    calc
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal (Real.exp (B ^ 2 * t ^ 2 / 8)) :=
        mul_le_mul_right (observation_mgf hB (hv τ h x hx) (hν.2 τ h x hx).2 t) _
      _ = _ := by
        rw [← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Nat.cast_succ]
        congr 2
        ring

private theorem trajExp_mgf_le {L : X → ℝ} (K : Set X) (hK : alg.QueriesIn K)
    [IsProbabilityMeasure P] (hν : ν.MeanOn L K) {B : ℝ} (hB : 0 ≤ B)
    (hv : ν.ValuesIn K (Set.Icc 0 B)) (t : ℝ) (n : ℕ) :
    alg.trajExp ν P n (fun h => ENNReal.ofReal (Real.exp (t * runDeviation L h))) ≤
      ENNReal.ofReal (Real.exp (n * (B ^ 2 * t ^ 2 / 8))) := by
  unfold trajExp
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal (Real.exp (n * (B ^ 2 * t ^ 2 / 8))))
    fun ω => ?_).trans_eq (by simp)
  refine (alg.go_zero_mono_terminal ν n n 0 ω Fin.elim0 (by simp)
    (g := fun _ h => ENNReal.ofReal (Real.exp (t * runDeviation L h))) (by simp)).trans ?_
  simpa [runDeviation] using alg.go_mgf_le ν K hK hν hB hv t n 0 ω Fin.elim0

private theorem trajExp_one_sided {L : X → ℝ} (hL : Measurable L)
    (K : Set X) (hK : alg.QueriesIn K) [IsProbabilityMeasure P]
    (hν : ν.MeanOn L K) {B : ℝ} (hB : 0 ≤ B)
    (hv : ν.ValuesIn K (Set.Icc 0 B)) (n : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (a : ℝ) {s : ℝ} (hs : s ^ 2 = 1) :
    alg.trajExp ν P n (fun h => if a < s * runDeviation L h then 1 else 0) ≤
      ENNReal.ofReal (Real.exp (-u * a + n * (B ^ 2 * u ^ 2 / 8))) := by
  let b := ENNReal.ofReal (Real.exp (-u * a))
  let f := fun h : Fin n → X × ℝ =>
    ENNReal.ofReal (Real.exp ((u * s) * runDeviation L h))
  have hf : Measurable f := ((measurable_runDeviation hL).const_mul _).exp.ennreal_ofReal
  calc
    _ ≤ alg.trajExp ν P n (fun h => b * f h + 0) := by
      apply alg.trajExp_mono_on ν P K hK
      intro h _
      by_cases h' : a < s * runDeviation L h
      · simp only [if_pos h', add_zero]
        dsimp [b, f]
        rw [← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ofReal_one]
        apply ofReal_le_ofReal
        rw [← Real.exp_zero, Real.exp_le_exp]
        nlinarith [mul_nonneg hu (sub_nonneg.mpr h'.le)]
      · simp [h']
    _ ≤ b * alg.trajExp ν P n f + alg.trajExp ν P n (fun _ => 0) :=
      alg.trajExp_upper ν P hν.1 hf measurable_const b
    _ ≤ _ := by
      rw [alg.trajExp_const ν P hν.1 n 0, add_zero]
      calc
        _ ≤ b * ENNReal.ofReal (Real.exp (n * (B ^ 2 * (u * s) ^ 2 / 8))) :=
          mul_le_mul_right (alg.trajExp_mgf_le ν P K hK hν hB hv (u * s) n) _
        _ = _ := by
          dsimp [b]
          rw [← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_pow, hs, mul_one]

private theorem trajExp_abs_dev_le {L : X → ℝ} (hL : Measurable L)
    (K : Set X) (hK : alg.QueriesIn K) [IsProbabilityMeasure P]
    (hν : ν.MeanOn L K) {B : ℝ} (hB : 0 < B)
    (hv : ν.ValuesIn K (Set.Icc 0 B)) (n : ℕ)
    {d : ℝ} (hd : 0 ≤ d) :
    alg.trajExp ν P n (fun h => if n * d < |runDeviation L h| then 1 else 0) ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * n * d ^ 2 / B ^ 2))) := by
  let u := 4 * d / B ^ 2
  let a := n * d
  let f (h : Fin n → X × ℝ) : ℝ≥0∞ := if a < 1 * runDeviation L h then 1 else 0
  let g (h : Fin n → X × ℝ) : ℝ≥0∞ := if a < (-1) * runDeviation L h then 1 else 0
  have hu : 0 ≤ u := by positivity
  have hf : Measurable f :=
    measurable_const.piecewise (measurableSet_lt measurable_const ((measurable_runDeviation hL).const_mul _))
      measurable_const
  have hg : Measurable g :=
    measurable_const.piecewise (measurableSet_lt measurable_const ((measurable_runDeviation hL).const_mul _))
      measurable_const
  have hsum : -u * a + n * (B ^ 2 * u ^ 2 / 8) = -(2 * n * d ^ 2 / B ^ 2) := by
    dsimp [u, a]
    field_simp
    ring
  have hpos := alg.trajExp_one_sided ν P hL K hK hν hB.le hv n hu a (s := 1) (by norm_num)
  have hneg := alg.trajExp_one_sided ν P hL K hK hν hB.le hv n hu a (s := -1) (by norm_num)
  calc
    _ ≤ alg.trajExp ν P n (fun h => 1 * f h + g h) := by
      apply alg.trajExp_mono_on ν P K hK
      intro h _
      by_cases hd' : a < |runDeviation L h|
      · rw [if_pos hd', one_mul]
        rcases (lt_abs.mp hd') with hp | hm
        · exact (le_add_of_nonneg_right (show 0 ≤ g h from bot_le)).trans' (by simp [f, hp])
        · exact (le_add_of_nonneg_left (show 0 ≤ f h from bot_le)).trans' (by simp [g, hm])
      · simp [a, hd']
    _ ≤ 1 * alg.trajExp ν P n f + alg.trajExp ν P n g :=
      alg.trajExp_upper ν P hν.1 hf hg 1
    _ ≤ _ := by
      rw [one_mul, two_mul, ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      rw [hsum] at hpos hneg
      exact add_le_add hpos hneg

end BilateralProfitRegular.BanditAlg
end BundlePart003


section BundlePart004


namespace BilateralProfitRegular.BanditAlg

open MeasureTheory ProbabilityTheory ENNReal Classical

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
variable (alg : BanditAlg X Ω) (ν : ObsEnv X) (P : Measure Ω)

private theorem multiExp_mono_on (K : Set X) (hK : alg.QueriesIn K) (n M : ℕ)
    {f g : (Fin M → Fin n → X × ℝ) → ℝ≥0∞}
    (hfg : ∀ hs, (∀ m i, (hs m i).1 ∈ K) → f hs ≤ g hs) :
    alg.multiExp ν P n M f ≤ alg.multiExp ν P n M g := by
  induction M with
  | zero =>
    exact hfg _ (fun i => i.elim0)
  | succ M ih =>
    simp only [multiExp]
    apply alg.trajExp_mono_on ν P K hK
    intro t ht
    apply ih
    intro hs hh
    apply hfg
    intro m
    refine Fin.cases ?_ (fun j => ?_) m
    · simpa only [Fin.cons_zero] using ht
    · simpa only [Fin.cons_succ] using hh j

private theorem multiExp_prod_add_sum_le (hν : ∀ τ, IsMarkovKernel (ν τ)) [IsProbabilityMeasure P]
    {n : ℕ} (M : ℕ) {f g : (Fin n → X × ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {p q : ℝ≥0∞}
    (hp : alg.trajExp ν P n f ≤ p) (hq : alg.trajExp ν P n g ≤ q) (a b : ℝ≥0∞) :
    alg.multiExp ν P n M (fun hs => a * (∏ m, f (hs m)) + (b + ∑ m, g (hs m))) ≤
      a * p ^ M + (b + M * q) := by
  induction M generalizing a b with
  | zero => simp [multiExp]
  | succ M ih =>
    let c := p ^ M
    let d := b + M * q
    let F (h : Fin n → X × ℝ) := f h
    let G (h : Fin n → X × ℝ) := g h + d
    have hG : Measurable G := hg.add_const _
    have hreorder (t : Fin n → X × ℝ) (ts : Fin M → Fin n → X × ℝ) :
        a * (∏ m, f (Fin.cons (α := fun _ => Fin n → X × ℝ) t ts m)) + (b + ∑ m, g (Fin.cons (α := fun _ => Fin n → X × ℝ) t ts m)) =
        (a * f t) * (∏ m, f (ts m)) + ((b + g t) + ∑ m, g (ts m)) := by
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ac_rfl
    calc
      _ ≤ alg.trajExp ν P n (fun t => (a * c) * F t + G t) := by
        simp only [multiExp, hreorder]
        apply alg.trajExp_mono_on ν P Set.univ (fun _ _ _ => Set.mem_univ _)
        intro t _
        refine (ih (a * f t) (b + g t)).trans_eq ?_
        dsimp [c, d, F, G]
        ac_rfl
      _ ≤ (a * c) * alg.trajExp ν P n F + alg.trajExp ν P n G :=
        alg.trajExp_upper ν P hν hf hG _
      _ ≤ (a * c) * p + (q + d) := by
        have hgd : alg.trajExp ν P n G ≤ q + d := by
          change alg.trajExp ν P n (fun t => g t + d) ≤ q + d
          have h := alg.trajExp_upper ν P hν hg
            (measurable_const (a := d) : Measurable (fun _ : Fin n → X × ℝ => d)) 1
          simp only [one_mul, alg.trajExp_const ν P hν] at h
          exact h.trans (add_le_add_left hq d)
        exact add_le_add (mul_le_mul_right hp _) hgd
      _ = _ := by
        dsimp [c, d]
        rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
        ac_rfl

private theorem trajExp_bad_loss_le (hν : ∀ τ, IsMarkovKernel (ν τ))
    [IsProbabilityMeasure P] (K : Set X) (hK : alg.QueriesIn K) {L : X → ℝ} (hL : Measurable L)
    (hbelow : BddBelow (L '' K)) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    alg.trajExp ν P n
        (fun h => if a < ∑ i, (L (h i).1 - sInf (L '' K)) then 1 else 0) ≤
      ENNReal.ofReal (a⁻¹) * alg.regret ν P n L K := by
  let c (h : Fin n → X × ℝ) := ∑ i, ENNReal.ofReal (L (h i).1 - sInf (L '' K))
  have hc : Measurable c := Finset.measurable_sum _ fun i _ =>
    ((hL.comp (measurable_pi_apply i).fst).sub_const _).ennreal_ofReal
  calc
    _ ≤ alg.trajExp ν P n (fun h => ENNReal.ofReal (a⁻¹) * c h + 0) := by
      apply alg.trajExp_mono_on ν P K hK
      intro h hh
      split
      · rename_i hbig
        have hn (i : Fin n) : 0 ≤ L (h i).1 - sInf (L '' K) :=
          sub_nonneg.mpr (csInf_le hbelow ⟨_, hh i, rfl⟩)
        dsimp [c]
        rw [add_zero, ← ofReal_sum_of_nonneg (fun i _ => hn i),
          ← ofReal_mul (inv_nonneg.mpr ha.le), ← ofReal_one]
        apply ofReal_le_ofReal
        rw [← div_eq_inv_mul, le_div_iff₀ ha, one_mul]
        exact hbig.le
      · exact bot_le
    _ ≤ ENNReal.ofReal (a⁻¹) * alg.trajExp ν P n c + alg.trajExp ν P n (fun _ => 0) :=
      alg.trajExp_upper ν P hν hc measurable_const _
    _ = _ := by
      rw [alg.trajExp_const ν P hν n 0, add_zero]
      exact congrArg _ (alg.trajExp_sum_eq_regret ν P hν n K)

end BilateralProfitRegular.BanditAlg
end BundlePart004


section BundlePart005


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- The average of the conditional losses at the queries of a completed run. -/
private noncomputable def avgLoss {X : Type} {n : ℕ} (L : X → ℝ) (h : Fin n → X × ℝ) : ℝ :=
  (∑ i, L (h i).1) / n

private theorem avgQuery_mem_and_jensen {n : ℕ} (hn : 0 < n) {K : Set (ℝ × ℝ)}
    {L : (ℝ × ℝ) → ℝ} (hL : ConvexOn ℝ K L)
    (h : Fin n → (ℝ × ℝ) × ℝ) (hh : ∀ i, (h i).1 ∈ K) :
    avgQuery h ∈ K ∧ L (avgQuery h) ≤ avgLoss L h := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw (i : Fin n) (_ : i ∈ Finset.univ) : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
  have hw1 : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp [hnR.ne']
  have hx : (∑ i, (n : ℝ)⁻¹ • (h i).1) = avgQuery h := by
    rw [avgQuery, Finset.smul_sum]
  have hmem := hL.1.sum_mem (t := Finset.univ) (z := fun i : Fin n => (h i).1)
    hw hw1 (fun i _ => hh i)
  have hJensen := hL.map_sum_le (t := Finset.univ) (p := fun i : Fin n => (h i).1)
    hw hw1 (fun i _ => hh i)
  rw [hx] at hmem hJensen
  refine ⟨hmem, ?_⟩
  rw [avgLoss, div_eq_mul_inv, mul_comm, Finset.mul_sum]
  simpa only [smul_eq_mul] using hJensen

private theorem clipped_inverse_approx {a b δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (ha : 1 / (10 * δ) ≤ a) (hb : 1 / (10 * δ) ≤ b) (hab : b ≤ a + d) :
    1 / a - 1 / b ≤ (100 * δ ^ 2) * d := by
  let c := 1 / (10 * δ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hapos : 0 < a := hc.trans_le ha
  have hbpos : 0 < b := hc.trans_le hb
  have hprod : c * c ≤ a * b :=
    mul_le_mul ha hb hc.le hapos.le
  have hnorm : (100 * δ ^ 2) * (c * c) = 1 := by
    dsimp [c]
    field_simp
    ring
  have hprod' : d ≤ (100 * δ ^ 2) * d * (a * b) := by
    calc
      d = ((100 * δ ^ 2) * (c * c)) * d := by rw [hnorm, one_mul]
      _ ≤ ((100 * δ ^ 2) * (a * b)) * d := by gcongr
      _ = _ := by ring
  calc
    1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    _ ≤ (100 * δ ^ 2) * d :=
      (div_le_iff₀ (mul_pos hapos hbpos)).2 (by linarith)

private theorem refineGood_of_avg_bounds {E : Environment} {lam δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) {K : Set (ℝ × ℝ)}
    (hL : ConvexOn ℝ K (fun x => 1 / auxProfit E lam x))
    (hR : ∀ x ∈ K, 0 < auxProfit E lam x ∧ auxProfit E lam x ≤ 10 * δ)
    {M n : ℕ} (hn : 0 < n) (hs : Fin M → Fin n → (ℝ × ℝ) × ℝ)
    (hquery : ∀ m i, (hs m i).1 ∈ K)
    (horacle : ∀ m,
      |avgObs (hs m) - avgLoss (fun x => 1 / auxProfit E lam x) (hs m)| ≤ ε / (400 * δ ^ 2))
    (hexists : ∃ m, avgLoss (fun x => 1 / auxProfit E lam x) (hs m) ≤
      sInf ((fun x => 1 / auxProfit E lam x) '' K) + ε / (200 * δ ^ 2)) :
    RefineGood E lam δ ε K hs := by
  let L := fun x => 1 / auxProfit E lam x
  let d := ε / (400 * δ ^ 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hd2 : ε / (200 * δ ^ 2) = 2 * d := by dsimp [d]; ring
  have hclamp (x : ℝ × ℝ) (hx : x ∈ K) : 1 / (10 * δ) ≤ L x :=
    one_div_le_one_div_of_le (hR x hx).1 (hR x hx).2
  have hbelow : BddBelow (L '' K) := ⟨1 / (10 * δ), by
    rintro _ ⟨x, hx, rfl⟩
    exact hclamp x hx⟩
  have herr : 100 * δ ^ 2 * d = ε / 4 := by
    dsimp [d]
    field_simp
    ring
  intro m hm
  obtain ⟨hmK, hmJ⟩ := avgQuery_mem_and_jensen hn hL (hs m) (hquery m)
  obtain ⟨g, hg⟩ := hexists
  have hgm : avgObs (hs m) ≤ sInf (L '' K) + 3 * d := by
    have h₁ : avgObs (hs m) ≤ avgObs (hs g) := hm g
    have h₂ : avgObs (hs g) - avgLoss L (hs g) ≤ d := (abs_le.mp (horacle g)).2
    linarith
  have hmin (x : ℝ × ℝ) (hx : x ∈ K) : sInf (L '' K) ≤ L x :=
    csInf_le hbelow ⟨x, hx, rfl⟩
  let a := max (avgObs (hs m)) (1 / (10 * δ))
  have ha : 1 / (10 * δ) ≤ a := le_max_right _ _
  refine ⟨hmK, ?_, ?_⟩
  · intro x hx
    have hax : a ≤ L x + 3 * d := max_le
      (hgm.trans (add_le_add_left (hmin x hx) _)) (by linarith [hclamp x hx])
    have hrecip := clipped_inverse_approx hδ (by positivity : 0 ≤ 3 * d)
      (hclamp x hx) ha hax
    change 1 / L x - 1 / a ≤ _ at hrecip
    have hR' : 1 / L x = auxProfit E lam x := by simp [L]
    rw [hR'] at hrecip
    change auxProfit E lam x - ε ≤ 1 / a
    linarith [show (100 * δ ^ 2) * (3 * d) = 3 * (ε / 4) by rw [← herr]; ring]
  · have hobs : -(d) ≤ avgObs (hs m) - avgLoss L (hs m) := (abs_le.mp (horacle m)).1
    have hbase : avgObs (hs m) ≤ a := le_max_left _ _
    have hy : L (avgQuery (hs m)) ≤ a + d := by linarith
    have hrecip := clipped_inverse_approx hδ hd ha (hclamp _ hmK) hy
    change 1 / a - 1 / L (avgQuery (hs m)) ≤ _ at hrecip
    have hR' : 1 / L (avgQuery (hs m)) = auxProfit E lam (avgQuery (hs m)) := by simp [L]
    rw [hR', herr] at hrecip
    change 1 / a ≤ auxProfit E lam (avgQuery (hs m)) + ε
    linarith

end BilateralProfitRegular
end BundlePart005


section BundlePart006




namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory ENNReal MechanismDesign.BilateralTrade Classical

variable {Ω : Type} [MeasurableSpace Ω]

private theorem refine_failure_le {E : Environment} {lam δ ε B : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 < B) {K : Set (ℝ × ℝ)}
    (hconv : ConvexOn ℝ K (fun x => 1 / auxProfit E lam x))
    (hbounds : ∀ x ∈ K, 0 < auxProfit E lam x ∧ auxProfit E lam x ≤ 10 * δ)
    (hL : Measurable (fun x : ℝ × ℝ => 1 / auxProfit E lam x))
    (alg : BanditAlg (ℝ × ℝ) Ω) (Pω : Measure Ω) [IsProbabilityMeasure Pω]
    (ν : ObsEnv (ℝ × ℝ)) (hK : alg.QueriesIn K)
    (hν : ν.MeanOn (fun x => 1 / auxProfit E lam x) K)
    (hv : ν.ValuesIn K (Set.Icc 0 B)) {n : ℕ} (hn : 0 < n) (M : ℕ)
    (hreg : alg.regret ν Pω n (fun x => 1 / auxProfit E lam x) K ≤
      ENNReal.ofReal ((n : ℝ) * ε / (800 * δ ^ 2))) :
    alg.multiExp ν Pω n M (fun hs => if RefineGood E lam δ ε K hs then 0 else 1) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ M +
        (M : ℝ) * (2 * Real.exp (-(2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / B ^ 2)))) := by
  let L := fun x => 1 / auxProfit E lam x
  let l := sInf (L '' K)
  let d := ε / (400 * δ ^ 2)
  let a := (n : ℝ) * ε / (200 * δ ^ 2)
  let p := ENNReal.ofReal (1 / 4)
  let q := ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * d ^ 2 / B ^ 2)))
  let S (h : Fin n → (ℝ × ℝ) × ℝ) := ∑ i, (L (h i).1 - l)
  let D (h : Fin n → (ℝ × ℝ) × ℝ) := BanditAlg.runDeviation L h
  let f (h : Fin n → (ℝ × ℝ) × ℝ) : ℝ≥0∞ := if a < S h then 1 else 0
  let g (h : Fin n → (ℝ × ℝ) × ℝ) : ℝ≥0∞ := if (n : ℝ) * d < |D h| then 1 else 0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hbelow : BddBelow (L '' K) := ⟨0, by
    rintro _ ⟨x, hx, rfl⟩
    exact (one_div_pos.mpr (hbounds x hx).1).le⟩
  have hS : Measurable S := Finset.measurable_sum _ fun i _ =>
    (hL.comp (measurable_pi_apply i).fst).sub_const _
  have hD : Measurable D := Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).snd.sub (hL.comp (measurable_pi_apply i).fst)
  have hf : Measurable f :=
    measurable_const.piecewise (measurableSet_lt measurable_const hS) measurable_const
  have hg : Measurable g :=
    measurable_const.piecewise (measurableSet_lt measurable_const hD.abs) measurable_const
  have hp : alg.trajExp ν Pω n f ≤ p := by
    calc
      _ ≤ ENNReal.ofReal (a⁻¹) * alg.regret ν Pω n L K :=
        alg.trajExp_bad_loss_le ν Pω hν.1 K hK hL hbelow n ha
      _ ≤ ENNReal.ofReal (a⁻¹) * ENNReal.ofReal ((n : ℝ) * ε / (800 * δ ^ 2)) :=
        mul_le_mul_right hreg _
      _ = p := by
        rw [← ofReal_mul (inv_nonneg.mpr ha.le)]
        congr 1
        dsimp [a]
        field_simp
        ring
  have hq : alg.trajExp ν Pω n g ≤ q :=
    alg.trajExp_abs_dev_le ν Pω hL K hK hν hB hv n hd
  have hloss (h : Fin n → (ℝ × ℝ) × ℝ) (hh : S h ≤ a) :
      avgLoss L h ≤ l + ε / (200 * δ ^ 2) := by
    simp only [S, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hh
    apply (div_le_iff₀ hnR).2
    dsimp [a] at hh
    exact (sub_le_iff_le_add.1 hh).trans_eq (by ring)
  have hobs (h : Fin n → (ℝ × ℝ) × ℝ) (hh : |D h| ≤ (n : ℝ) * d) :
      |avgObs h - avgLoss L h| ≤ d := by
    unfold avgObs avgLoss
    rw [← sub_div, abs_div, abs_of_nonneg hnR.le]
    apply (div_le_iff₀ hnR).2
    simpa only [D, BanditAlg.runDeviation, Finset.sum_sub_distrib, mul_comm] using hh
  calc
    _ ≤ alg.multiExp ν Pω n M (fun hs => 1 * (∏ m, f (hs m)) + (0 + ∑ m, g (hs m))) := by
      apply alg.multiExp_mono_on ν Pω K hK n M
      intro hs hqueries
      rw [one_mul, zero_add]
      by_cases hsuccess : RefineGood E lam δ ε K hs
      · simp [hsuccess]
      rw [if_neg hsuccess]
      by_cases hall : ∀ m, a < S (hs m)
      · have hprod : (∏ m, f (hs m)) = 1 := Finset.prod_eq_one fun m _ => by simp [f, hall m]
        simp [hprod]
      push Not at hall
      by_cases herr : ∃ m, (n : ℝ) * d < |D (hs m)|
      · obtain ⟨m, hm⟩ := herr
        have hsingle : g (hs m) = 1 := by simp [g, hm]
        have hsum : g (hs m) ≤ ∑ i, g (hs i) :=
          Finset.single_le_sum (f := fun i => g (hs i)) (fun _ _ => bot_le) (Finset.mem_univ m)
        exact (hsingle ▸ hsum).trans (le_add_of_nonneg_left bot_le)
      push Not at herr
      obtain ⟨m, hm⟩ := hall
      exact False.elim (hsuccess (refineGood_of_avg_bounds hδ hε.le hconv hbounds hn hs hqueries
        (fun j => hobs (hs j) (herr j)) ⟨m, hloss (hs m) hm⟩))
    _ ≤ 1 * p ^ M + (0 + M * q) :=
      alg.multiExp_prod_add_sum_le ν Pω hν.1 M hf hg hp hq 1 0
    _ = _ := by
      simp only [p, q, one_mul, zero_add]
      rw [← ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4),
        ← ofReal_natCast, ← ofReal_mul (by positivity : (0 : ℝ) ≤ M),
        ← ofReal_add (by positivity) (by positivity)]

end BilateralProfitRegular
end BundlePart006


section BundlePart007


namespace BilateralProfitRegular

private theorem scale_factor (j : ℕ) :
    (4 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
  norm_num

private theorem double_scale_factor (j : ℕ) :
    (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num

private theorem log_eight (T : ℕ) (hT : 0 < T) :
    Real.log (8 * (T : ℝ)) =
      Real.log (2 * (T : ℝ)) + 2 * Real.log 2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [show 8 * (T : ℝ) = 2 ^ 2 * (2 * T) by ring,
    Real.log_mul (by norm_num) (by positivity : (2 * (T : ℝ)) ≠ 0), Real.log_pow]
  norm_num
  ring

set_option maxHeartbeats 1200000 in
/-- One choice of the run-size constant simultaneously supports both probability
budgets and the normalized expected regret at every admissible phase. -/
private theorem refine_phase_budgets (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (T j : ℕ), 0 < T →
      (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) → ∀ δ : ℝ, 0 < δ →
      let n := phaseLen C₀ T j
      let M := numCopies C₀ T
      let ε := acc δ j
      0 < n ∧ 0 < ε ∧
      C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤ (n : ℝ) * ε / (800 * δ ^ 2) ∧
      (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) ∧
      (M : ℝ) * (2 * Real.exp (-(2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2))) ≤
        1 / (2 * (T : ℝ)) := by
  obtain ⟨D, hDbig, hD₁, hD₂⟩ : ∃ D : ℝ, 1000000 ≤ D ∧ C₁ ≤ D ∧ C₂ ≤ D := by
    refine ⟨1000000 * (1 + C₁ + C₂), ?_, ?_, ?_⟩ <;> linarith only [hC₁, hC₂]
  have hD : 0 < D := by linarith only [hDbig]
  have hD1 : 1 ≤ D := by linarith only [hDbig]
  refine ⟨D ^ 8, by positivity, ?_⟩
  intro T j hT hj δ hδ
  dsimp only
  let n := phaseLen (D ^ 8) T j
  let M := numCopies (D ^ 8) T
  let ε := acc δ j
  let L := Real.log (2 * (T : ℝ))
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT' : (0 : ℝ) < T := by positivity
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith only [hT1])
  have hL : 1 / 2 ≤ L := by linarith only [Real.log_two_gt_d9, hlog2]
  have hL' : 0 < L := by linarith only [hL]
  have hlogLT : Real.log (T : ℝ) ≤ L := Real.log_le_log hT' (by linarith only [hT'])
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have hlog8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have hfloor : (4 : ℝ) ^ j * D ^ 8 * L ^ 4 ≤ n := by
    change _ ≤ (↑(4 ^ j * ⌈D ^ 8 * L ^ 4⌉₊) : ℝ)
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hfloor
  have hn : 0 < n := by exact_mod_cast hn'
  have hε : 0 < ε := by dsimp [ε, acc]; positivity
  have hsqrt : (2 : ℝ) ^ j * D ^ 4 * L ^ 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    convert hfloor using 1
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    ring
  have hCLR : (1 : ℝ) ≤ D ^ 8 * L ^ 4 := by
    have hg : (2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 4 ≤ D ^ 8 * L ^ 4 := by gcongr <;> linarith only [hDbig, hL, hD, hD1]
    norm_num at hg
    linarith only [hg]
  have hCMR : (1 : ℝ) ≤ D ^ 8 * L := by
    have hg : (2 : ℝ) ^ 8 * (1 / 2 : ℝ) ≤ D ^ 8 * L := by gcongr <;> linarith only [hDbig, hL, hD, hD1]
    norm_num at hg
    linarith only [hg]
  have hlogn : Real.log (2 * (n : ℝ)) ≤ 24 * D * L := by
    by_cases hj0 : j = 0
    · subst j
      have hn0 : (n : ℝ) ≤ 2 * (D ^ 8 * L ^ 4) := by
        change (↑(4 ^ (0 : ℕ) * ⌈D ^ 8 * L ^ 4⌉₊) : ℝ) ≤ _
        simp only [pow_zero, one_mul]
        linarith only [hCLR, Nat.ceil_lt_add_one (show 0 ≤ D ^ 8 * L ^ 4 by positivity)]
      calc
        _ ≤ Real.log (4 * (D ^ 8 * L ^ 4)) := Real.log_le_log (by positivity) (by linarith only [hn0])
        _ = Real.log 4 + 8 * Real.log D + 4 * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow]
          push_cast
          ring
        _ ≤ 10 * D + 4 * L := by
          linarith only [hlog4, hD1, Real.log_le_sub_one_of_pos hD, Real.log_le_sub_one_of_pos hL']
        _ ≤ _ := by
          have hab : 10 * D ≤ 20 * D * L := by nlinarith only [mul_nonneg hD.le (sub_nonneg.mpr hL)]
          have hbc : 4 * L ≤ 4 * D * L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
          linarith only [hab, hbc]
    · have hj := hj.resolve_left hj0
      have hnj : n ≤ 4 * T := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        change 4 ^ (k + 1) * ⌈D ^ 8 * L ^ 4⌉₊ ≤ 4 * T
        have hprev : 4 ^ k * ⌈D ^ 8 * L ^ 4⌉₊ ≤ T := by simpa [phaseLen, L] using hj
        rw [pow_succ, mul_right_comm, mul_comm _ (4 : ℕ)]
        exact Nat.mul_le_mul_left _ hprev
      have hnj' : (n : ℝ) ≤ 4 * (T : ℝ) := by exact_mod_cast hnj
      calc
        _ ≤ Real.log (8 * (T : ℝ)) := Real.log_le_log (by positivity) (by linarith only [hnj'])
        _ = L + 2 * Real.log 2 := log_eight T hT
        _ ≤ 3 * L := by linarith only [hlog2]
        _ ≤ _ := by nlinarith only [hL', mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
  have hlogn_pos : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [h1]
  have hscaled_sqrt : δ * D ^ 4 * L ^ 2 ≤ ε * Real.sqrt n := by
    calc
      _ = ε * ((2 : ℝ) ^ j * D ^ 4 * L ^ 2) := by
        have hscale := double_scale_factor j
        change _ = (δ * (1 / 2) ^ j) * _
        calc
          _ = δ * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) * D ^ 4 * L ^ 2 := by rw [hscale, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hε.le
  have hnorm : 800 * C₂ * (24 * D * L) ^ 2 ≤ D ^ 4 * L ^ 2 := by
    have h1 : 460800 * C₂ ≤ D ^ 2 := by
      calc
        _ ≤ D * D := mul_le_mul (by linarith only [hDbig]) hD₂ hC₂.le hD.le
        _ = _ := by ring
    calc
      _ = ((460800 : ℝ) * C₂) * (D ^ 2 * L ^ 2) := by ring
      _ ≤ D ^ 2 * (D ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hreg : C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤
      (n : ℝ) * ε / (800 * δ ^ 2) := by
    have h₁ : 800 * C₂ * Real.log (2 * (n : ℝ)) ^ 2 ≤ D ^ 4 * L ^ 2 := by
      refine le_trans ?_ hnorm
      gcongr
    have h₂ : δ * (800 * C₂ * Real.log (2 * (n : ℝ)) ^ 2) ≤ ε * Real.sqrt n :=
      (mul_le_mul_of_nonneg_left h₁ hδ.le).trans (by simpa only [mul_assoc] using hscaled_sqrt)
    have h₃ := mul_le_mul_of_nonneg_right h₂ (Real.sqrt_nonneg (n : ℝ))
    rw [mul_assoc ε, ← pow_two, Real.sq_sqrt hn'.le] at h₃
    apply (le_div_iff₀ (by positivity : 0 < 800 * δ ^ 2)).2
    convert h₃ using 1
    · field_simp
    · ring
  have hMlo : D ^ 8 * L ≤ M := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * (D ^ 8 * L) := by
    change (↑⌈D ^ 8 * L⌉₊ : ℝ) ≤ _
    linarith only [hCMR, Nat.ceil_lt_add_one (show 0 ≤ D ^ 8 * L by positivity)]
  have hfail : (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) := by
    have hL_M : L ≤ M := le_trans (le_mul_of_one_le_left hL'.le (one_le_pow₀ hD1)) hMlo
    have hlog4' : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith only [Real.log_two_gt_d9]
    have hM' : (0 : ℝ) ≤ M := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlog4' hM'
    have hx : -(M : ℝ) * Real.log 4 ≤ -L := by linarith only [hprod, hL_M]
    have he := Real.exp_le_exp.mpr hx
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4),
      Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 * (T : ℝ))] at he
    simpa only [one_div, inv_pow] using he
  refine ⟨hn, hε, hreg, hfail, ?_⟩
  let a := (2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2)
  have ha : D ^ 8 * L ^ 4 / (80000 * C₁ ^ 2) ≤ a := by
    calc
      _ = ((4 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j) ^ 2) *
          (D ^ 8 * L ^ 4 / (80000 * C₁ ^ 2)) := by rw [scale_factor, one_mul]
      _ = (2 * ((4 : ℝ) ^ j * D ^ 8 * L ^ 4) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2) := by
        change _ = 2 * _ * (δ * (1 / 2) ^ j / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2
        field_simp
        ring
      _ ≤ a := by
        dsimp [a]
        gcongr
  have hA_L : 24 * D * L ≤ a := by
    have h8 : 15360000 * C₁ ^ 2 * D ≤ D ^ 8 := by
      have h₇ : 15360000 * C₁ ^ 2 ≤ D ^ 7 := by
        calc
          _ ≤ 15360000 * D ^ 2 := by gcongr
          _ ≤ D ^ 5 * D ^ 2 := by
            gcongr
            calc
              (15360000 : ℝ) ≤ (1000000 : ℝ) ^ 5 := by norm_num
              _ ≤ D ^ 5 := by gcongr
          _ = _ := by ring
      calc
        _ ≤ D ^ 7 * D := mul_le_mul_of_nonneg_right h₇ hD.le
        _ = _ := by ring
    have hL3 : (1 / 8 : ℝ) ≤ L ^ 3 := by
      calc
        _ = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have h4 : L / 8 ≤ L ^ 4 := by nlinarith only [mul_le_mul_of_nonneg_right hL3 hL'.le]
    refine le_trans ?_ ha
    apply (le_div_iff₀ (by positivity : 0 < 80000 * C₁ ^ 2)).2
    calc
      _ = (15360000 * C₁ ^ 2 * D) * (L / 8) := by ring
      _ ≤ D ^ 8 * L ^ 4 := by gcongr
  have hlog : Real.log (8 * (D ^ 8 * L) * (T : ℝ)) ≤ 24 * D * L := by
    calc
      _ = Real.log 8 + 8 * Real.log D + Real.log L + Real.log (T : ℝ) := by
        rw [Real.log_mul (by positivity) hT'.ne', Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by positivity) hL'.ne', Real.log_pow]
        push_cast
        ring
      _ ≤ 11 * D + 2 * L := by
        linarith only [hlog8, hD1, Real.log_le_sub_one_of_pos hD, Real.log_le_sub_one_of_pos hL', hlogLT]
      _ ≤ _ := by
        have hab : 11 * D ≤ 22 * D * L := by nlinarith only [mul_nonneg hD.le (sub_nonneg.mpr hL)]
        have hbc : 2 * L ≤ 2 * D * L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
        linarith only [hab, hbc]
  have he : 8 * (D ^ 8 * L) * (T : ℝ) ≤ Real.exp a := by
    rw [← Real.exp_log (show 0 < 8 * (D ^ 8 * L) * (T : ℝ) by positivity), Real.exp_le_exp]
    exact hlog.trans hA_L
  change (M : ℝ) * (2 * Real.exp (-a)) ≤ 1 / (2 * (T : ℝ))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (T : ℝ))).2
  rw [Real.exp_neg]
  calc
    _ ≤ (2 * (D ^ 8 * L)) * (2 * (Real.exp a)⁻¹) * (2 * (T : ℝ)) := by gcongr
    _ = (8 * (D ^ 8 * L) * (T : ℝ)) / Real.exp a := by ring
    _ ≤ 1 := by simpa only [div_le_one (Real.exp_pos _)] using he

end BilateralProfitRegular
end BundlePart007


section BundlePart008









namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade Classical

private theorem measurable_cdf_like {f : ℝ → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun b => ∫ z in a..b, f z) := by
  let U : Set (ℝ × ℝ) := {p | a < p.2 ∧ p.2 ≤ p.1}
  let V : Set (ℝ × ℝ) := {p | p.1 < p.2 ∧ p.2 ≤ a}
  have hU : MeasurableSet U :=
    (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst)
  have hV : MeasurableSet V :=
    (measurableSet_lt measurable_fst measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
  have hu := (((hf.comp measurable_snd).indicator hU).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
  have hv := (((hf.comp measurable_snd).indicator hV).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
  have hu_eq (b : ℝ) : (∫ z, U.indicator (f ∘ Prod.snd) (b, z)) = ∫ z in Set.Ioc a b, f z := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hv_eq (b : ℝ) : (∫ z, V.indicator (f ∘ Prod.snd) (b, z)) = ∫ z in Set.Ioc b a, f z := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hu' : Measurable (fun b => ∫ z in Set.Ioc a b, f z) := by simpa only [hu_eq] using hu
  have hv' : Measurable (fun b => ∫ z in Set.Ioc b a, f z) := by simpa only [hv_eq] using hv
  exact hu'.sub hv' 

private theorem measurable_auxProfit_reciprocal (E : Environment) (lam : ℝ) :
    Measurable (fun x : ℝ × ℝ => 1 / auxProfit E lam x) := by
  have hs : Measurable E.cdfS := measurable_cdf_like E.fS_measurable E.loS
  have hb : Measurable E.cdfB := measurable_cdf_like E.fB_measurable E.loB
  unfold auxProfit
  apply measurable_const.div
  exact ((measurable_snd.sub measurable_fst).const_mul _).div
    ((((hs.comp measurable_fst).const_div _).add
      ((measurable_const.sub (hb.comp measurable_snd)).const_div _)).pow_const _)

private theorem refinement :
    (∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (c : Candidate), η < δ → δ ≤ muStar E → muStar E < 6 * δ → c.Valid E δ →
      ∀ lam : ℝ, 0 < lam → |Real.log (lam / c.param E)| ≤ 1 / 1000 * Real.sqrt (η / δ) →
      ∀ j : ℕ, (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω), IsProbabilityMeasure Pω →
      ∀ alg : BanditAlg (ℝ × ℝ) Ω, alg.QueriesIn c.region →
        (∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
          ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
          alg.regret ν Pω (phaseLen C₀ T j) (fun x => 1 / auxProfit E lam x) c.region ≤
            ENNReal.ofReal (C₂ / δ * Real.sqrt (phaseLen C₀ T j) *
              Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2)) →
      ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
        ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
        alg.multiExp ν Pω (phaseLen C₀ T j) (numCopies C₀ T)
            (fun hs => if RefineGood E lam δ (acc δ j) c.region hs then 0 else 1) ≤
          ENNReal.ofReal (1 / T)) := by
  intro C₁ C₂ hC₁ hC₂
  obtain ⟨C₀, hC₀, hbudget⟩ := refine_phase_budgets C₁ C₂ hC₁ hC₂
  refine ⟨C₀, hC₀, ?_⟩
  intro T η hη _ hT E hE δ c hηδ hδmu hmu hc lam hlam _ j hj
    Ω mΩ Pω iPω alg hquery hag ν hmean hval
  have hTpos : 0 < T := by
    have hKpos : 0 < gridK η := by
      unfold gridK
      exact Nat.ceil_pos.2 (one_div_pos.mpr hη)
    exact hKpos.trans_le hT
  have hδ : 0 < δ := hη.trans hηδ
  obtain ⟨hn, hε, hreg, hfail, htail⟩ := hbudget T j hTpos hj δ hδ
  have hconv : ConvexOn ℝ c.region (fun x => 1 / auxProfit E lam x) :=
    (lemma_6_2 E hE lam hlam).1.subset hc.1 hc.2.2.1
  have hbounds : ∀ x ∈ c.region, 0 < auxProfit E lam x ∧ auxProfit E lam x ≤ 10 * δ := by
    intro x hx
    have hxi := hc.1 hx
    obtain ⟨_, _, _, hpos, hupper, _, _⟩ := (lemma_6_2 E hE lam hlam).2 x hxi
    refine ⟨hpos, ?_⟩
    exact hupper.trans ((RefineGeometry.mu_le_muStar E hE.1 (RefineGeometry.intT_subset_unitSq hxi)).trans
      (by linarith))
  refine (refine_failure_le hδ hε (div_pos hC₁ hδ) hconv hbounds
    (measurable_auxProfit_reciprocal E lam) alg Pω ν hquery hmean hval hn _
    ((hag ν hmean hval).trans (ENNReal.ofReal_le_ofReal hreg))).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
  exact (add_le_add hfail htail).trans_eq (by field_simp; ring)

private theorem lemma_6_6 :
    (∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (c : Candidate), η < δ → δ ≤ muStar E → muStar E < 6 * δ → c.Valid E δ →
      ∀ lam : ℝ, 0 < lam → |Real.log (lam / c.param E)| ≤ 1 / 1000 * Real.sqrt (η / δ) →
      ∀ j : ℕ, (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω), IsProbabilityMeasure Pω →
      ∀ alg : BanditAlg (ℝ × ℝ) Ω, alg.QueriesIn c.region →
        (∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
          ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
          alg.regret ν Pω (phaseLen C₀ T j) (fun x => 1 / auxProfit E lam x) c.region ≤
            ENNReal.ofReal (C₂ / δ * Real.sqrt (phaseLen C₀ T j) *
              Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2)) →
      ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
        ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
        alg.multiExp ν Pω (phaseLen C₀ T j) (numCopies C₀ T)
            (fun hs => if RefineGood E lam δ (acc δ j) c.region hs then 0 else 1) ≤
          ENNReal.ofReal (1 / T)) ∧
    (∀ (η : ℝ), 0 < η → η < 1 →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (N : ℕ) (cs : Fin N → Candidate),
        η < δ → δ ≤ muStar E → muStar E < 6 * δ → (∀ i, (cs i).Valid E δ) →
      ∀ istar : Fin N, (cs istar).NearOpt E η δ →
      ∀ (A : ℕ → Finset (Fin N)) (z y : ℕ → Fin N → ℝ × ℝ) (ρ rhat : ℕ → Fin N → ℝ),
        A 0 = Finset.univ → (∀ i, z 0 i = (cs i).root) →
        (∀ j i, i ∈ A (j + 1) ↔
          i ∈ A j ∧ ∀ l ∈ A j, rhat j l - 10 * (η + acc δ j) ≤ rhat j i) →
        (∀ j, ∀ i ∈ A (j + 1), z (j + 1) i = y j i) →
        (∀ i, ∀ ρ' : ℝ, CalibValid E η δ (cs i) (cs i).root ρ' →
          muStar E - auxProfit E (ρ' * balance E (cs i).root) (cs i).root ≤
            65 * (η + acc δ 0)) ∧
        ∀ j : ℕ,
          (∀ j' ≤ j, ∀ i ∈ A j',
            CalibValid E η δ (cs i) (z j' i) (ρ j' i) ∧ y j' i ∈ (cs i).region ∧
            (∀ x ∈ (cs i).region,
              auxProfit E (ρ j' i * balance E (z j' i)) x - acc δ j' ≤ rhat j' i) ∧
            rhat j' i ≤ auxProfit E (ρ j' i * balance E (z j' i)) (y j' i) + acc δ j') →
          istar ∈ A (j + 1) ∧
          ∀ i ∈ A (j + 1), ∀ ρ' : ℝ, CalibValid E η δ (cs i) (z (j + 1) i) ρ' →
            muStar E - auxProfit E (ρ' * balance E (z (j + 1) i)) (z (j + 1) i) ≤
              65 * (η + acc δ (j + 1))) := ⟨refinement, successive_elimination⟩


end BilateralProfitRegular
end BundlePart008

open BilateralProfitRegular
open MeasureTheory MechanismDesign.BilateralTrade Classical

theorem solution :
    (∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (c : Candidate), η < δ → δ ≤ muStar E → muStar E < 6 * δ → c.Valid E δ →
      ∀ lam : ℝ, 0 < lam → |Real.log (lam / c.param E)| ≤ 1 / 1000 * Real.sqrt (η / δ) →
      ∀ j : ℕ, (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω), IsProbabilityMeasure Pω →
      ∀ alg : BanditAlg (ℝ × ℝ) Ω, alg.QueriesIn c.region →
        (∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
          ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
          alg.regret ν Pω (phaseLen C₀ T j) (fun x => 1 / auxProfit E lam x) c.region ≤
            ENNReal.ofReal (C₂ / δ * Real.sqrt (phaseLen C₀ T j) *
              Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2)) →
      ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
        ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
        alg.multiExp ν Pω (phaseLen C₀ T j) (numCopies C₀ T)
            (fun hs => if RefineGood E lam δ (acc δ j) c.region hs then 0 else 1) ≤
          ENNReal.ofReal (1 / T)) ∧
    (∀ (η : ℝ), 0 < η → η < 1 →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (N : ℕ) (cs : Fin N → Candidate),
        η < δ → δ ≤ muStar E → muStar E < 6 * δ → (∀ i, (cs i).Valid E δ) →
      ∀ istar : Fin N, (cs istar).NearOpt E η δ →
      ∀ (A : ℕ → Finset (Fin N)) (z y : ℕ → Fin N → ℝ × ℝ) (ρ rhat : ℕ → Fin N → ℝ),
        A 0 = Finset.univ → (∀ i, z 0 i = (cs i).root) →
        (∀ j i, i ∈ A (j + 1) ↔
          i ∈ A j ∧ ∀ l ∈ A j, rhat j l - 10 * (η + acc δ j) ≤ rhat j i) →
        (∀ j, ∀ i ∈ A (j + 1), z (j + 1) i = y j i) →
        (∀ i, ∀ ρ' : ℝ, CalibValid E η δ (cs i) (cs i).root ρ' →
          muStar E - auxProfit E (ρ' * balance E (cs i).root) (cs i).root ≤
            65 * (η + acc δ 0)) ∧
        ∀ j : ℕ,
          (∀ j' ≤ j, ∀ i ∈ A j',
            CalibValid E η δ (cs i) (z j' i) (ρ j' i) ∧ y j' i ∈ (cs i).region ∧
            (∀ x ∈ (cs i).region,
              auxProfit E (ρ j' i * balance E (z j' i)) x - acc δ j' ≤ rhat j' i) ∧
            rhat j' i ≤ auxProfit E (ρ j' i * balance E (z j' i)) (y j' i) + acc δ j') →
          istar ∈ A (j + 1) ∧
          ∀ i ∈ A (j + 1), ∀ ρ' : ℝ, CalibValid E η δ (cs i) (z (j + 1) i) ρ' →
            muStar E - auxProfit E (ρ' * balance E (z (j + 1) i)) (z (j + 1) i) ≤
              65 * (η + acc δ (j + 1))) := by
  exact BilateralProfitRegular.lemma_6_6
