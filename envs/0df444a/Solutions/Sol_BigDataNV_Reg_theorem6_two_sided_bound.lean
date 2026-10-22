-- Prove2me | solution 1 for BigDataNV.Reg.theorem6_two_sided_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:24:30.523159+00:00
-- url     : https://prove2.me/submissions/bdc160b0-cd06-4310-94d3-84a35e3e8193

import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace BigDataNV.Reg

lemma sgb_symm0 {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (x : Ω) (p : Fin n → Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ => Ω) 0).symm (x, p) = Fin.cons x p := by
  simp [Fin.consEquiv]

lemma sgb_symmI {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (i : Fin (n+1)) (x : Ω) (p : Fin n → Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ => Ω) i).symm (x, p) = Fin.insertNth i x p := by
  simp [Fin.insertNthEquiv]

lemma sgb_int {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {h : α → ℝ} (hm : Measurable h) (C : ℝ) (hC : ∀ x, |h x| ≤ C) : Integrable h ν :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x))

lemma sgb_absint {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {h : α → ℝ} (C : ℝ) (hC : ∀ x, |h x| ≤ C) : |∫ x, h x ∂ν| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := h) (C := C)
    (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x))
  simpa [Real.norm_eq_abs] using this

lemma sgb_mcd_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ (n : ℕ) (c : Fin n → ℝ) (f : (Fin n → Ω) → ℝ), Measurable f → ∀ B : ℝ, (∀ x, |f x| ≤ B) →
    (∀ x i y, |f x - f (Function.update x i y)| ≤ c i) → ∀ t : ℝ,
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi fun _ => μ))) ∂(Measure.pi fun _ => μ)
      ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro c f _ B _ _ t
    have hf : f = fun _ => f default := funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [hf]
    simp
  | succ n ih =>
    intro c f hf B hB hc t
    set P := Measure.pi fun _ : Fin n => μ
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0
    have hp : MeasurePreserving e.symm (μ.prod P) (Measure.pi fun _ => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm _
    set F : Ω × (Fin n → Ω) → ℝ := fun p => f (e.symm p) with hFdef
    have hFm : Measurable F := hf.comp e.symm.measurable
    have hFB : ∀ p, |F p| ≤ B := fun p => hB _
    have hFc : ∀ x0 x', F (x0, x') = f (Fin.cons x0 x') := fun x0 x' => by
      simp [hFdef, e, Fin.consEquiv]
    have hEf : ∫ y, f y ∂(Measure.pi fun _ => μ) = ∫ p, F p ∂(μ.prod P) := by
      rw [← hp.integral_comp' (g := f)]
    set g : Ω → ℝ := fun x0 => ∫ x', F (x0, x') ∂P with hgdef
    have hgm : Measurable g := (hFm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
    have hgB : ∀ x, |g x| ≤ B := fun x => sgb_absint P B (fun x' => hFB _)
    have hEg : ∫ p, F p ∂(μ.prod P) = ∫ x, g x ∂μ :=
      integral_prod F (sgb_int _ hFm B hFB)
    set E := ∫ p, F p ∂(μ.prod P)
    have hEB : |E| ≤ B := sgb_absint _ B hFB
    -- the inner bound
    have hinner : ∀ x0, ∫ x', Real.exp (t * (F (x0, x') - g x0)) ∂P
        ≤ Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8) := by
      intro x0
      refine ih (fun j => c j.succ) (fun x' => F (x0, x')) (hFm.comp measurable_prodMk_left) B
        (fun x' => hFB _) ?_ t
      intro x j y
      have := hc (Fin.cons x0 x) j.succ y
      rw [hFc, hFc, Fin.cons_update]; exact this
    -- the Hoeffding bound
    have hgdiff : ∀ x y, g x - g y ≤ c 0 := by
      intro x y
      have h1 : g x - g y = ∫ x', (F (x, x') - F (y, x')) ∂P := by
        exact (integral_sub (sgb_int _ (hFm.comp measurable_prodMk_left) B (fun _ => hFB _))
          (sgb_int _ (hFm.comp measurable_prodMk_left) B (fun _ => hFB _))).symm
      rw [h1]
      have h2 : ∀ x', F (x, x') - F (y, x') ≤ c 0 := by
        intro x'
        have := hc (Fin.cons x x') 0 y
        rw [Fin.update_cons_zero] at this
        rw [hFc, hFc]
        exact (le_abs_self _).trans this
      calc ∫ x', (F (x, x') - F (y, x')) ∂P ≤ ∫ _x', c 0 ∂P :=
            integral_mono (sgb_int _ ((hFm.comp measurable_prodMk_left).sub
              (hFm.comp measurable_prodMk_left)) (2 * B) (fun x' => by
                have := hFB (x, x'); have := hFB (y, x')
                rw [abs_le] at *; constructor <;> linarith))
              (integrable_const _) h2
        _ = c 0 := by simp
    have hout : ∫ x, Real.exp (t * (g x - E)) ∂μ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) := by
      have hne : Nonempty Ω := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        have := measure_univ (μ := μ)
        rw [Set.univ_eq_empty_iff.mpr hne] at this
        simp at this
      set a := ⨅ x, g x
      have hbdd : BddBelow (Set.range g) := ⟨-B, by
        rintro _ ⟨x, rfl⟩; have := hgB x; rw [abs_le] at this; linarith⟩
      have hIcc : ∀ x, g x ∈ Set.Icc a (a + c 0) := by
        intro x
        refine ⟨ciInf_le hbdd x, ?_⟩
        have : g x - c 0 ≤ a := le_ciInf (fun y => by linarith [hgdiff x y])
        linarith
      have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) hgm.aemeasurable
        (Filter.Eventually.of_forall hIcc)
      have hmgf := hH.mgf_le t
      rw [← hEg] at hmgf
      unfold mgf at hmgf
      refine hmgf.trans (le_of_eq ?_)
      congr 1
      simp only [add_sub_cancel_left, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm,
        Real.norm_eq_abs, NNReal.coe_ofNat]
      rw [div_pow, sq_abs]; ring
    -- assemble
    rw [hEf, ← hp.integral_comp' (g := fun x => Real.exp (t * (f x - E)))]
    change ∫ p, Real.exp (t * (F p - E)) ∂(μ.prod P) ≤ _
    have hexpInt : Integrable (fun p => Real.exp (t * (F p - E))) (μ.prod P) := by
      refine sgb_int _ (by fun_prop) (Real.exp (|t| * (2 * B))) (fun p => ?_)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hFB p
      have h2 : |F p - E| ≤ 2 * B := by
        rw [abs_le] at *; constructor <;> linarith
      calc t * (F p - E) ≤ |t * (F p - E)| := le_abs_self _
        _ = |t| * |F p - E| := abs_mul _ _
        _ ≤ |t| * (2 * B) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    rw [integral_prod _ hexpInt]
    have hsplit : ∀ x0, ∫ x', Real.exp (t * (F (x0, x') - E)) ∂P =
        (∫ x', Real.exp (t * (F (x0, x') - g x0)) ∂P) * Real.exp (t * (g x0 - E)) := by
      intro x0
      rw [← integral_mul_const]
      congr 1; funext x'
      rw [← Real.exp_add]; congr 1; ring
    simp_rw [hsplit]
    have hgexpInt : Integrable (fun x => Real.exp (t * (g x - E))) μ := by
      refine sgb_int _ (by fun_prop) (Real.exp (|t| * (2 * B))) (fun p => ?_)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hgB p
      have h2 : |g p - E| ≤ 2 * B := by
        rw [abs_le] at *; constructor <;> linarith
      calc t * (g p - E) ≤ |t * (g p - E)| := le_abs_self _
        _ = |t| * |g p - E| := abs_mul _ _
        _ ≤ |t| * (2 * B) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    calc ∫ x0, (∫ x', Real.exp (t * (F (x0, x') - g x0)) ∂P) * Real.exp (t * (g x0 - E)) ∂μ
        ≤ ∫ x0, Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8) * Real.exp (t * (g x0 - E)) ∂μ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x0 => mul_nonneg
              (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le)
          · exact hgexpInt.const_mul _
          · exact Filter.Eventually.of_forall (fun x0 =>
              mul_le_mul_of_nonneg_right (hinner x0) (Real.exp_pos _).le)
      _ = Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8) * ∫ x0, Real.exp (t * (g x0 - E)) ∂μ :=
          integral_const_mul _ _
      _ ≤ Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hout (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring

lemma sgb_exp_le {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (n : ℕ) (ℓ : (Fin (n+1) → Ω) → Ω → ℝ)
    (hℓ : Measurable (fun p : (Fin (n+1) → Ω) × Ω => ℓ p.1 p.2))
    (M : ℝ) (h0 : ∀ S z, 0 ≤ ℓ S z) (hM : ∀ S z, ℓ S z ≤ M) (β : ℝ)
    (hstab : ∀ S S' : Fin (n+1) → Ω, (∃ i, ∀ j, j ≠ i → S j = S' j) → ∀ z, |ℓ S z - ℓ S' z| ≤ β)
    (i : Fin (n+1)) :
    ∫ S, (∫ z, ℓ S z ∂D) ∂(Measure.pi fun _ => D) ≤
      ∫ S, ℓ S (S i) ∂(Measure.pi fun _ => D) + β := by
  set P := Measure.pi fun _ : Fin n => D
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) i
  have hp : MeasurePreserving e.symm (D.prod P) (Measure.pi fun _ => D) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => D) i).symm _
  have hB : ∀ S z, |ℓ S z| ≤ M := fun S z => abs_le.mpr ⟨by linarith [h0 S z, hM S z], hM S z⟩
  have hes : Measurable e.symm := e.symm.measurable
  -- K S' := ∫ z, ℓ (ins z S') z
  set K : (Fin n → Ω) → ℝ := fun S' => ∫ z, ℓ (e.symm (z, S')) z ∂D with hK
  have hKm : Measurable K := by
    have : Measurable (fun q : (Fin n → Ω) × Ω => ℓ (e.symm (q.2, q.1)) q.2) :=
      hℓ.comp ((hes.comp (measurable_snd.prodMk measurable_fst)).prodMk measurable_snd)
    exact (this.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hKB : ∀ S', |K S'| ≤ M := fun S' => sgb_absint D M (fun z => hB _ _)
  -- R ∘ e.symm
  have hRm : Measurable (fun S => ∫ z, ℓ S z ∂D) :=
    (hℓ.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have h1 : ∫ S, (∫ z, ℓ S z ∂D) ∂(Measure.pi fun _ => D) =
      ∫ p, (∫ z, ℓ (e.symm p) z ∂D) ∂(D.prod P) :=
    (hp.integral_comp' (g := fun S => ∫ z, ℓ S z ∂D)).symm
  have h2 : ∫ S, ℓ S (S i) ∂(Measure.pi fun _ => D) =
      ∫ p, ℓ (e.symm p) p.1 ∂(D.prod P) := by
    rw [← hp.integral_comp' (g := fun S => ℓ S (S i))]
    congr 1; funext p
    congr 1
    simp [e, Fin.insertNthEquiv]
  have hmono : ∀ p : Ω × (Fin n → Ω), ∫ z, ℓ (e.symm p) z ∂D ≤ K p.2 + β := by
    rintro ⟨x, S'⟩
    have hint : ∀ S, Integrable (fun z => ℓ S z) D := fun S =>
      sgb_int D (hℓ.comp (measurable_const.prodMk measurable_id)) M (fun z => hB _ _)
    calc ∫ z, ℓ (e.symm (x, S')) z ∂D ≤ ∫ z, (ℓ (e.symm (z, S')) z + β) ∂D := by
          apply integral_mono (hint _)
          · refine Integrable.add (sgb_int D ?_ M (fun z => hB _ _)) (integrable_const _)
            exact hℓ.comp ((hes.comp (measurable_id.prodMk measurable_const)).prodMk measurable_id)
          · intro z
            have := hstab (e.symm (x, S')) (e.symm (z, S')) ⟨i, fun j hj => by
              obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
              simp [e, Fin.insertNthEquiv]⟩ z
            rw [abs_le] at this; linarith
      _ = K S' + β := by
          rw [integral_add _ (integrable_const _)]
          · simp [hK]
          · exact sgb_int D (hℓ.comp ((hes.comp (measurable_id.prodMk measurable_const)).prodMk
              measurable_id)) M (fun z => hB _ _)
  rw [h1, h2]
  have hA : Integrable (fun p : Ω × (Fin n → Ω) => ∫ z, ℓ (e.symm p) z ∂D) (D.prod P) :=
    sgb_int _ (hRm.comp hes) M (fun p => sgb_absint D M (fun z => hB _ _))
  have hKi : Integrable (fun p : Ω × (Fin n → Ω) => K p.2 + β) (D.prod P) :=
    (sgb_int _ (hKm.comp measurable_snd) M (fun p => hKB _)).add (integrable_const _)
  have hL : Integrable (fun p : Ω × (Fin n → Ω) => ℓ (e.symm p) p.1) (D.prod P) :=
    sgb_int _ (hℓ.comp (hes.prodMk measurable_fst)) M (fun p => hB _ _)
  calc ∫ p, (∫ z, ℓ (e.symm p) z ∂D) ∂(D.prod P) ≤ ∫ p, (K p.2 + β) ∂(D.prod P) :=
        integral_mono hA hKi hmono
    _ = ∫ p, ℓ (e.symm p) p.1 ∂(D.prod P) + β := by
        rw [integral_add (f := fun p : Ω × (Fin n → Ω) => K p.2)
          (sgb_int _ (hKm.comp measurable_snd) M (fun p => hKB _))
          (integrable_const _)]
        congr 1
        · rw [integral_prod_symm (fun p : Ω × (Fin n → Ω) => K p.2)
              (sgb_int _ (hKm.comp measurable_snd) M (fun p => hKB _)),
            integral_prod_symm (fun p : Ω × (Fin n → Ω) => ℓ (e.symm p) p.1) hL]
          simp [hK]
        · simp

lemma sgb_core_gen {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (n : ℕ) (ℓ : (Fin (n+1) → Ω) → Ω → ℝ)
    (hℓ : Measurable (fun p : (Fin (n+1) → Ω) × Ω => ℓ p.1 p.2))
    (M : ℝ) (h0 : ∀ S z, 0 ≤ ℓ S z) (hM : ∀ S z, ℓ S z ≤ M) (β : ℝ) (hβ : 0 ≤ β)
    (hstab : ∀ S S' : Fin (n+1) → Ω, (∃ i, ∀ j, j ≠ i → S j = S' j) → ∀ z, |ℓ S z - ℓ S' z| ≤ β)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin (n+1) => D)
      {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ)))}).toReal := by
  set m : ℝ := ((n+1 : ℕ) : ℝ) with hmdef
  have hm : 0 < m := by rw [hmdef]; positivity
  set Pm := Measure.pi (fun _ : Fin (n+1) => D)
  have hB : ∀ S z, |ℓ S z| ≤ M := fun S z => abs_le.mpr ⟨by linarith [h0 S z, hM S z], hM S z⟩
  have hne : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := D)
    rw [Set.univ_eq_empty_iff.mpr hne] at this
    simp at this
  have hM0 : 0 ≤ M := (h0 (fun _ => Classical.arbitrary Ω) (Classical.arbitrary Ω)).trans (hM _ _)
  set R : (Fin (n+1) → Ω) → ℝ := fun S => ∫ z, ℓ S z ∂D with hR
  set Rh : (Fin (n+1) → Ω) → ℝ := fun S => (1 / m) * ∑ i, ℓ S (S i) with hRh
  set Φ : (Fin (n+1) → Ω) → ℝ := fun S => R S - Rh S with hΦ
  have hRm : Measurable R := (hℓ.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hRhm : Measurable Rh := by
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun i _ => hℓ.comp (measurable_id.prodMk (measurable_pi_apply i)))
  have hΦm : Measurable Φ := hRm.sub hRhm
  have hR01 : ∀ S, 0 ≤ R S ∧ R S ≤ M := fun S =>
    ⟨integral_nonneg (fun z => h0 S z), by
      have := sgb_absint D M (fun z => hB S z); exact (le_abs_self _).trans this⟩
  have hRh01 : ∀ S, 0 ≤ Rh S ∧ Rh S ≤ M := by
    intro S
    constructor
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => h0 _ _))
    · have : ∑ i, ℓ S (S i) ≤ ∑ _i : Fin (n+1), M := Finset.sum_le_sum (fun i _ => hM _ _)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      calc (1 / m) * ∑ i, ℓ S (S i) ≤ (1 / m) * (((n+1 : ℕ) : ℝ) * M) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
        _ = M := by rw [← hmdef]; field_simp
  have hΦB : ∀ S, |Φ S| ≤ 2 * M := by
    intro S; have := hR01 S; have := hRh01 S
    rw [abs_le]; constructor <;> simp only [hΦ] <;> linarith
  -- bounded differences
  set c : ℝ := 2 * β + M / m with hc
  have hdiff : ∀ S i y, |Φ S - Φ (Function.update S i y)| ≤ c := by
    intro S i y
    set S' := Function.update S i y
    have hst : ∀ z, |ℓ S z - ℓ S' z| ≤ β := hstab S S' ⟨i, fun j hj => by
      simp [S', Function.update_of_ne hj]⟩
    have h1 : |R S - R S'| ≤ β := by
      have : R S - R S' = ∫ z, (ℓ S z - ℓ S' z) ∂D := by
        rw [integral_sub]
        · exact sgb_int D (hℓ.comp (measurable_const.prodMk measurable_id)) M (fun z => hB _ _)
        · exact sgb_int D (hℓ.comp (measurable_const.prodMk measurable_id)) M (fun z => hB _ _)
      rw [this]; exact sgb_absint D β hst
    have h2 : |Rh S - Rh S'| ≤ β + M / m := by
      have hterm : ∀ j, |ℓ S (S j) - ℓ S' (S' j)| ≤ β + (if j = i then M else 0) := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [if_true]
          have := hB S (S j); have := hB S' (S' j)
          have := h0 S (S j); have := h0 S' (S' j); have := hM S (S j); have := hM S' (S' j)
          rw [abs_le]; constructor <;> linarith
        · simp only [hj, if_false, add_zero]
          have : S' j = S j := by simp [S', Function.update_of_ne hj]
          rw [this]; exact hst _
      have hsum : |∑ j, ℓ S (S j) - ∑ j, ℓ S' (S' j)| ≤ m * β + M := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum (fun j _ => hterm j)).trans (le_of_eq ?_)
        rw [Finset.sum_add_distrib]
        simp [hmdef]
      have : Rh S - Rh S' = (1 / m) * (∑ j, ℓ S (S j) - ∑ j, ℓ S' (S' j)) := by
        simp only [hRh]; ring
      rw [this, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
      calc 1 / m * |∑ j, ℓ S (S j) - ∑ j, ℓ S' (S' j)| ≤ 1 / m * (m * β + M) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = β + M / m := by field_simp
    have : Φ S - Φ S' = (R S - R S') - (Rh S - Rh S') := by simp only [hΦ]; ring
    rw [this]
    calc |(R S - R S') - (Rh S - Rh S')| ≤ |R S - R S'| + |Rh S - Rh S'| := abs_sub _ _
      _ ≤ β + (β + M / m) := add_le_add h1 h2
      _ = c := by rw [hc]; ring
  -- expectation bound
  have hEΦ : ∫ S, Φ S ∂Pm ≤ β := by
    have hRi : Integrable R Pm := sgb_int _ hRm M (fun S => abs_le.mpr ⟨by linarith [(hR01 S).1], (hR01 S).2⟩)
    have hli : ∀ i : Fin (n+1), Integrable (fun S => ℓ S (S i)) Pm := fun i =>
      sgb_int _ (hℓ.comp (measurable_id.prodMk (measurable_pi_apply i))) M (fun S => hB _ _)
    have hE : ∀ i : Fin (n+1), ∫ S, R S ∂Pm ≤ ∫ S, ℓ S (S i) ∂Pm + β := fun i =>
      sgb_exp_le D n ℓ hℓ M h0 hM β hstab i
    have hRhE : ∫ S, Rh S ∂Pm = (1 / m) * ∑ i, ∫ S, ℓ S (S i) ∂Pm := by
      simp only [hRh]
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hli i)]
    have hsumE : ∑ i : Fin (n+1), (∫ S, R S ∂Pm - β) ≤ ∑ i, ∫ S, ℓ S (S i) ∂Pm :=
      Finset.sum_le_sum (fun i _ => by linarith [hE i])
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumE
    have hΦE : ∫ S, Φ S ∂Pm = ∫ S, R S ∂Pm - ∫ S, Rh S ∂Pm := integral_sub hRi
      (sgb_int _ hRhm M (fun S => abs_le.mpr ⟨by linarith [(hRh01 S).1], (hRh01 S).2⟩))
    rw [hΦE, hRhE]
    have : (1 / m) * (m * (∫ S, R S ∂Pm - β)) ≤ (1 / m) * ∑ i, ∫ S, ℓ S (S i) ∂Pm :=
      mul_le_mul_of_nonneg_left (by rw [hmdef]; exact_mod_cast hsumE) (by positivity)
    have h' : (1 / m) * (m * (∫ S, R S ∂Pm - β)) = ∫ S, R S ∂Pm - β := by field_simp
    linarith
  -- trivial case
  by_cases hcz : c = 0
  · have hβ0 : β = 0 := by
      have : 0 ≤ M / m := div_nonneg hM0 hm.le
      linarith
    have hM00 : M = 0 := by
      have : M / m = 0 := by linarith
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · linarith
    have hl0 : ∀ S z, ℓ S z = 0 := fun S z => le_antisymm (hM00 ▸ hM S z) (h0 S z)
    have : {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ)))}
        = Set.univ := by
      ext S; simp [hl0, hβ0, hM00]
    rw [this, measure_univ]; simp; linarith
  have hcpos : 0 < c := by
    have : 0 ≤ M / m := div_nonneg hM0 hm.le
    rcases lt_or_eq_of_le (show 0 ≤ c by rw [hc]; positivity) with h | h
    · exact h
    · exact absurd h.symm hcz
  -- subgaussian
  set E := ∫ S, Φ S ∂Pm
  set cc : NNReal := Real.toNNReal (m * c ^ 2 / 4) with hcc
  have hccv : (cc : ℝ) = m * c ^ 2 / 4 := Real.coe_toNNReal _ (by positivity)
  have hsg : HasSubgaussianMGF (fun S => Φ S - E) cc Pm := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · refine sgb_int _ (by fun_prop) (Real.exp (|t| * (4 * M))) (fun p => ?_)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hΦB p
      have h3 : |E| ≤ 2 * M := sgb_absint _ _ hΦB
      have h2 : |Φ p - E| ≤ 4 * M := by
        rw [abs_le] at *; constructor <;> linarith
      calc t * (Φ p - E) ≤ |t * (Φ p - E)| := le_abs_self _
        _ = |t| * |Φ p - E| := abs_mul _ _
        _ ≤ |t| * (4 * M) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    · have := sgb_mcd_mgf D (n+1) (fun _ => c) Φ hΦm (2 * M) hΦB (fun S i y => hdiff S i y) t
      unfold mgf
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [hccv]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hmdef]; ring
  set L := Real.log (1 / δ)
  have hL : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hδ, hδ1⟩)
  set ε := (2 * m * β + M) * Real.sqrt (L / (2 * m))
  have hmc : 2 * m * β + M = m * c := by rw [hc]; field_simp
  have hε : 0 ≤ ε := mul_nonneg (by rw [hmc]; positivity) (Real.sqrt_nonneg _)
  have htail := hsg.measure_ge_le hε
  have hexp : Real.exp (-ε ^ 2 / (2 * (cc : ℝ))) = δ := by
    have : ε ^ 2 = (m * c) ^ 2 * (L / (2 * m)) := by
      simp only [ε]; rw [mul_pow, Real.sq_sqrt (by positivity), hmc]
    rw [this, hccv]
    have : -((m * c) ^ 2 * (L / (2 * m))) / (2 * (m * c ^ 2 / 4)) = -L := by
      field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]; simp
  rw [hexp] at htail
  -- the good set contains the complement of the tail event
  have hsub : {S | ε ≤ Φ S - E}ᶜ ⊆ {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ)))} := by
    intro S hS
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hS
    show R S ≤ Rh S + β + ε
    have : Φ S = R S - Rh S := rfl
    linarith
  have hmeas : MeasurableSet {S | ε ≤ Φ S - E} := measurableSet_le measurable_const (hΦm.sub_const _)
  have := measureReal_mono (μ := Pm) hsub
  rw [probReal_compl_eq_one_sub hmeas] at this
  change 1 - δ ≤ Pm.real _
  linarith

lemma th6_meas_good {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (n : ℕ) (ℓ : (Fin (n+1) → Ω) → Ω → ℝ)
    (hℓ : Measurable (fun p : (Fin (n+1) → Ω) × Ω => ℓ p.1 p.2)) (β K : ℝ) :
    MeasurableSet {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β + K} := by
  have hRm : Measurable (fun S => ∫ z, ℓ S z ∂D) :=
    (hℓ.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hRhm : Measurable (fun S : Fin (n+1) → Ω => (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i)) := by
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun i _ => hℓ.comp (measurable_id.prodMk (measurable_pi_apply i)))
  exact measurableSet_le hRm ((hRhm.add_const _).add_const _)

lemma th6_prob_bad {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
    (n : ℕ) (ℓ : (Fin (n+1) → Ω) → Ω → ℝ)
    (hℓ : Measurable (fun p : (Fin (n+1) → Ω) × Ω => ℓ p.1 p.2))
    (M : ℝ) (h0 : ∀ S z, 0 ≤ ℓ S z) (hM : ∀ S z, ℓ S z ≤ M) (β : ℝ) (hβ : 0 ≤ β)
    (hstab : ∀ S S' : Fin (n+1) → Ω, (∃ i, ∀ j, j ≠ i → S j = S' j) → ∀ z, |ℓ S z - ℓ S' z| ≤ β)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi (fun _ : Fin (n+1) => D))
      {S : Fin (n+1) → Ω | ¬ (∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ))))}
      ≤ ENNReal.ofReal δ := by
  have h := sgb_core_gen D n ℓ hℓ M h0 hM β hβ hstab δ hδ hδ1
  have hm := th6_meas_good D n ℓ hℓ β ((2 * ((n+1 : ℕ) : ℝ) * β + M) *
    Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ))))
  have := probReal_compl_eq_one_sub (μ := Measure.pi (fun _ : Fin (n+1) => D)) hm
  have h2 : (Measure.pi (fun _ : Fin (n+1) => D)).real
      {S : Fin (n+1) → Ω | ¬ (∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ))))}
      ≤ δ := by
    have e : {S : Fin (n+1) → Ω | ¬ (∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ))))}
        = {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ)))}ᶜ := by
      ext S; simp
    rw [e, this]
    have h' : 1 - δ ≤ (Measure.pi (fun _ : Fin (n+1) => D)).real
      {S : Fin (n+1) → Ω | ∫ z, ℓ S z ∂D ≤
        (1 / ((n+1 : ℕ) : ℝ)) * ∑ i, ℓ S (S i) + β +
          (2 * ((n+1 : ℕ) : ℝ) * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * ((n+1 : ℕ) : ℝ)))} := h
    linarith
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h2

theorem th6_core {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (Z0 : Set Z) (hμ : μ Z0ᶜ = 0)
    (ℓ : H → Z → ℝ) (n : ℕ) (hn : 1 ≤ n) (A : (Fin n → Z) → H)
    (Aloo : Fin n → (Fin n → Z) → H)
    (hloo : ∀ (i : Fin n) (S S' : Fin n → Z), (∀ j, j ≠ i → S j = S' j) → Aloo i S = Aloo i S')
    (α M : ℝ)
    (hstab : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ i : Fin n, ∀ z ∈ Z0,
      |ℓ (A S) z - ℓ (Aloo i S) z| ≤ α)
    (hbound : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ z ∈ Z0, 0 ≤ ℓ (A S) z ∧ ℓ (A S) z ≤ M)
    (hmeas : Measurable (fun q : (Fin n → Z) × Z => ℓ (A q.1) q.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | 2 * α + (4 * (n : ℝ) * α + M) * Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |(∫ z, ℓ (A S) z ∂μ) - (1 / (n : ℝ)) * ∑ i, ℓ (A S) (S i)|} ≤ ENNReal.ofReal δ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  classical
  set N := toMeasurable μ Z0ᶜ with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hμ
  set Z1 := Nᶜ with hZ1
  have hZ1m : MeasurableSet Z1 := hNm.compl
  have hZ1sub : Z1 ⊆ Z0 := by
    intro z hz; by_contra h
    exact hz (subset_toMeasurable μ Z0ᶜ h)
  have hZ1ne : Z1.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : N = Set.univ := Set.compl_empty_iff.mp h
    rw [this] at hN0
    simp at hN0
  obtain ⟨z0, hz0⟩ := hZ1ne
  set ρ : Z → Z := fun z => if z ∈ Z1 then z else z0 with hρ
  have hρm : Measurable ρ := Measurable.ite hZ1m measurable_id measurable_const
  have hρZ1 : ∀ z, ρ z ∈ Z1 := fun z => by
    by_cases h : z ∈ Z1 <;> simp [hρ, h, hz0]
  have hρid : ∀ z ∈ Z1, ρ z = z := fun z h => by simp [hρ, h]
  have hα : 0 ≤ α :=
    (abs_nonneg _).trans (hstab (fun _ => z0) (fun _ => hZ1sub hz0) 0 z0 (hZ1sub hz0))
  set L : (Fin (k+1) → Z) → Z → ℝ := fun S z => ℓ (A (fun j => ρ (S j))) (ρ z) with hL
  have hLm : Measurable (fun p : (Fin (k+1) → Z) × Z => L p.1 p.2) := by
    have : Measurable (fun p : (Fin (k+1) → Z) × Z => ((fun j => ρ (p.1 j)), ρ p.2)) :=
      (measurable_pi_lambda _ (fun j => hρm.comp ((measurable_pi_apply j).comp
        measurable_fst))).prodMk (hρm.comp measurable_snd)
    exact hmeas.comp this
  have hZ1S : ∀ S : Fin (k+1) → Z, ∀ j, ρ (S j) ∈ Z0 := fun S j => hZ1sub (hρZ1 _)
  have hL0 : ∀ S z, 0 ≤ L S z := fun S z =>
    (hbound _ (hZ1S S) _ (hZ1sub (hρZ1 z))).1
  have hLM : ∀ S z, L S z ≤ M := fun S z =>
    (hbound _ (hZ1S S) _ (hZ1sub (hρZ1 z))).2
  have hLstab : ∀ S S' : Fin (k+1) → Z, (∃ i, ∀ j, j ≠ i → S j = S' j) → ∀ z,
      |L S z - L S' z| ≤ 2 * α := by
    rintro S S' ⟨i, hi⟩ z
    have h1 := hstab (fun j => ρ (S j)) (hZ1S S) i (ρ z) (hZ1sub (hρZ1 z))
    have h2 := hstab (fun j => ρ (S' j)) (hZ1S S') i (ρ z) (hZ1sub (hρZ1 z))
    have h3 : Aloo i (fun j => ρ (S j)) = Aloo i (fun j => ρ (S' j)) :=
      hloo i _ _ (fun j hj => by simp [hi j hj])
    rw [h3] at h1
    obtain ⟨a1, a2⟩ := abs_le.mp h1
    obtain ⟨b1, b2⟩ := abs_le.mp h2
    simp only [hL]
    rw [abs_le]; constructor <;> linarith
  have G1 := th6_prob_bad μ k L hLm M hL0 hLM (2 * α) (by linarith) hLstab (δ / 2)
    (by linarith) (by linarith)
  set L' : (Fin (k+1) → Z) → Z → ℝ := fun S z => M - L S z with hL'
  have hL'm : Measurable (fun p : (Fin (k+1) → Z) × Z => L' p.1 p.2) :=
    measurable_const.sub hLm
  have G2 := th6_prob_bad μ k L' hL'm M (fun S z => by simp only [hL']; linarith [hLM S z])
    (fun S z => by simp only [hL']; linarith [hL0 S z]) (2 * α) (by linarith)
    (fun S S' h z => by
      have := hLstab S S' h z
      simp only [hL']
      rw [abs_le] at *; constructor <;> linarith [this.1, this.2]) (δ / 2)
    (by linarith) (by linarith)
  -- null set
  set Pm := Measure.pi fun _ : Fin (k+1) => μ with hPm
  have hnull : Pm {S : Fin (k+1) → Z | ¬ ∀ j, S j ∈ Z1} = 0 := by
    have : {S : Fin (k+1) → Z | ¬ ∀ j, S j ∈ Z1} = ⋃ j, (fun S : Fin (k+1) → Z => S j) ⁻¹' N := by
      ext S; simp [hZ1]
    rw [this]
    refine measure_iUnion_null (fun j => ?_)
    exact Measure.pi_eval_preimage_null (fun _ => μ) hN0
  have hae : ∀ᵐ z ∂μ, z ∈ Z1 := by
    rw [ae_iff]; simpa [hZ1] using hN0
  refine le_trans (measure_mono (t := {S : Fin (k+1) → Z | ¬ ∀ j, S j ∈ Z1} ∪
      ({S | ¬ (∫ z, L S z ∂μ ≤ (1 / ((k+1 : ℕ) : ℝ)) * ∑ i, L S (S i) + 2 * α +
          (2 * ((k+1 : ℕ) : ℝ) * (2 * α) + M) *
            Real.sqrt (Real.log (1 / (δ / 2)) / (2 * ((k+1 : ℕ) : ℝ))))} ∪
       {S | ¬ (∫ z, L' S z ∂μ ≤ (1 / ((k+1 : ℕ) : ℝ)) * ∑ i, L' S (S i) + 2 * α +
          (2 * ((k+1 : ℕ) : ℝ) * (2 * α) + M) *
            Real.sqrt (Real.log (1 / (δ / 2)) / (2 * ((k+1 : ℕ) : ℝ))))})) ?_) ?_
  · intro S hS
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hZ, g1, g2⟩ := hcon
    have hρS : (fun j => ρ (S j)) = S := funext fun j => hρid _ (hZ j)
    have hRint : ∫ z, L S z ∂μ = ∫ z, ℓ (A S) z ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      simp only [hL, hρS, hρid z hz]
    have hLS : ∀ i, L S (S i) = ℓ (A S) (S i) := fun i => by
      simp only [hL, hρS, hρid _ (hZ i)]
    have hint : Integrable (fun z => L S z) μ :=
      sgb_int μ (hLm.comp (measurable_const.prodMk measurable_id)) M
        (fun z => abs_le.mpr ⟨by linarith [hL0 S z, hLM S z], hLM S z⟩)
    have hRint' : ∫ z, L' S z ∂μ = M - ∫ z, L S z ∂μ := by
      simp only [hL']
      rw [integral_sub (integrable_const _) hint]; simp
    simp only [hRint, hLS, hL'] at g1 g2 hRint'
    set m : ℝ := ((k+1 : ℕ) : ℝ) with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    have hsum : ∑ i, (M - ℓ (A S) (S i)) = m * M - ∑ i, ℓ (A S) (S i) := by
      rw [Finset.sum_sub_distrib]; simp [hm]
    have hlog : Real.log (1 / (δ / 2)) = Real.log (2 / δ) := by rw [one_div_div]
    rw [hsum, hlog] at g2
    rw [hlog] at g1
    rw [hRint'] at g2
    have e1 : (1 / m) * (m * M - ∑ i, ℓ (A S) (S i)) = M - (1 / m) * ∑ i, ℓ (A S) (S i) := by
      field_simp
    rw [e1] at g2
    have hK : 2 * m * (2 * α) + M = 4 * m * α + M := by ring
    rw [hK] at g1 g2
    have : |(∫ z, ℓ (A S) z ∂μ) - (1 / m) * ∑ i, ℓ (A S) (S i)| ≤
        2 * α + (4 * m * α + M) * Real.sqrt (Real.log (2 / δ) / (2 * m)) := by
      rw [abs_le]; constructor <;> linarith
    exact absurd hS (not_lt.mpr this)
  · calc Pm ({S : Fin (k+1) → Z | ¬ ∀ j, S j ∈ Z1} ∪ (_ ∪ _))
        ≤ Pm {S : Fin (k+1) → Z | ¬ ∀ j, S j ∈ Z1} + (Pm _ + Pm _) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ 0 + (ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2)) := by
          rw [hnull]; exact add_le_add le_rfl (add_le_add G1 G2)
      _ = ENNReal.ofReal δ := by
          rw [zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1; ring

end BigDataNV.Reg

open BigDataNV.Reg


theorem solution {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (Z0 : Set Z) (hμ : μ Z0ᶜ = 0)
    (ℓ : H → Z → ℝ) (n : ℕ) (hn : 1 ≤ n) (A : (Fin n → Z) → H)
    (Aloo : Fin n → (Fin n → Z) → H)
    (hloo : ∀ (i : Fin n) (S S' : Fin n → Z), (∀ j, j ≠ i → S j = S' j) → Aloo i S = Aloo i S')
    (α M : ℝ)
    (hstab : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ i : Fin n, ∀ z ∈ Z0,
      |ℓ (A S) z - ℓ (Aloo i S) z| ≤ α)
    (hbound : ∀ S : Fin n → Z, (∀ j, S j ∈ Z0) → ∀ z ∈ Z0, 0 ≤ ℓ (A S) z ∧ ℓ (A S) z ≤ M)
    (hmeas : Measurable (fun q : (Fin n → Z) × Z => ℓ (A q.1) q.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | 2 * α + (4 * (n : ℝ) * α + M) * Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |(∫ z, ℓ (A S) z ∂μ) - (1 / (n : ℝ)) * ∑ i, ℓ (A S) (S i)|} ≤ ENNReal.ofReal δ := by
  exact th6_core μ Z0 hμ ℓ n hn A Aloo hloo α M hstab hbound hmeas δ hδ0 hδ1
