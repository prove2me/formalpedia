-- Prove2me | solution 1 for FoundationsML.Stability.stability_generalization_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:18:53.089114+00:00
-- url     : https://prove2.me/submissions/f9d47298-a845-4d19-ba24-f5fa39573783

import Mathlib
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_UniformlyStable

open MeasureTheory
open MeasureTheory ProbabilityTheory

namespace FoundationsML.Stability

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

theorem sgb_v2_core
    {X Y Y' : Type*} [MeasurableSpace (X × Y)] (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 0 < m)
    (L : Y' → Y → ℝ) (hLnn : ∀ y' y, 0 ≤ L y' y)
    (A : (Fin m → X × Y) → (X → Y')) (β M : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hstab : UniformlyStable L A β)
    (hbound : ∀ S : Fin m → X × Y, ∀ z : X × Y, Loss L (A S) z ≤ M)
    (hAmeas : Measurable (fun p : (Fin m → X × Y) × (X × Y) => Loss L (A p.1) p.2))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × Y | GeneralizationError D L (A S) ≤
        EmpiricalError L S (A S) + β +
          (2 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact sgb_core_gen D n (fun S z => Loss L (A S) z) hAmeas M (fun S z => hLnn _ _) hbound β hβ
    hstab δ hδ hδ1

end FoundationsML.Stability

open FoundationsML.Stability


theorem solution
    {X Y Y' : Type*} [MeasurableSpace (X × Y)] (D : Measure (X × Y)) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 0 < m)
    (L : Y' → Y → ℝ) (hLnn : ∀ y' y, 0 ≤ L y' y)
    (A : (Fin m → X × Y) → (X → Y')) (β M : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hstab : UniformlyStable L A β)
    (hbound : ∀ S : Fin m → X × Y, ∀ z : X × Y, Loss L (A S) z ≤ M)
    (hAmeas : Measurable (fun p : (Fin m → X × Y) × (X × Y) => Loss L (A p.1) p.2))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × Y | GeneralizationError D L (A S) ≤
        EmpiricalError L S (A S) + β +
          (2 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by
  exact sgb_v2_core D hm L hLnn A β M hβ hM hstab hbound hAmeas δ hδ hδ1
