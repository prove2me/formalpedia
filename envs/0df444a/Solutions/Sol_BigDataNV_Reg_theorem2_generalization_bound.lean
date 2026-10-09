-- Prove2me | solution 1 for BigDataNV.Reg.theorem2_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:10:33.172526+00:00
-- url     : https://prove2.me/submissions/2d9a353b-006c-4411-8546-2afd7112e1a8

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace P82cd

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma hoeff_step {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf

/-- McDiarmid's inequality, mgf form, uniform difference bound `c`. -/
theorem mcd_mgf {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (c B : ℝ) (hc : 0 ≤ c) : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), Measurable f →
    (∀ S, |f S| ≤ B) → (∀ S i z, |f (Function.update S i z) - f S| ≤ c) → ∀ t : ℝ,
    ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν)
      ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _ t
    have hfS : ∀ S, f S = f default := fun S => congrArg f (Subsingleton.elim _ _)
    simp [hfS]
  | succ n ih =>
    intro f hf hB hdiff t
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hmps := hmp.symm e
    set g : Ω → (Fin n → Ω) → ℝ := fun z w => f (Fin.cons z w) with hg
    have hge : ∀ p : Ω × (Fin n → Ω), f (e.symm p) = g p.1 p.2 := by
      intro p; simp [g, e]; try rfl
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = fun p => f (e.symm p) := by
        funext p; rw [hge p]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hgB : ∀ z w, |g z w| ≤ B := fun z w => hB _
    set hw : (Fin n → Ω) → ℝ := fun w => ∫ z, g z w ∂ν with hhw
    have hwm : Measurable hw :=
      (StronglyMeasurable.integral_prod_left (μ := ν) hgm.stronglyMeasurable).measurable
    have hwB : ∀ w, |hw w| ≤ B := fun w => abs_integral_le_of_bdd ν _ B fun z => hgB z w
    have hgz : ∀ w, Measurable fun z => g z w := fun w => hgm.comp (measurable_id.prodMk measurable_const)
    have hwdiff : ∀ w j y, |hw (Function.update w j y) - hw w| ≤ c := by
      intro w j y
      simp only [hw]
      rw [← integral_sub (int_of_bdd ν _ (hgz _) B fun z => hgB z _)
        (int_of_bdd ν _ (hgz _) B fun z => hgB z _)]
      refine abs_integral_le_of_bdd ν _ c fun z => ?_
      simp only [g, Fin.cons_update]
      exact hdiff _ _ _
    have hih := ih hw hwm hwB hwdiff t
    -- the mean
    have hint_f : Integrable (fun p : Ω × (Fin n → Ω) => g p.1 p.2) (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hgm B fun p => hgB p.1 p.2
    have hmean : ∫ S, f S ∂(Measure.pi fun _ => ν) = ∫ w, hw w ∂(Measure.pi fun _ => ν) := by
      rw [← hmps.integral_comp' (g := f)]
      simp_rw [hge]
      rw [integral_prod_symm _ hint_f]
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ S, f S ∂(Measure.pi fun _ => ν) := ⟨_, rfl⟩
    rw [← hm]
    rw [← hm] at hmean
    have hexpm : Measurable fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)) :=
      Real.measurable_exp.comp (measurable_const.mul (hgm.sub measurable_const))
    have hint_e : Integrable (fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)))
        (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hexpm (Real.exp (|t| * (B + |m|))) fun p => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hgB p.1 p.2
        calc t * (g p.1 p.2 - m) ≤ |t * (g p.1 p.2 - m)| := le_abs_self _
          _ = |t| * |g p.1 p.2 - m| := abs_mul _ _
          _ ≤ |t| * (B + |m|) := by
            gcongr
            calc |g p.1 p.2 - m| ≤ |g p.1 p.2| + |m| := abs_sub _ _
              _ ≤ B + |m| := by linarith
    have hstep : ∀ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ≤
        Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
      intro w
      have hosc : ∀ z z', g z' w - g z w ≤ c := by
        intro z z'
        have := hdiff (Fin.cons z w) 0 z'
        rw [Fin.update_cons_zero] at this
        exact (abs_le.mp this).2
      have hh := hoeff_step ν (fun z => g z w) (hgz w) c B hc (fun z => hgB z w) hosc t
      have : ∀ z, Real.exp (t * (g z w - m)) =
          Real.exp (t * (hw w - m)) * Real.exp (t * (g z w - ∫ z', g z' w ∂ν)) := by
        intro z; rw [← Real.exp_add]; congr 1; simp only [hw]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    calc ∫ S, Real.exp (t * (f S - m)) ∂(Measure.pi fun _ => ν)
        = ∫ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ∂(Measure.pi fun _ => ν) := by
          rw [← hmps.integral_comp' (g := fun S => Real.exp (t * (f S - m)))]
          simp_rw [hge]
          rw [integral_prod_symm _ hint_e]
      _ ≤ ∫ w, Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2)
            ∂(Measure.pi fun _ => ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            integral_nonneg fun z => (Real.exp_pos _).le) ?_ (Filter.Eventually.of_forall hstep)
          refine Integrable.mul_const ?_ _
          refine int_of_bdd _ _ (Real.measurable_exp.comp
            (measurable_const.mul (hwm.sub measurable_const))) (Real.exp (|t| * (B + |m|))) fun w => ?_
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have h1 := hwB w
          calc t * (hw w - m) ≤ |t * (hw w - m)| := le_abs_self _
            _ = |t| * |hw w - m| := abs_mul _ _
            _ ≤ |t| * (B + |m|) := by
              gcongr
              calc |hw w - m| ≤ |hw w| + |m| := abs_sub _ _
                _ ≤ B + |m| := by linarith
      _ = (∫ w, Real.exp (t * (hw w - ∫ w', hw w' ∂(Measure.pi fun _ => ν)))
            ∂(Measure.pi fun _ => ν)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
          rw [integral_mul_const, ← hmean]
      _ ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) * Real.exp (c ^ 2 / 8 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hih (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * c ^ 2 / 8 * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring


lemma per_coord {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {m : ℕ} (ψ : (Fin (m + 1) → Z) → Z → ℝ) (hψm : Measurable (Function.uncurry ψ))
    (M γ : ℝ) (hψ0 : ∀ S z, 0 ≤ ψ S z) (hψM : ∀ S z, ψ S z ≤ M)
    (hγ : ∀ S i z' z, |ψ (Function.update S i z') z - ψ S z| ≤ γ) (i : Fin (m + 1)) :
    |∫ S, (∫ z, ψ S z ∂μ - ψ S (S i)) ∂(Measure.pi fun _ => μ)| ≤ γ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Z) i with he
  have hmp : MeasurePreserving e (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
  have hmps := hmp.symm e
  have hsymm : ∀ p : Z × (Fin m → Z), e.symm p = Fin.insertNth (α := fun _ => Z) i p.1 p.2 := by
    intro p; simp [e]; try rfl
  have hins : Measurable fun p : Z × (Fin m → Z) => Fin.insertNth (α := fun _ => Z) i p.1 p.2 := by
    have := e.symm.measurable
    have heq : (⇑e.symm) = fun p : Z × (Fin m → Z) => Fin.insertNth (α := fun _ => Z) i p.1 p.2 := funext hsymm
    rwa [heq] at this
  have hψS : ∀ S, Measurable (ψ S) := fun S => hψm.comp (measurable_const.prodMk measurable_id)
  have hψb : ∀ S z, |ψ S z| ≤ M := fun S z => by rw [abs_of_nonneg (hψ0 S z)]; exact hψM S z
  have hint : ∀ S, Integrable (ψ S) μ := fun S => int_of_bdd μ _ (hψS S) M (hψb S)
  have hIb : ∀ S, ∫ z, ψ S z ∂μ ∈ Set.Icc 0 M := fun S =>
    ⟨integral_nonneg (hψ0 S), (le_abs_self _).trans (abs_integral_le_of_bdd μ _ M (hψb S))⟩
  set G : (Fin (m + 1) → Z) → ℝ := fun S => ∫ z, ψ S z ∂μ - ψ S (S i) with hG
  have hGm : Measurable G :=
    (StronglyMeasurable.integral_prod_right (ν := μ) hψm.stronglyMeasurable).measurable.sub
      (hψm.comp (measurable_id.prodMk (measurable_pi_apply i)))
  have hGb : ∀ S, |G S| ≤ M := by
    intro S
    have := hIb S
    rw [abs_le]; constructor <;> simp only [G] <;> linarith [hψ0 S (S i), hψM S (S i), this.1, this.2]
  have hintG : Integrable (fun p : Z × (Fin m → Z) => G (Fin.insertNth (α := fun _ => Z) i p.1 p.2))
      (μ.prod (Measure.pi fun _ => μ)) :=
    int_of_bdd _ _ (hGm.comp hins) M fun p => hGb _
  rw [← hmps.integral_comp' (g := G)]
  simp_rw [hsymm]
  rw [integral_prod_symm _ hintG]
  refine abs_integral_le_of_bdd _ _ γ fun w => ?_
  have hx : Measurable fun x : Z => Fin.insertNth (α := fun _ => Z) i x w :=
    hins.comp (measurable_id.prodMk measurable_const)
  have hbm : Measurable fun x : Z => ψ (Fin.insertNth (α := fun _ => Z) i x w) x :=
    hψm.comp (hx.prodMk measurable_id)
  have ham2 : Measurable (Function.uncurry fun (x : Z) (z : Z) => ψ (Fin.insertNth (α := fun _ => Z) i x w) z) :=
    hψm.comp ((hx.comp measurable_fst).prodMk measurable_snd)
  have ham : Measurable fun x : Z => ∫ z, ψ (Fin.insertNth (α := fun _ => Z) i x w) z ∂μ :=
    (StronglyMeasurable.integral_prod_right (ν := μ) ham2.stronglyMeasurable).measurable
  have hinta : Integrable (fun x : Z => ∫ z, ψ (Fin.insertNth (α := fun _ => Z) i x w) z ∂μ) μ :=
    int_of_bdd μ _ ham M fun x => abs_integral_le_of_bdd μ _ M (hψb _)
  have hintb : Integrable (fun x : Z => ψ (Fin.insertNth (α := fun _ => Z) i x w) x) μ :=
    int_of_bdd μ _ hbm M fun x => hψb _ _
  have e1 : ∫ x, G (Fin.insertNth (α := fun _ => Z) i x w) ∂μ =
      ∫ x, (∫ z, ψ (Fin.insertNth (α := fun _ => Z) i x w) z ∂μ - ∫ z, ψ (Fin.insertNth (α := fun _ => Z) i z w) z ∂μ) ∂μ := by
    simp only [G, Fin.insertNth_apply_same]
    rw [integral_sub hinta hintb, integral_sub hinta (integrable_const _), integral_const]
    simp
  rw [e1]
  refine abs_integral_le_of_bdd _ _ γ fun x => ?_
  rw [← integral_sub (hint _) hintb]
  refine abs_integral_le_of_bdd _ _ γ fun z => ?_
  have := hγ (Fin.insertNth (α := fun _ => Z) i x w) i z z
  rw [Fin.update_insertNth, abs_sub_comm] at this
  exact this

theorem abs_tail {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (ψ : (Fin n → Z) → Z → ℝ) (hψm : Measurable (Function.uncurry ψ))
    (M γ : ℝ) (hψ0 : ∀ S z, 0 ≤ ψ S z) (hψM : ∀ S z, ψ S z ≤ M)
    (hγ : ∀ S i z' z, |ψ (Function.update S i z') z - ψ S z| ≤ γ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | γ + (2 * n * γ + M) * Real.sqrt (Real.log (2 / δ) / (2 * n)) <
        |∫ z, ψ S z ∂μ - (1 / (n : ℝ)) * ∑ i, ψ S (S i)|} ≤ ENNReal.ofReal δ := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hZ : Nonempty Z := nonempty_of_isProbabilityMeasure μ
  obtain ⟨z0⟩ := hZ
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans (hγ (fun _ => z0) ⟨0, hn⟩ z0 z0)
  have hM0 : 0 ≤ M := (hψ0 (fun _ => z0) z0).trans (hψM _ _)
  have hψS : ∀ S, Measurable (ψ S) := fun S => hψm.comp (measurable_const.prodMk measurable_id)
  have hψb : ∀ S z, |ψ S z| ≤ M := fun S z => by rw [abs_of_nonneg (hψ0 S z)]; exact hψM S z
  have hint : ∀ S, Integrable (ψ S) μ := fun S => int_of_bdd μ _ (hψS S) M (hψb S)
  have hIb : ∀ S, ∫ z, ψ S z ∂μ ∈ Set.Icc 0 M := fun S =>
    ⟨integral_nonneg (hψ0 S), (le_abs_self _).trans (abs_integral_le_of_bdd μ _ M (hψb S))⟩
  have havg : ∀ S, (1 / (n : ℝ)) * ∑ i, ψ S (S i) ∈ Set.Icc 0 M := by
    intro S
    have h1 : 0 ≤ ∑ i, ψ S (S i) := Finset.sum_nonneg fun i _ => hψ0 S (S i)
    have h2 : ∑ i, ψ S (S i) ≤ n * M := by
      calc ∑ i, ψ S (S i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψM S (S i)
        _ = n * M := by simp
    constructor
    · positivity
    · rw [one_div, inv_mul_le_iff₀ hnpos]; exact h2
  set f : (Fin n → Z) → ℝ := fun S => ∫ z, ψ S z ∂μ - (1 / (n : ℝ)) * ∑ i, ψ S (S i) with hf
  have hfB : ∀ S, |f S| ≤ M := by
    intro S
    have a := hIb S; have b := havg S
    rw [abs_le]; constructor <;> simp only [f] <;> linarith [a.1, a.2, b.1, b.2]
  have hfm : Measurable f :=
    (StronglyMeasurable.integral_prod_right (ν := μ) hψm.stronglyMeasurable).measurable.sub
      (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        hψm.comp (measurable_id.prodMk (measurable_pi_apply i))))
  set c := 2 * γ + M / n with hc
  have hc0 : 0 ≤ c := by positivity
  have hfdiff : ∀ S i z', |f (Function.update S i z') - f S| ≤ c := by
    intro S i z'
    set S' := Function.update S i z'
    have e : f S' - f S = (∫ z, (ψ S' z - ψ S z) ∂μ) -
        (1 / (n : ℝ)) * ∑ j, (ψ S' (S' j) - ψ S (S j)) := by
      simp only [f]; rw [integral_sub (hint _) (hint _), Finset.sum_sub_distrib]; ring
    have p1 : |∫ z, (ψ S' z - ψ S z) ∂μ| ≤ γ := abs_integral_le_of_bdd μ _ γ fun z => hγ S i z' z
    have p2 : ∀ j, |ψ S' (S' j) - ψ S (S j)| ≤ γ + (if j = i then M else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [S', Function.update_self, if_true]
        have a1 := hγ S j z' z'
        have a2 := hψ0 S z'; have a3 := hψM S z'; have a4 := hψ0 S (S j); have a5 := hψM S (S j)
        rw [abs_le] at a1 ⊢; constructor <;> linarith [a1.1, a1.2]
      · simp only [S', Function.update_of_ne hj, if_neg hj, add_zero]
        exact hγ S i z' (S j)
    have p3 : |∑ j, (ψ S' (S' j) - ψ S (S j))| ≤ n * γ + M := by
      calc |∑ j, (ψ S' (S' j) - ψ S (S j))| ≤ ∑ j, |ψ S' (S' j) - ψ S (S j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (γ + (if j = i then M else 0)) := Finset.sum_le_sum fun j _ => p2 j
        _ = n * γ + M := by rw [Finset.sum_add_distrib]; simp
    rw [e]
    calc |(∫ z, (ψ S' z - ψ S z) ∂μ) - (1 / (n : ℝ)) * ∑ j, (ψ S' (S' j) - ψ S (S j))|
        ≤ |∫ z, (ψ S' z - ψ S z) ∂μ| + |(1 / (n : ℝ)) * ∑ j, (ψ S' (S' j) - ψ S (S j))| :=
          abs_sub _ _
      _ ≤ γ + (1 / (n : ℝ)) * (n * γ + M) := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
          gcongr
      _ = c := by simp only [c]; field_simp; ring
  -- the mean
  have hEf : |∫ S, f S ∂(Measure.pi fun _ => μ)| ≤ γ := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hfeq : f = fun S => (1 / ((m + 1 : ℕ) : ℝ)) * ∑ i, (∫ z, ψ S z ∂μ - ψ S (S i)) := by
      funext S
      simp only [f]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [hfeq, integral_const_mul]
    have hGint : ∀ i : Fin (m + 1), Integrable (fun S => ∫ z, ψ S z ∂μ - ψ S (S i))
        (Measure.pi fun _ => μ) := by
      intro i
      refine int_of_bdd _ _ ((StronglyMeasurable.integral_prod_right (ν := μ)
        hψm.stronglyMeasurable).measurable.sub
        (hψm.comp (measurable_id.prodMk (measurable_pi_apply i)))) M fun S => ?_
      have := hIb S
      rw [abs_le]; constructor <;> linarith [hψ0 S (S i), hψM S (S i), this.1, this.2]
    rw [integral_finsetSum _ fun i _ => hGint i, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 1 / ((m + 1 : ℕ) : ℝ))]
    calc 1 / ((m + 1 : ℕ) : ℝ) * |∑ i, ∫ S, (∫ z, ψ S z ∂μ - ψ S (S i)) ∂(Measure.pi fun _ => μ)|
        ≤ 1 / ((m + 1 : ℕ) : ℝ) * ∑ _i : Fin (m + 1), γ := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => per_coord μ ψ hψm M γ hψ0 hψM hγ i)
      _ = γ := by simp; field_simp
  -- the tail
  set L := Real.log (2 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set ε := (2 * n * γ + M) * Real.sqrt (L / (2 * n)) with hε
  have hε0 : 0 ≤ ε := by positivity
  rcases eq_or_lt_of_le hc0 with hc0' | hcpos
  · -- degenerate case: everything vanishes
    have hγz : γ = 0 := by
      have : 0 ≤ M / n := by positivity
      linarith
    have hMz : M = 0 := by
      have : M / n = 0 := by linarith
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h hnpos.ne'
    have hψz : ∀ S z, ψ S z = 0 := fun S z => le_antisymm (hMz ▸ hψM S z) (hψ0 S z)
    have : {S : Fin n → Z | γ + (2 * n * γ + M) * Real.sqrt (Real.log (2 / δ) / (2 * n)) <
        |∫ z, ψ S z ∂μ - (1 / (n : ℝ)) * ∑ i, ψ S (S i)|} = ∅ := by
      ext S; simp [hψz, hγz, hMz]
    rw [this, measure_empty]; exact bot_le
  · set π := Measure.pi fun _ : Fin n => μ with hπ
    set cc : NNReal := ⟨n * c ^ 2 / 4, by positivity⟩ with hcc
    have hccr : (cc : ℝ) = n * c ^ 2 / 4 := rfl
    set X : (Fin n → Z) → ℝ := fun S => f S - ∫ S', f S' ∂π with hX
    have hEfM : |∫ S', f S' ∂π| ≤ M := abs_integral_le_of_bdd π _ M hfB
    have hXm : Measurable X := hfm.sub measurable_const
    have hsg : HasSubgaussianMGF X cc π := by
      constructor
      · intro t
        refine int_of_bdd π _ (Real.measurable_exp.comp (measurable_const.mul hXm))
          (Real.exp (|t| * (2 * M))) fun S => ?_
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hfB S
        calc t * X S ≤ |t * X S| := le_abs_self _
          _ = |t| * |X S| := abs_mul _ _
          _ ≤ |t| * (2 * M) := by
            gcongr
            calc |X S| ≤ |f S| + |∫ S', f S' ∂π| := abs_sub _ _
              _ ≤ 2 * M := by linarith
      · intro t
        have := mcd_mgf μ c M hc0 n f hfm hfB hfdiff t
        unfold mgf
        calc ∫ S, Real.exp (t * X S) ∂π ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := this
          _ = Real.exp (cc * t ^ 2 / 2) := by
            congr 1; rw [hccr]; ring
    have hexp : Real.exp (-ε ^ 2 / (2 * cc)) = δ / 2 := by
      have hsq : ε ^ 2 = (n * c) ^ 2 * (L / (2 * n)) := by
        rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
        congr 1; simp only [c]; field_simp
      have : -ε ^ 2 / (2 * (cc : ℝ)) = -L := by
        rw [hsq, hccr]; field_simp; try ring
      rw [this, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have t1 := hsg.measure_ge_le hε0
    have t2 := hsg.neg.measure_ge_le hε0
    rw [hexp] at t1 t2
    have hsub : {S : Fin n → Z | γ + (2 * n * γ + M) * Real.sqrt (Real.log (2 / δ) / (2 * n)) <
        |∫ z, ψ S z ∂μ - (1 / (n : ℝ)) * ∑ i, ψ S (S i)|} ⊆
        {S | ε ≤ X S} ∪ {S | ε ≤ (-X) S} := by
      intro S hS
      simp only [Set.mem_setOf_eq] at hS
      change γ + ε < |f S| at hS
      have : |f S| ≤ |X S| + γ := by
        calc |f S| = |X S + ∫ S', f S' ∂π| := by simp only [X]; ring_nf
          _ ≤ |X S| + |∫ S', f S' ∂π| := abs_add_le _ _
          _ ≤ |X S| + γ := by linarith
      have hlt : ε < |X S| := by linarith
      rcases lt_abs.mp hlt with h | h
      · left; exact h.le
      · right; simp only [Set.mem_setOf_eq, Pi.neg_apply]; exact h.le
    calc π _ ≤ π ({S | ε ≤ X S} ∪ {S | ε ≤ (-X) S}) := measure_mono hsub
      _ ≤ π {S | ε ≤ X S} + π {S | ε ≤ (-X) S} := measure_union_le _ _
      _ = ENNReal.ofReal (π.real {S | ε ≤ X S}) + ENNReal.ofReal (π.real {S | ε ≤ (-X) S}) := by
          rw [ofReal_measureReal, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
          gcongr
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring


open FoundationsML.Stability BigDataNV.Reg

lemma nvCost_eq (b h q d : ℝ) :
    nvCost b h q d = b * max (d - q) 0 + h * max (q - d) 0 := by
  simp only [nvCost, InventoryControl.newsboyLoss]
  ring

lemma nvCost_nonneg (b h q d : ℝ) (hb : 0 < b) (hh : 0 < h) : 0 ≤ nvCost b h q d := by
  rw [nvCost_eq]
  have h1 : 0 ≤ max (d - q) 0 := le_max_right _ _
  have h2 : 0 ≤ max (q - d) 0 := le_max_right _ _
  positivity

lemma nvCost_le (b h Dbar q d : ℝ) (hb : 0 < b) (hh : 0 < h) (hq : q ∈ Set.Icc 0 Dbar)
    (hd : d ∈ Set.Icc 0 Dbar) : nvCost b h q d ≤ max b h * Dbar := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hd0, hd1⟩ := hd
  have hbm : b ≤ max b h := le_max_left _ _
  have hhm : h ≤ max b h := le_max_right _ _
  rw [nvCost_eq]
  rcases le_total q d with hqd | hqd
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ d - q), max_eq_right (by linarith : q - d ≤ 0)]
    nlinarith
  · rw [max_eq_right (by linarith : d - q ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ q - d)]
    nlinarith

lemma nvCost_lip (b h u v d : ℝ) (hb : 0 < b) (hh : 0 < h) :
    |nvCost b h u d - nvCost b h v d| ≤ max b h * |u - v| := by
  have hbm : b ≤ max b h := le_max_left _ _
  have hhm : h ≤ max b h := le_max_right _ _
  rw [nvCost_eq, nvCost_eq]
  rcases le_total u d with hud | hud <;> rcases le_total v d with hvd | hvd
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ d - u), max_eq_right (by linarith : u - d ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ d - v), max_eq_right (by linarith : v - d ≤ 0)]
    rw [abs_le]
    rcases le_total u v with huv | huv
    · rw [abs_of_nonpos (by linarith)]; constructor <;> nlinarith
    · rw [abs_of_nonneg (by linarith)]; constructor <;> nlinarith
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ d - u), max_eq_right (by linarith : u - d ≤ 0),
      max_eq_right (by linarith : d - v ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ v - d)]
    rw [abs_le, abs_of_nonpos (by linarith : u - v ≤ 0)]; constructor <;> nlinarith
  · rw [max_eq_right (by linarith : d - u ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ u - d),
      max_eq_left (by linarith : (0:ℝ) ≤ d - v), max_eq_right (by linarith : v - d ≤ 0)]
    rw [abs_le, abs_of_nonneg (by linarith : 0 ≤ u - v)]; constructor <;> nlinarith
  · rw [max_eq_right (by linarith : d - u ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ u - d),
      max_eq_right (by linarith : d - v ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ v - d)]
    rw [abs_le]
    rcases le_total u v with huv | huv
    · rw [abs_of_nonpos (by linarith)]; constructor <;> nlinarith
    · rw [abs_of_nonneg (by linarith)]; constructor <;> nlinarith

lemma max0_conv (a a' t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max (a + t * (a' - a)) 0 ≤ (1 - t) * max a 0 + t * max a' 0 := by
  have h1 : a ≤ max a 0 := le_max_left _ _
  have h2 : a' ≤ max a' 0 := le_max_left _ _
  have h3 : 0 ≤ max a 0 := le_max_right _ _
  have h4 : 0 ≤ max a' 0 := le_max_right _ _
  apply max_le
  · nlinarith
  · nlinarith

lemma nvCost_conv (b h u v d t : ℝ) (hb : 0 < b) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    nvCost b h (u + t * (v - u)) d ≤ (1 - t) * nvCost b h u d + t * nvCost b h v d := by
  rw [nvCost_eq, nvCost_eq, nvCost_eq]
  have e1 : d - (u + t * (v - u)) = (d - u) + t * ((d - v) - (d - u)) := by ring
  have e2 : u + t * (v - u) - d = (u - d) + t * ((v - d) - (u - d)) := by ring
  rw [e1, e2]
  have c1 := max0_conv (d - u) (d - v) t ht0 ht1
  have c2 := max0_conv (u - d) (v - d) t ht0 ht1
  nlinarith

/-- the loss of a linear rule -/
noncomputable def ell {p : ℕ} (b h : ℝ) (q : EuclideanSpace ℝ (Fin p))
    (z : EuclideanSpace ℝ (Fin p) × ℝ) : ℝ :=
  nvCost b h (inner ℝ q z.1) z.2

lemma obj_eq {p n : ℕ} (b h lam : ℝ) (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ)
    (q : EuclideanSpace ℝ (Fin p)) :
    nvRegObjective b h lam S q = (1 / (n : ℝ)) * ∑ i, ell b h q (S i) + lam * ‖q‖ ^ 2 := rfl

lemma ell_lip {p : ℕ} (b h X : ℝ) (hb : 0 < b) (hh : 0 < h) (q q' : EuclideanSpace ℝ (Fin p))
    (z : EuclideanSpace ℝ (Fin p) × ℝ) (hz : ‖z.1‖ ≤ X) :
    |ell b h q z - ell b h q' z| ≤ max b h * X * ‖q - q'‖ := by
  unfold ell
  refine (nvCost_lip b h _ _ _ hb hh).trans ?_
  rw [← inner_sub_left]
  have h1 := abs_real_inner_le_norm (q - q') z.1
  have hK : 0 ≤ max b h := le_trans hb.le (le_max_left _ _)
  calc max b h * |inner ℝ (q - q') z.1| ≤ max b h * (‖q - q'‖ * ‖z.1‖) :=
        mul_le_mul_of_nonneg_left h1 hK
    _ ≤ max b h * (‖q - q'‖ * X) := by gcongr
    _ = max b h * X * ‖q - q'‖ := by ring

/-- strong convexity at a minimiser -/
lemma strong_min {p n : ℕ} (b h lam : ℝ) (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (q : EuclideanSpace ℝ (Fin p))
    (hq : IsNVRegSolution b h lam S q) (y : EuclideanSpace ℝ (Fin p)) :
    nvRegObjective b h lam S q + lam * ‖y - q‖ ^ 2 ≤ nvRegObjective b h lam S y := by
  set L : EuclideanSpace ℝ (Fin p) → ℝ := fun g => (1 / (n : ℝ)) * ∑ i, ell b h g (S i) with hL
  have hF : ∀ g, nvRegObjective b h lam S g = L g + lam * ‖g‖ ^ 2 := fun g => obj_eq b h lam S g
  set D := ‖y - q‖ ^ 2 with hD
  set P := inner ℝ q (y - q) with hP
  have hy : ‖y‖ ^ 2 = ‖q‖ ^ 2 + 2 * P + D := by
    have : y = q + (y - q) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  have hconvL : ∀ t, 0 ≤ t → t ≤ 1 → L (q + t • (y - q)) ≤ (1 - t) * L q + t * L y := by
    intro t ht0 ht1
    simp only [hL]
    have hn : 0 ≤ 1 / (n : ℝ) := by positivity
    have : ∀ i, ell b h (q + t • (y - q)) (S i) ≤ (1 - t) * ell b h q (S i) + t * ell b h y (S i) := by
      intro i
      unfold ell
      have : inner ℝ (q + t • (y - q)) (S i).1 =
          inner ℝ q (S i).1 + t * (inner ℝ y (S i).1 - inner ℝ q (S i).1) := by
        rw [inner_add_left, real_inner_smul_left, inner_sub_left]
      rw [this]
      exact nvCost_conv b h _ _ _ t hb hh ht0 ht1
    calc 1 / (n : ℝ) * ∑ i, ell b h (q + t • (y - q)) (S i)
        ≤ 1 / (n : ℝ) * ∑ i, ((1 - t) * ell b h q (S i) + t * ell b h y (S i)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => this i) hn
      _ = (1 - t) * (1 / (n : ℝ) * ∑ i, ell b h q (S i)) +
            t * (1 / (n : ℝ) * ∑ i, ell b h y (S i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  have hnorm : ∀ t : ℝ, ‖q + t • (y - q)‖ ^ 2 = ‖q‖ ^ 2 + 2 * t * P + t ^ 2 * D := by
    intro t
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have key : ∀ t, 0 < t → t ≤ 1 → -(lam * t * D) ≤ L y - L q + 2 * lam * P := by
    intro t ht0 ht1
    have h1 := hq (q + t • (y - q))
    rw [hF, hF, hnorm] at h1
    have h2 := hconvL t ht0.le ht1
    have h3 : t * (L q) ≤ t * (L y + 2 * lam * P + lam * t * D) := by nlinarith
    have h4 := le_of_mul_le_mul_left h3 ht0
    linarith
  have hD0 : 0 ≤ D := by positivity
  have hv : 0 ≤ L y - L q + 2 * lam * P := by
    by_contra hv
    push Not at hv
    set v := L y - L q + 2 * lam * P
    set t := min 1 (-v / (lam * D + 1)) with ht
    have hden : 0 < lam * D + 1 := by positivity
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hden)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t * (lam * D + 1) ≤ -v := by
      have := min_le_right 1 (-v / (lam * D + 1))
      rw [← ht] at this
      calc t * (lam * D + 1) ≤ -v / (lam * D + 1) * (lam * D + 1) :=
            mul_le_mul_of_nonneg_right this hden.le
        _ = -v := div_mul_cancel₀ _ hden.ne'
    have := key t ht0 ht1
    nlinarith
  rw [hF, hF, hy]
  nlinarith

/-- uniform stability under replacement of one sample point -/
lemma stab {p n : ℕ} (b h lam X : ℝ) (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ X)
    (hn : 1 ≤ n) (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (i : Fin n)
    (z' : EuclideanSpace ℝ (Fin p) × ℝ) (hS : ∀ j, ‖(S j).1‖ ≤ X) (hz' : ‖z'.1‖ ≤ X)
    (q q' : EuclideanSpace ℝ (Fin p)) (hq : IsNVRegSolution b h lam S q)
    (hq' : IsNVRegSolution b h lam (Function.update S i z') q')
    (w : EuclideanSpace ℝ (Fin p) × ℝ) (hw : ‖w.1‖ ≤ X) :
    |ell b h q w - ell b h q' w| ≤ (max b h) ^ 2 * X ^ 2 / ((n : ℝ) * lam) := by
  set K := max b h
  have hK : 0 < K := lt_of_lt_of_le hb (le_max_left _ _)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set D := ‖q - q'‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have s1 := strong_min b h lam hb hh hlam S q hq q'
  have s2 := strong_min b h lam hb hh hlam (Function.update S i z') q' hq' q
  have hdiffobj : ∀ g, nvRegObjective b h lam S g - nvRegObjective b h lam (Function.update S i z') g
      = (1 / (n : ℝ)) * (ell b h g (S i) - ell b h g z') := by
    intro g
    rw [obj_eq, obj_eq]
    have hs1 := Finset.add_sum_erase Finset.univ (fun j => ell b h g (S j)) (Finset.mem_univ i)
    have hs2 := Finset.add_sum_erase Finset.univ (fun j => ell b h g (Function.update S i z' j))
      (Finset.mem_univ i)
    have hs3 : ∑ j ∈ Finset.univ.erase i, ell b h g (Function.update S i z' j) =
        ∑ j ∈ Finset.univ.erase i, ell b h g (S j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp only [Function.update_self] at hs2
    rw [← hs1, ← hs2, hs3]
    ring
  have hq'q : ‖q' - q‖ = D := by rw [norm_sub_rev]
  rw [hq'q] at s1
  have l1 := ell_lip b h X hb hh q' q (S i) (hS i)
  have l2 := ell_lip b h X hb hh q q' z' hz'
  rw [norm_sub_rev] at l1
  have hsum : 2 * lam * D ^ 2 ≤ (1 / (n : ℝ)) * (2 * K * X * D) := by
    have e1 := hdiffobj q
    have e2 := hdiffobj q'
    have a1 := (abs_le.mp l1).2
    have a2 := (abs_le.mp l2).2
    have hn' : 0 ≤ 1 / (n : ℝ) := by positivity
    have : (1 / (n : ℝ)) * (ell b h q' (S i) - ell b h q' z' - (ell b h q (S i) - ell b h q z'))
        ≤ (1 / (n : ℝ)) * (2 * K * X * D) := by
      apply mul_le_mul_of_nonneg_left _ hn'; linarith
    nlinarith
  have hDbound : D ≤ K * X / ((n : ℝ) * lam) := by
    rw [le_div_iff₀ (by positivity)]
    rcases eq_or_lt_of_le hD0 with h0 | h0
    · rw [← h0]; simp; positivity
    · have : 2 * lam * D ^ 2 * n ≤ 2 * K * X * D := by
        have := mul_le_mul_of_nonneg_right hsum hnpos.le
        rw [show (1 / (n:ℝ)) * (2 * K * X * D) * n = 2 * K * X * D by field_simp] at this
        linarith
      nlinarith
  have l3 := ell_lip b h X hb hh q q' w hw
  calc |ell b h q w - ell b h q' w| ≤ K * X * D := l3
    _ ≤ K * X * (K * X / ((n : ℝ) * lam)) := by
        apply mul_le_mul_of_nonneg_left hDbound; positivity
    _ = K ^ 2 * X ^ 2 / ((n : ℝ) * lam) := by ring

end P82cd

open MeasureTheory FoundationsML.Stability BigDataNV.Reg in
theorem solution {p n : ℕ} (b h lam Xmax Dbar : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax) (hD : 0 ≤ Dbar)
    (Xdom : Set (EuclideanSpace ℝ (Fin p))) (hXdom : ∀ x ∈ Xdom, ‖x‖ ^ 2 ≤ Xmax ^ 2)
    (μ : Measure (EuclideanSpace ℝ (Fin p) × ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (dataSupport Xdom Dbar)ᶜ = 0)
    (qhat : (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) → EuclideanSpace ℝ (Fin p))
    (hqhat : ∀ S, IsNVRegSolution b h lam S (qhat S))
    (hrange : ∀ S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ, (∀ j, S j ∈ dataSupport Xdom Dbar) →
      ∀ x ∈ Xdom, inner ℝ (qhat S) x ∈ Set.Icc 0 Dbar)
    (hmeas : Measurable qhat)
    (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => μ)
      {S | (max b h) ^ 2 * Xmax ^ 2 / ((n : ℝ) * lam) +
          (2 * (max b h) ^ 2 * Xmax ^ 2 / lam + max b h * Dbar) *
            Real.sqrt (Real.log (2 / δ) / (2 * (n : ℝ))) <
        |GeneralizationError μ (nvCost b h) (linEval (qhat S)) -
          EmpiricalError (nvCost b h) S (linEval (qhat S))|} ≤ ENNReal.ofReal δ := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set Z1 : Set (EuclideanSpace ℝ (Fin p) × ℝ) := (toMeasurable μ (dataSupport Xdom Dbar)ᶜ)ᶜ with hZ1
  have hZ1m : MeasurableSet Z1 := (measurableSet_toMeasurable _ _).compl
  have hZ1sub : Z1 ⊆ dataSupport Xdom Dbar := by
    intro z hz
    by_contra hc
    exact hz (subset_toMeasurable _ _ hc)
  have hZ1null : μ Z1ᶜ = 0 := by
    rw [hZ1, compl_compl, measure_toMeasurable, hμ]
  have hZ1ae : ∀ᵐ z ∂μ, z ∈ Z1 := mem_ae_iff.2 hZ1null
  obtain ⟨z0, hz0⟩ := hZ1ae.exists
  set π : EuclideanSpace ℝ (Fin p) × ℝ → EuclideanSpace ℝ (Fin p) × ℝ :=
    fun z => if z ∈ Z1 then z else z0 with hπ
  have hπm : Measurable π := Measurable.ite hZ1m measurable_id measurable_const
  have hπZ1 : ∀ z, π z ∈ Z1 := by
    intro z; by_cases hz : z ∈ Z1
    · simp only [π, if_pos hz]; exact hz
    · simp only [π, if_neg hz]; exact hz0
  have hπid : ∀ z ∈ Z1, π z = z := by intro z hz; simp only [π, if_pos hz]
  set P : (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) → (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) :=
    fun S j => π (S j) with hP
  have hPm : Measurable P := measurable_pi_lambda _ fun j => hπm.comp (measurable_pi_apply j)
  have hPupd : ∀ S i z', P (Function.update S i z') = Function.update (P S) i (π z') := by
    intro S i z'
    funext j
    by_cases hj : j = i
    · subst hj; simp [P]
    · simp [P, Function.update_of_ne hj]
  have hnorm : ∀ z ∈ Z1, ‖z.1‖ ≤ Xmax := by
    intro z hz
    have h1 := hXdom z.1 (Set.mem_prod.mp (hZ1sub hz)).1
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg z.1]
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin p) × (EuclideanSpace ℝ (Fin p) × ℝ) =>
      P82cd.ell b h x.1 x.2 := by
    unfold P82cd.ell nvCost InventoryControl.newsboyLoss
    fun_prop
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) → EuclideanSpace ℝ (Fin p) × ℝ → ℝ,
      ψ = fun S z => P82cd.ell b h (qhat (P S)) (π z) := ⟨_, rfl⟩
  have hψapp : ∀ S z, ψ S z = P82cd.ell b h (qhat (P S)) (π z) := fun S z => by rw [hψ]
  have hψm : Measurable (Function.uncurry ψ) := by
    have e : Function.uncurry ψ = (fun x : EuclideanSpace ℝ (Fin p) × (EuclideanSpace ℝ (Fin p) × ℝ) =>
        P82cd.ell b h x.1 x.2) ∘ (fun q : (Fin n → EuclideanSpace ℝ (Fin p) × ℝ) ×
          (EuclideanSpace ℝ (Fin p) × ℝ) => (qhat (P q.1), π q.2)) := by
      funext q; simp only [Function.uncurry, Function.comp, hψapp]
    rw [e]
    exact hcont.measurable.comp ((hmeas.comp (hPm.comp measurable_fst)).prodMk
      (hπm.comp measurable_snd))
  have hψ0 : ∀ S z, 0 ≤ ψ S z := by
    intro S z
    rw [hψapp]; unfold P82cd.ell
    exact P82cd.nvCost_nonneg b h (inner ℝ (qhat (P S)) (π z).1) (π z).2 hb hh
  have hψM : ∀ S z, ψ S z ≤ max b h * Dbar := by
    intro S z
    have hz := Set.mem_prod.mp (hZ1sub (hπZ1 z))
    rw [hψapp]; unfold P82cd.ell
    exact P82cd.nvCost_le b h Dbar (inner ℝ (qhat (P S)) (π z).1) (π z).2 hb hh
      (hrange (P S) (fun j => hZ1sub (hπZ1 _)) _ hz.1) hz.2
  have hγ : ∀ S i z' z, |ψ (Function.update S i z') z - ψ S z| ≤
      (max b h) ^ 2 * Xmax ^ 2 / ((n : ℝ) * lam) := by
    intro S i z' z
    rw [hψapp, hψapp, hPupd, abs_sub_comm]
    exact P82cd.stab b h lam Xmax hb hh hlam hX hn (P S) i (π z') (fun j => hnorm _ (hπZ1 _))
      (hnorm _ (hπZ1 z')) (qhat (P S)) (qhat (Function.update (P S) i (π z'))) (hqhat _) (hqhat _)
      (π z) (hnorm _ (hπZ1 z))
  have main := P82cd.abs_tail μ hn ψ hψm (max b h * Dbar) ((max b h) ^ 2 * Xmax ^ 2 / ((n : ℝ) * lam))
    hψ0 hψM hγ δ hδ0 hδ1
  refine le_trans (measure_mono_ae ?_) main
  have hall : ∀ᵐ S ∂(Measure.pi fun _ : Fin n => μ), ∀ j, S j ∈ Z1 :=
    ae_all_iff.2 fun j => (Measure.tendsto_eval_ae_ae (i := j)).eventually hZ1ae
  filter_upwards [hall] with S hS hmem
  change _ < _ at hmem
  change _ < _
  have hPS : P S = S := funext fun j => hπid _ (hS j)
  have hI : ∫ z, ψ S z ∂μ = GeneralizationError μ (nvCost b h) (linEval (qhat S)) := by
    simp only [hψapp, hPS]
    unfold GeneralizationError Loss linEval P82cd.ell
    exact integral_congr_ae (hZ1ae.mono fun z hz => by simp only [hπid z hz])
  have hE : (1 / (n : ℝ)) * ∑ i, ψ S (S i) = EmpiricalError (nvCost b h) S (linEval (qhat S)) := by
    simp only [hψapp, hPS, hπid _ (hS _)]
    rfl
  have h2n : 2 * (n : ℝ) * ((max b h) ^ 2 * Xmax ^ 2 / ((n : ℝ) * lam)) =
      2 * (max b h) ^ 2 * Xmax ^ 2 / lam := by
    field_simp
  rw [hI, hE, h2n]
  exact hmem
