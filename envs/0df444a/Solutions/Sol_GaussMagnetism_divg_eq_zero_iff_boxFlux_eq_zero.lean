-- Prove2me | solution 1 for GaussMagnetism.divg_eq_zero_iff_boxFlux_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:47:12.930184+00:00
-- url     : https://prove2.me/submissions/41d8daa1-743e-4f02-9abe-a57654aebe6c

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM GaussMagnetism

namespace LU2GM

open MeasureTheory

abbrev R3 := Fin 3 → ℝ

theorem pos_box (f : R3 → ℝ) (hf : Continuous f) (x : R3) (hx : 0 < f x) :
    ∃ a b : R3, (∀ i, a i < b i) ∧ 0 < ∫ y in Set.Icc a b, f y := by
  have hev : ∀ᶠ y in nhds x, f x / 2 < f y :=
    hf.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨fun i => x i - ε / 2, fun i => x i + ε / 2, fun i => by linarith, ?_⟩
  have hsub : ∀ y ∈ Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤ f y := by
    intro y hy
    apply le_of_lt
    apply hball
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    have h1 := hy.1 i
    have h2 := hy.2 i
    simp only at h1 h2
    constructor <;> linarith
  have hvol : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) := by
    rw [measureReal_def, Real.volume_Icc_pi]
    apply ENNReal.toReal_pos
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    · exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  have hmono : ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤
      ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f y := by
    apply setIntegral_mono_on
    · exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    · exact hf.continuousOn.integrableOn_compact isCompact_Icc
    · exact measurableSet_Icc
    · exact hsub
  rw [setIntegral_const, smul_eq_mul] at hmono
  have : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) * (f x / 2) :=
    mul_pos hvol (by linarith)
  linarith

theorem zero_of_box (f : R3 → ℝ) (hf : Continuous f)
    (h : ∀ a b : R3, (∀ i, a i < b i) → ∫ y in Set.Icc a b, f y = 0) (x : R3) :
    f x = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨a, b, hab, hpos⟩ := pos_box (fun y => -f y) hf.neg x (by linarith)
    rw [integral_neg, h a b hab] at hpos
    simp at hpos
  · obtain ⟨a, b, hab, hpos⟩ := pos_box f hf x hgt
    rw [h a b hab] at hpos
    exact lt_irrefl _ hpos

theorem fin2 (f : (Fin 2 → ℝ) → ℝ) (hf : Continuous f) (c d : Fin 2 → ℝ)
    (h0 : c 0 ≤ d 0) (h1 : c 1 ≤ d 1) :
    ∫ y in Set.Icc c d, f y = ∫ u in c 0..d 0, ∫ w in c 1..d 1, f ![u, w] := by
  set e := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm with he
  have hmp : MeasurePreserving e volume volume := (volume_preserving_finTwoArrow ℝ).symm _
  have hpre : e ⁻¹' Set.Icc c d = Set.Icc (c 0) (d 0) ×ˢ Set.Icc (c 1) (d 1) := by
    ext ⟨u, w⟩
    change (c ≤ ![u, w] ∧ ![u, w] ≤ d) ↔ _
    simp only [Set.mem_prod, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    tauto
  rw [← hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding f _, hpre,
    Measure.volume_eq_prod, setIntegral_prod (fun x => f (e x))
      ((hf.comp e.continuous).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  simp only [intervalIntegral.integral_of_le h0, intervalIntegral.integral_of_le h1,
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  rfl

theorem ins0 (c u w : ℝ) : (0 : Fin 3).insertNth c ![u, w] = ![c, u, w] := by
  ext j; fin_cases j <;> rfl

theorem ins1 (c u w : ℝ) : (1 : Fin 3).insertNth c ![u, w] = ![u, c, w] := by
  ext j; fin_cases j <;> rfl

theorem ins2 (c u w : ℝ) : (2 : Fin 3).insertNth c ![u, w] = ![u, w, c] := by
  ext j; fin_cases j <;> rfl

theorem key (B : Vec → Vec) (hB : ContDiff ℝ 1 B) (a b : Vec) (hab : ∀ i, a i ≤ b i) :
    boxFlux B a b = ∫ p in Set.Icc (EuclideanSpace.equiv (Fin 3) ℝ a)
      (EuclideanSpace.equiv (Fin 3) ℝ b), divg B ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) := by
  set e := EuclideanSpace.equiv (Fin 3) ℝ with he
  set G : R3 → R3 := fun p => e (B (e.symm p)) with hGdef
  have hG : ContDiff ℝ 1 G := e.contDiff.comp (hB.comp e.symm.contDiff)
  have hBd : Differentiable ℝ B := hB.differentiable one_ne_zero
  have hfd : ∀ p v, fderiv ℝ G p v = e (fderiv ℝ B (e.symm p) (e.symm v)) := by
    intro p v
    have h := e.hasFDerivAt.comp p ((hBd (e.symm p)).hasFDerivAt.comp p e.symm.hasFDerivAt)
    rw [show G = e ∘ (B ∘ e.symm) from rfl, h.fderiv]
    rfl
  have hdiv : ∀ p, divg B (e.symm p) = ∑ i, fderiv ℝ G p (Pi.single i 1) i := by
    intro p
    unfold divg Larmor.partialDeriv
    apply Finset.sum_congr rfl
    intro i _
    rw [hfd]
    rfl
  simp_rw [hdiv]
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  rw [MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (e a) (e b) (fun i => hab i)
    G (fderiv ℝ G) ∅ Set.countable_empty hG.continuous.continuousOn
    (fun x _ => (hG.differentiable one_ne_zero x).hasFDerivAt)
    (by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply Continuous.continuousOn
      apply continuous_finset_sum
      intro i _
      exact (continuous_apply i).comp (hcont.clm_apply continuous_const))]
  have hface : ∀ (i : Fin 3) (c : ℝ), Continuous (fun y : Fin 2 → ℝ => G (i.insertNth c y) i) :=
    fun i c => (continuous_apply i).comp (hG.continuous.comp (by fun_prop))
  have hint : ∀ (f : (Fin 2 → ℝ) → ℝ), Continuous f → ∀ c d : Fin 2 → ℝ,
      IntegrableOn f (Set.Icc c d) := fun f hf c d =>
    hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [Fin.sum_univ_three]
  rw [← integral_sub (hint _ (hface 0 _) _ _) (hint _ (hface 0 _) _ _),
    ← integral_sub (hint _ (hface 1 _) _ _) (hint _ (hface 1 _) _ _),
    ← integral_sub (hint _ (hface 2 _) _ _) (hint _ (hface 2 _) _ _)]
  rw [fin2 (fun y => G (Fin.insertNth 0 (e b 0) y) 0 - G (Fin.insertNth 0 (e a 0) y) 0)
      ((hface 0 _).sub (hface 0 _)) _ _ (hab 1) (hab 2),
    fin2 (fun y => G (Fin.insertNth 1 (e b 1) y) 1 - G (Fin.insertNth 1 (e a 1) y) 1)
      ((hface 1 _).sub (hface 1 _)) _ _ (hab 0) (hab 2),
    fin2 (fun y => G (Fin.insertNth 2 (e b 2) y) 2 - G (Fin.insertNth 2 (e a 2) y) 2)
      ((hface 2 _).sub (hface 2 _)) _ _ (hab 0) (hab 1)]
  simp only [ins0, ins1, ins2]
  rfl

end LU2GM

open LU2GM in
theorem solution (B : Vec → Vec) (hB : ContDiff ℝ 1 B) :
    (∀ x, divg B x = 0) ↔
      ∀ a b : Vec, (∀ i, a i < b i) → boxFlux B a b = 0 := by
  set e := EuclideanSpace.equiv (Fin 3) ℝ with he
  constructor
  · intro h a b hab
    rw [key B hB a b (fun i => (hab i).le)]
    simp only [h, MeasureTheory.integral_zero]
  · intro h x
    have hc : Continuous (fun p : R3 => divg B (e.symm p)) := by
      have hdiv : (fun p : R3 => divg B (e.symm p)) = fun p =>
          ∑ i : Fin 3, (e (fderiv ℝ B (e.symm p) (EuclideanSpace.single i 1))) i := by
        funext p
        unfold divg Larmor.partialDeriv
        rfl
      rw [hdiv]
      have hcB : Continuous (fderiv ℝ B) := hB.continuous_fderiv one_ne_zero
      apply continuous_finset_sum
      intro i _
      exact (continuous_apply i).comp (e.continuous.comp
        ((hcB.comp e.symm.continuous).clm_apply continuous_const))
    have := zero_of_box _ hc (fun a' b' hab' => by
      have hk : boxFlux B (e.symm a') (e.symm b') =
          ∫ p in Set.Icc a' b', divg B (e.symm p) :=
        key B hB (e.symm a') (e.symm b') (fun i => (hab' i).le)
      rw [← hk]
      exact h _ _ hab') (e x)
    simpa using this
