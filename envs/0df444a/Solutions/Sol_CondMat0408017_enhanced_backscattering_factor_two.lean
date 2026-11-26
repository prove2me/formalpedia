-- Prove2me | solution 1 for CondMat0408017.enhanced_backscattering_factor_two
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:36:12.749843+00:00
-- url     : https://prove2.me/submissions/fc7dff89-0e2c-45e2-8c2e-a0209bd705c1

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

private lemma norm_add_sq_complex (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re := by
  have h1 : ‖z + w‖ ^ 2 = Complex.normSq (z + w) := (Complex.normSq_eq_norm_sq (z + w)).symm
  have h2 : ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
  have h3 : ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
  rw [h1, h2, h3]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

private lemma memLp_conj {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℂ} (hf : MemLp f 2 P) : MemLp (fun w => starRingEnd ℂ (f w)) 2 P := by
  refine ⟨(Complex.conjCLE.continuous.comp_aestronglyMeasurable hf.1), ?_⟩
  rw [eLpNorm_congr_norm_ae (g := f) (Filter.Eventually.of_forall (fun w => by simp))]
  exact hf.2

private lemma integral_norm_sq_add_of_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℂ} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (horth : ∫ w, f w * starRingEnd ℂ (g w) ∂P = 0) :
    ∫ w, ‖f w + g w‖ ^ 2 ∂P = (∫ w, ‖f w‖ ^ 2 ∂P) + ∫ w, ‖g w‖ ^ 2 ∂P := by
  have hf2 : Integrable (fun w => ‖f w‖ ^ 2) P := hf.norm.integrable_sq
  have hg2 : Integrable (fun w => ‖g w‖ ^ 2) P := hg.norm.integrable_sq
  have hfg : Integrable (fun w => f w * starRingEnd ℂ (g w)) P :=
    hf.integrable_mul (memLp_conj hg)
  have hre : Integrable (fun w => 2 * (f w * starRingEnd ℂ (g w)).re) P :=
    (Complex.reCLM.integrable_comp hfg).const_mul 2
  have hpoint : (fun w => ‖f w + g w‖ ^ 2) =
      fun w => (‖f w‖ ^ 2 + ‖g w‖ ^ 2) + 2 * (f w * starRingEnd ℂ (g w)).re := by
    ext w
    exact norm_add_sq_complex (f w) (g w)
  have hf2g2 : Integrable (fun w => ‖f w‖ ^ 2 + ‖g w‖ ^ 2) P := hf2.add hg2
  rw [hpoint, integral_add hf2g2 hre, integral_add hf2 hg2, integral_const_mul]
  have hre0 : ∫ w, (f w * starRingEnd ℂ (g w)).re ∂P = 0 := by
    have hcomm := Complex.reCLM.integral_comp_comm hfg
    simpa [horth] using hcomm
  rw [hre0, mul_zero, add_zero]

private lemma memLp_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (F : ι → Ω → ℂ) (hF : ∀ i ∈ s, MemLp (F i) 2 P) :
    MemLp (fun w => ∑ i ∈ s, F i w) 2 P := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.zero
  | @insert a t ha ih =>
    have hFa : MemLp (F a) 2 P := hF a (Finset.mem_insert_self a t)
    have hFt : MemLp (fun w => ∑ i ∈ t, F i w) 2 P :=
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have heq : (fun w => ∑ i ∈ insert a t, F i w) = fun w => F a w + ∑ i ∈ t, F i w := by
      ext w; exact Finset.sum_insert ha
    rw [heq]
    exact hFa.add hFt

private lemma integral_mul_conj_finset_sum_zero {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (f : Ω → ℂ) (F : ι → Ω → ℂ) (hf : MemLp f 2 P)
    (hF : ∀ i ∈ s, MemLp (F i) 2 P)
    (horth : ∀ i ∈ s, ∫ w, f w * starRingEnd ℂ (F i w) ∂P = 0) :
    ∫ w, f w * starRingEnd ℂ (∑ i ∈ s, F i w) ∂P = 0 := by
  have heq : (fun w => f w * starRingEnd ℂ (∑ i ∈ s, F i w)) =
      fun w => ∑ i ∈ s, f w * starRingEnd ℂ (F i w) := by
    ext w
    rw [map_sum, Finset.mul_sum]
  have hint : ∀ i ∈ s, Integrable (fun w => f w * starRingEnd ℂ (F i w)) P :=
    fun i hi => hf.integrable_mul (memLp_conj (hF i hi))
  rw [heq, integral_finsetSum s hint]
  exact Finset.sum_eq_zero horth

private lemma integral_norm_sq_finset_sum_of_orth {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) (F : ι → Ω → ℂ) (hF : ∀ i ∈ s, MemLp (F i) 2 P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ w, F i w * starRingEnd ℂ (F j w) ∂P = 0) :
    ∫ w, ‖∑ i ∈ s, F i w‖ ^ 2 ∂P = ∑ i ∈ s, ∫ w, ‖F i w‖ ^ 2 ∂P := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    have hFa : MemLp (F a) 2 P := hF a (Finset.mem_insert_self a t)
    have hFt_all : ∀ i ∈ t, MemLp (F i) 2 P := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hFt : MemLp (fun w => ∑ i ∈ t, F i w) 2 P := memLp_finset_sum t F hFt_all
    have hsum_orth : ∫ w, F a w * starRingEnd ℂ (∑ i ∈ t, F i w) ∂P = 0 :=
      integral_mul_conj_finset_sum_zero t (F a) F hFa hFt_all (fun i hi =>
        horth a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
    have heq : (fun w => ‖∑ i ∈ insert a t, F i w‖ ^ 2) =
        fun w => ‖F a w + ∑ i ∈ t, F i w‖ ^ 2 := by
      ext w; rw [Finset.sum_insert ha]
    rw [heq, integral_norm_sq_add_of_orth hFa hFt hsum_orth, Finset.sum_insert ha]
    congr 1
    exact ih hFt_all (fun i hi j hj hij =>
      horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {J : Type*} [Fintype J] (Sb Sa : Ω → ℂ) (Ab Bb Aa Ba : J → Ω → ℂ)
    (hS : MemLp Sb 2 P ∧ MemLp Sa 2 P)
    (hA : ∀ j, MemLp (Ab j) 2 P ∧ MemLp (Bb j) 2 P ∧ MemLp (Aa j) 2 P ∧ MemLp (Ba j) 2 P)
    (hrecip : ∀ j, Bb j = Ab j)
    (hincoh : ∀ j, ∫ w, Aa j w * starRingEnd ℂ (Ba j w) ∂P = 0)
    (hpairsb : ∀ i j, i ≠ j →
      ∫ w, (Ab i w + Bb i w) * starRingEnd ℂ (Ab j w + Bb j w) ∂P = 0)
    (hpairsa : ∀ i j, i ≠ j →
      ∫ w, (Aa i w + Ba i w) * starRingEnd ℂ (Aa j w + Ba j w) ∂P = 0)
    (hsingb : ∀ j, ∫ w, Sb w * starRingEnd ℂ (Ab j w + Bb j w) ∂P = 0)
    (hsinga : ∀ j, ∫ w, Sa w * starRingEnd ℂ (Aa j w + Ba j w) ∂P = 0)
    (hsame : ∀ j, ∫ w, ‖Aa j w‖ ^ 2 ∂P = ∫ w, ‖Ab j w‖ ^ 2 ∂P ∧
      ∫ w, ‖Ba j w‖ ^ 2 ∂P = ∫ w, ‖Ab j w‖ ^ 2 ∂P)
    (hsingle : ∫ w, ‖Sa w‖ ^ 2 ∂P = ∫ w, ‖Sb w‖ ^ 2 ∂P)
    (_hmult : 0 < ∑ j, ∫ w, ‖Ab j w‖ ^ 2 ∂P) :
    (∫ w, ‖Sb w‖ ^ 2 ∂P = 0 →
      ∫ w, ‖Sb w + ∑ j, (Ab j w + Bb j w)‖ ^ 2 ∂P =
        2 * ∫ w, ‖Sa w + ∑ j, (Aa j w + Ba j w)‖ ^ 2 ∂P) ∧
    (0 < ∫ w, ‖Sb w‖ ^ 2 ∂P →
      ∫ w, ‖Sb w + ∑ j, (Ab j w + Bb j w)‖ ^ 2 ∂P <
        2 * ∫ w, ‖Sa w + ∑ j, (Aa j w + Ba j w)‖ ^ 2 ∂P) := by
  have hFb_lp : ∀ j ∈ (Finset.univ : Finset J), MemLp (fun w => Ab j w + Bb j w) 2 P :=
    fun j _ => (hA j).1.add (hA j).2.1
  have hFa_lp : ∀ j ∈ (Finset.univ : Finset J), MemLp (fun w => Aa j w + Ba j w) 2 P :=
    fun j _ => (hA j).2.2.1.add (hA j).2.2.2
  have hb_tot : ∫ w, ‖Sb w + ∑ j, (Ab j w + Bb j w)‖ ^ 2 ∂P =
      (∫ w, ‖Sb w‖ ^ 2 ∂P) + 4 * ∑ j, ∫ w, ‖Ab j w‖ ^ 2 ∂P := by
    rw [integral_norm_sq_add_of_orth hS.1 (memLp_finset_sum Finset.univ _ hFb_lp)
      (integral_mul_conj_finset_sum_zero Finset.univ Sb _ hS.1 hFb_lp (fun j _ => hsingb j))]
    rw [integral_norm_sq_finset_sum_of_orth Finset.univ _ hFb_lp (fun i _ j _ hij => hpairsb i j hij)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h2 : (fun w => ‖Ab j w + Bb j w‖ ^ 2) = fun w => 4 * ‖Ab j w‖ ^ 2 := by
      ext w
      rw [hrecip j, ← two_mul, norm_mul, Complex.norm_ofNat, mul_pow]
      norm_num
    rw [h2, integral_const_mul]
  have ha_tot : ∫ w, ‖Sa w + ∑ j, (Aa j w + Ba j w)‖ ^ 2 ∂P =
      (∫ w, ‖Sb w‖ ^ 2 ∂P) + 2 * ∑ j, ∫ w, ‖Ab j w‖ ^ 2 ∂P := by
    rw [integral_norm_sq_add_of_orth hS.2 (memLp_finset_sum Finset.univ _ hFa_lp)
      (integral_mul_conj_finset_sum_zero Finset.univ Sa _ hS.2 hFa_lp (fun j _ => hsinga j))]
    rw [integral_norm_sq_finset_sum_of_orth Finset.univ _ hFa_lp (fun i _ j _ hij => hpairsa i j hij)]
    rw [hsingle]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_norm_sq_add_of_orth (hA j).2.2.1 (hA j).2.2.2 (hincoh j),
      (hsame j).1, (hsame j).2, two_mul]
  rw [hb_tot, ha_tot]
  constructor
  · intro h0; linarith
  · intro hpos; linarith
