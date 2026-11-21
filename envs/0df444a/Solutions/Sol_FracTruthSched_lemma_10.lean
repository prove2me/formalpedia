-- Prove2me | solution 1 for FracTruthSched.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:44:53.843183+00:00
-- url     : https://prove2.me/submissions/1866cdd2-91c9-4db0-8064-f75d674697d8

import Mathlib

section
set_option autoImplicit false

namespace FracTruthSched.Dev.L10

open MeasureTheory

theorem approx (ψ : (Fin 4 → ℝ) → ℝ) (hψ : Continuous ψ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 4) ℝ, ∀ x ∈ Set.Icc (0 : Fin 4 → ℝ) 1,
      |ψ x - MvPolynomial.eval x p| < ε := by
  let K : Set (Fin 4 → ℝ) := Set.Icc 0 1
  have : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let coord : Fin 4 → C(K, ℝ) := fun i => ⟨fun x => x.1 i, (continuous_apply i).comp continuous_subtype_val⟩
  let Φ : MvPolynomial (Fin 4) ℝ →ₐ[ℝ] C(K, ℝ) := MvPolynomial.aeval coord
  have hΦ : ∀ p x, Φ p x = MvPolynomial.eval x.1 p := by
    intro p x
    induction p using MvPolynomial.induction_on with
    | C a => simp [Φ]
    | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, ContinuousMap.mul_apply, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X, Φ]
      rfl
  let A : Subalgebra ℝ C(K, ℝ) := Φ.range
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, x.1 i ≠ y.1 i := by
      by_contra h
      push Not at h
      exact hxy (Subtype.ext (funext h))
    obtain ⟨i, hi⟩ := this
    refine ⟨(coord i : K → ℝ), ⟨coord i, ⟨MvPolynomial.X i, by simp [Φ]⟩, rfl⟩, hi⟩
  have hdense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  let g : C(K, ℝ) := ⟨fun x => ψ x.1, hψ.comp continuous_subtype_val⟩
  have hg : g ∈ A.topologicalClosure := by rw [hdense]; trivial
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hg
  obtain ⟨a, ⟨p, rfl⟩, hd⟩ := hg ε hε
  refine ⟨p, fun x hx => ?_⟩
  have := ContinuousMap.dist_apply_le_dist (f := g) (g := Φ p) ⟨x, hx⟩
  rw [hΦ, Real.dist_eq] at this
  exact lt_of_le_of_lt this hd

theorem poly_moment (f : (Fin 4 → ℝ) → ℝ)
    (hfi : Integrable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hz : ∀ s : Fin 4 → ℕ, ∫ r in Set.Ici (0 : Fin 4 → ℝ),
      f r * ∏ i, Real.exp (-r i) ^ s i = 0)
    (p : MvPolynomial (Fin 4) ℝ) :
    Integrable (fun r => f r * MvPolynomial.eval (fun i => Real.exp (-r i)) p)
        (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) ∧
      ∫ r in Set.Ici (0 : Fin 4 → ℝ),
        f r * MvPolynomial.eval (fun i => Real.exp (-r i)) p = 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hW : ∀ r : Fin 4 → ℝ, MvPolynomial.eval (fun i => Real.exp (-r i))
        (MvPolynomial.monomial u a) = a * ∏ i, Real.exp (-r i) ^ u i := by
      intro r
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp_rw [hW]
    have hint : Integrable (fun r => f r * ∏ i, Real.exp (-r i) ^ u i)
        (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
      refine hfi.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
      have hr' : ∀ i, 0 ≤ r i := fun i => hr i
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => by positivity)]
      refine Finset.prod_le_one (fun i _ => by positivity) fun i _ => ?_
      exact pow_le_one₀ (by positivity) (Real.exp_le_one_iff.mpr (by linarith [hr' i]))
    have heq : ∀ r : Fin 4 → ℝ, f r * (a * ∏ i, Real.exp (-r i) ^ u i)
        = a * (f r * ∏ i, Real.exp (-r i) ^ u i) := fun r => by ring
    simp_rw [heq]
    refine ⟨hint.const_mul a, ?_⟩
    rw [integral_const_mul, hz u, mul_zero]
  | add p q hp hq =>
    simp_rw [map_add, mul_add]
    refine ⟨hp.1.add hq.1, ?_⟩
    rw [integral_add hp.1 hq.1, hp.2, hq.2, add_zero]

theorem bcf_integrable (f : (Fin 4 → ℝ) → ℝ)
    (hfi : Integrable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (ψ : BoundedContinuousFunction (Fin 4 → ℝ) ℝ) :
    Integrable (fun r => f r * ψ (fun i => Real.exp (-r i)))
        (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) :=
  hfi.mul_bdd (c := ‖ψ‖)
    (Continuous.aestronglyMeasurable (ψ.continuous.comp (by fun_prop)))
    (ae_of_all _ fun r => ψ.norm_coe_le_norm _)

theorem bcf_moment (f : (Fin 4 → ℝ) → ℝ)
    (hfi : Integrable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hz : ∀ s : Fin 4 → ℕ, ∫ r in Set.Ici (0 : Fin 4 → ℝ),
      f r * ∏ i, Real.exp (-r i) ^ s i = 0)
    (ψ : BoundedContinuousFunction (Fin 4 → ℝ) ℝ) :
    ∫ r in Set.Ici (0 : Fin 4 → ℝ), f r * ψ (fun i => Real.exp (-r i)) = 0 := by
  set μ := volume.restrict (Set.Ici (0 : Fin 4 → ℝ)) with hμ
  set I := ∫ r in Set.Ici (0 : Fin 4 → ℝ), f r * ψ (fun i => Real.exp (-r i)) with hI
  set C := ∫ r, ‖f r‖ ∂μ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun r => norm_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → |I| ≤ ε * C := by
    intro ε hε
    obtain ⟨p, hp⟩ := approx ψ ψ.continuous ε hε
    obtain ⟨hpi, hp0⟩ := poly_moment f hfi hz p
    have h1 : I = ∫ r, (f r * ψ (fun i => Real.exp (-r i)) -
        f r * MvPolynomial.eval (fun i => Real.exp (-r i)) p) ∂μ := by
      rw [integral_sub (bcf_integrable f hfi ψ) hpi, hp0, sub_zero]
    rw [h1, ← Real.norm_eq_abs, hC, mul_comm, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hfi.norm.mul_const ε) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hr' : ∀ i, 0 ≤ r i := fun i => hr i
    have hmem : (fun i => Real.exp (-r i)) ∈ Set.Icc (0 : Fin 4 → ℝ) 1 :=
      ⟨fun i => (Real.exp_pos _).le, fun i => Real.exp_le_one_iff.mpr (by linarith [hr' i])⟩
    have := hp _ hmem
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact this.le) (norm_nonneg _)
  by_contra hne
  have habs : 0 < |I| := abs_pos.mpr hne
  have := key (|I| / (2 * (C + 1))) (by positivity)
  have h2 : |I| / (2 * (C + 1)) * C < |I| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem core (f : (Fin 4 → ℝ) → ℝ)
    (hfm : AEMeasurable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hfi : Integrable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hz : ∀ s : Fin 4 → ℕ, ∫ r in Set.Ici (0 : Fin 4 → ℝ),
      f r * ∏ i, Real.exp (-r i) ^ s i = 0) :
    f =ᵐ[volume.restrict (Set.Ici (0 : Fin 4 → ℝ))] 0 := by
  set μ := volume.restrict (Set.Ici (0 : Fin 4 → ℝ)) with hμ
  let e : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun r i => Real.exp (-r i)
  have he : Continuous e := by fun_prop
  have hinj : Function.Injective e := by
    intro a b h
    funext i
    have := congr_fun h i
    simpa [e] using this
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  have hgp : AEMeasurable (fun r => ENNReal.ofReal (f r)) μ := hfm.ennreal_ofReal
  have hgm : AEMeasurable (fun r => ENNReal.ofReal (-f r)) μ := hfm.neg.ennreal_ofReal
  have hfinp : ∫⁻ r, ENNReal.ofReal (f r) ∂μ ≠ ⊤ := hfi.lintegral_lt_top.ne
  have hfinm : ∫⁻ r, ENNReal.ofReal (-f r) ∂μ ≠ ⊤ := hfi.neg.lintegral_lt_top.ne
  have : IsFiniteMeasure (μ.withDensity fun r => ENNReal.ofReal (f r)) :=
    isFiniteMeasure_withDensity hfinp
  have : IsFiniteMeasure (μ.withDensity fun r => ENNReal.ofReal (-f r)) :=
    isFiniteMeasure_withDensity hfinm
  have hmap : (μ.withDensity fun r => ENNReal.ofReal (f r)).map e =
      (μ.withDensity fun r => ENNReal.ofReal (-f r)).map e := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro ψ
    rw [integral_map hemb.measurable.aemeasurable ψ.continuous.aestronglyMeasurable,
      integral_map hemb.measurable.aemeasurable ψ.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ hgp (ae_of_all _ fun r => by simp),
      integral_withDensity_eq_integral_toReal_smul₀ hgm (ae_of_all _ fun r => by simp)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    have hcont : AEStronglyMeasurable (fun r => ψ (e r)) μ :=
      Continuous.aestronglyMeasurable (ψ.continuous.comp he)
    have hb : ∀ᵐ r ∂μ, ‖ψ (e r)‖ ≤ ‖ψ‖ := ae_of_all _ fun r => ψ.norm_coe_le_norm _
    have h1 : Integrable (fun r => max (f r) 0 * ψ (e r)) μ :=
      hfi.pos_part.mul_bdd hcont hb
    have h2 : Integrable (fun r => max (-f r) 0 * ψ (e r)) μ :=
      hfi.neg_part.mul_bdd hcont hb
    have h3 := bcf_moment f hfi hz ψ
    have h4 : ∀ r, f r * ψ (fun i => Real.exp (-r i)) =
        max (f r) 0 * ψ (e r) - max (-f r) 0 * ψ (e r) := by
      intro r
      rcases le_total (f r) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    simp_rw [h4] at h3
    rw [integral_sub h1 h2] at h3
    exact sub_eq_zero.mp h3
  have hρ : (μ.withDensity fun r => ENNReal.ofReal (f r)) =
      μ.withDensity fun r => ENNReal.ofReal (-f r) := by
    have := congrArg (Measure.comap e) hmap
    rwa [hemb.comap_map, hemb.comap_map] at this
  have hae := (withDensity_eq_iff hgp hgm hfinp).mp hρ
  filter_upwards [hae] with r hr
  rcases lt_trichotomy (f r) 0 with h | h | h
  · exfalso
    rw [ENNReal.ofReal_of_nonpos h.le] at hr
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne hr
  · exact h
  · exfalso
    rw [ENNReal.ofReal_of_nonpos (by linarith : -f r ≤ 0)] at hr
    exact (ENNReal.ofReal_pos.mpr h).ne' hr

theorem g_integrable :
    Integrable (fun r : Fin 4 → ℝ => ∏ i, Real.exp (-(1 / 2) * r i))
      (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
  have h : Set.Ici (0 : Fin 4 → ℝ) = Set.univ.pi fun _ => Set.Ici (0 : ℝ) :=
    (Set.pi_univ_Ici (0 : Fin 4 → ℝ)).symm
  have hv : (volume : Measure (Fin 4 → ℝ)) = Measure.pi fun _ => volume := rfl
  rw [hv, h, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (f := fun _ x => Real.exp (-(1 / 2) * x)) fun i =>
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_integrableOn_Ioi 0 (by norm_num))

end FracTruthSched.Dev.L10

namespace FracTruthSched

open MeasureTheory

theorem chk_lemma_10 (F : (Fin 4 → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hgrowth : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |F r| ≤ ∑ ν, r ν)
    (hL : ∀ θ : Fin 4 → ℝ, (∀ ν, 0 < θ ν) →
      ∫ r in Set.Ici (0 : Fin 4 → ℝ), F r * Real.exp (-∑ ν, θ ν * r ν) = 0) :
    F =ᵐ[volume.restrict (Set.Ici (0 : Fin 4 → ℝ))] 0 := by
  set f : (Fin 4 → ℝ) → ℝ := fun r => F r * Real.exp (-∑ ν, r ν) with hf
  have hfsm : AEStronglyMeasurable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) :=
    hF.mul (Continuous.aestronglyMeasurable (by fun_prop))
  have hfi : Integrable f (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
    refine Integrable.mono' (Dev.L10.g_integrable.const_mul 2) hfsm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have hr' : ∀ i, 0 ≤ r i := fun i => hr i
    have hS : 0 ≤ ∑ ν, r ν := Finset.sum_nonneg fun i _ => hr' i
    set S := ∑ ν, r ν with hSdef
    have hprod : ∏ i, Real.exp (-(1 / 2) * r i) = Real.exp (-S / 2) := by
      rw [← Real.exp_sum, hSdef, ← Finset.mul_sum]
      congr 1
      ring
    rw [hprod, hf]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |F r| ≤ S := hgrowth r hr
    have h2 : S ≤ 2 * Real.exp (S / 2) := by linarith [Real.add_one_le_exp (S / 2)]
    have h3 : Real.exp (-S) = Real.exp (-S / 2) * Real.exp (-S / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : Real.exp (S / 2) * Real.exp (-S / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hpos := Real.exp_pos (-S / 2)
    calc |F r| * Real.exp (-S) ≤ S * Real.exp (-S) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (S / 2) * Real.exp (-S) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (-S / 2) := by
          rw [h3]
          calc 2 * Real.exp (S / 2) * (Real.exp (-S / 2) * Real.exp (-S / 2))
              = 2 * (Real.exp (S / 2) * Real.exp (-S / 2)) * Real.exp (-S / 2) := by ring
            _ = 2 * Real.exp (-S / 2) := by rw [h4]; ring
  have hz : ∀ s : Fin 4 → ℕ, ∫ r in Set.Ici (0 : Fin 4 → ℝ),
      f r * ∏ i, Real.exp (-r i) ^ s i = 0 := by
    intro s
    have := hL (fun i => (s i : ℝ) + 1) fun i => by positivity
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hf]
    have hp : ∏ i, Real.exp (-r i) ^ s i = Real.exp (∑ i, -((s i : ℝ) * r i)) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hp, mul_assoc, ← Real.exp_add]
    congr 3
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hcore := Dev.L10.core f hfsm.aemeasurable hfi hz
  filter_upwards [hcore] with r hr
  have : F r * Real.exp (-∑ ν, r ν) = 0 := hr
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h (Real.exp_pos _).ne'

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_lemma_10 := @FracTruthSched.chk_lemma_10
