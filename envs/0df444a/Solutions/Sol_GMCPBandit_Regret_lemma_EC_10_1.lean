-- Prove2me | solution 1 for GMCPBandit.Regret.lemma_EC_10_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:30:23.374198+00:00
-- url     : https://prove2.me/submissions/a5df46c5-2b9d-4004-a675-a6c11245deca

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret.EC10aux

/-- `|e^u − 1| ≤ |u| e^{|u|}`. -/
lemma abs_exp_sub_one_le' (u : ℝ) : |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · have h1 := Real.add_one_le_exp (-u)
    have h2 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos u
    rw [abs_of_nonneg hu, abs_of_nonneg (by linarith [Real.add_one_le_exp u])]
    nlinarith
  · have h1 := Real.add_one_le_exp u
    have h2 : Real.exp u ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hu.le
    rw [abs_of_nonpos (by linarith), abs_of_neg hu]
    have h3 : 1 ≤ Real.exp (-u) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    nlinarith

/-- `|x ⬝ᵥ v| ≤ xmax ‖v‖₁` when `‖x‖_∞ ≤ xmax`. -/
lemma abs_dot_le {d : ℕ} (x v : Fin d → ℝ) (xmax : ℝ) (hx : ∀ j, |x j| ≤ xmax) :
    |x ⬝ᵥ v| ≤ xmax * l1 v := by
  unfold dotProduct l1
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hx j) (abs_nonneg _)

end GMCPBandit.Regret.EC10aux

open GMCPBandit.Regret GMCPBandit.Regret.EC10aux in
theorem solution {d K : ℕ} (𝒳 : Set (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b σ σ2 σ3 : ℝ)
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3)
    (hf' : ∀ r ∈ Set.Icc (-Rmax) Rmax, ∀ η : ℝ, |η| ≤ b * xmax →
      |deriv (fun η => negLogDens g r η) η| ≤ σ2)
    (x : Fin d → ℝ) (hx : x ∈ 𝒳) (i : Fin K) (βhat : Fin d → ℝ) (hβhat : l1 βhat ≤ b) :
    |meanFn ν g (x ⬝ᵥ β i) - meanFn ν g (x ⬝ᵥ βhat)| ≤
      Rmax * Real.exp (σ2 * xmax * l1 (βhat - β i)) * σ2 * xmax * l1 (βhat - β i) := by
  obtain ⟨hxmax, -, hRmax, -, -, hxb, -, -, hβb⟩ := hA1
  obtain ⟨-, hσ2, -, hA5'⟩ := hA5
  have hxj : ∀ j, |x j| ≤ xmax := hxb x hx
  set η1 := x ⬝ᵥ β i with hη1
  set η2 := x ⬝ᵥ βhat with hη2
  set L := l1 (βhat - β i) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hη1b : |η1| ≤ b * xmax := by
    have := abs_dot_le x (β i) xmax hxj
    nlinarith [hβb i]
  have hη2b : |η2| ≤ b * xmax := by
    have := abs_dot_le x βhat xmax hxj
    nlinarith
  have hδ : |η2 - η1| ≤ xmax * L := by
    have : η2 - η1 = x ⬝ᵥ (βhat - β i) := by
      rw [hη1, hη2, dotProduct_sub]
    rw [this]; exact abs_dot_le x _ xmax hxj
  set δ := |η2 - η1| with hδdef
  have hδ0 : 0 ≤ δ := abs_nonneg _
  -- pointwise bound on the density difference
  have hpt : ∀ r ∈ Set.Icc (-Rmax) Rmax,
      |g r η1 - g r η2| ≤ g r η1 * (σ2 * δ * Real.exp (σ2 * δ)) := by
    intro r hr
    set F := fun η => negLogDens g r η with hF
    have hgF : ∀ η, g r η = Real.exp (-F η) := by
      intro η
      simp only [hF, negLogDens, neg_neg]
      rw [Real.exp_log (hglm.pos r hr η)]
    obtain ⟨hsmooth, -, hder⟩ := hA5' r hr
    have hdiff : Differentiable ℝ F := hsmooth.differentiable (by simp)
    have hMV : ‖F η2 - F η1‖ ≤ σ2 * ‖η2 - η1‖ := by
      refine Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (-(b * xmax)) (b * xmax))
        (fun y _ => hdiff y) (fun y hy => ?_) (convex_Icc _ _) ?_ ?_
      · rw [Real.norm_eq_abs]
        exact hf' r hr y (abs_le.mpr hy)
      · exact abs_le.mp hη1b
      · exact abs_le.mp hη2b
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hMV
    have hu : |-(F η2 - F η1)| ≤ σ2 * δ := by rw [abs_neg]; exact hMV
    have key : g r η1 - g r η2 = - (g r η1 * (Real.exp (-(F η2 - F η1)) - 1)) := by
      rw [hgF η1, hgF η2, mul_sub, ← Real.exp_add]; ring_nf
    rw [key, abs_neg, abs_mul, abs_of_pos (hglm.pos r hr η1)]
    apply mul_le_mul_of_nonneg_left _ (hglm.pos r hr η1).le
    refine (abs_exp_sub_one_le' _).trans ?_
    exact mul_le_mul hu (Real.exp_le_exp.mpr hu) (Real.exp_pos _).le (by positivity)
  have hae : ∀ᵐ r ∂ν, r ∈ Set.Icc (-Rmax) Rmax := mem_ae_iff.mpr hglm.concentrated
  have hmeas : ∀ η, Measurable (fun r => g r η) := fun η =>
    hglm.measurable_g.comp (measurable_id.prodMk measurable_const)
  have hint : ∀ η, Integrable (fun r => r * g r η) ν := fun η =>
    (hglm.integrable η).bdd_mul (c := Rmax) measurable_id.aestronglyMeasurable
      (hae.mono fun r hr => by rw [Real.norm_eq_abs]; exact abs_le.mpr hr)
  have hdiffI : meanFn ν g η1 - meanFn ν g η2 = ∫ r, (r * g r η1 - r * g r η2) ∂ν := by
    unfold meanFn; rw [integral_sub (hint η1) (hint η2)]
  set c := σ2 * δ * Real.exp (σ2 * δ) with hc
  have hbound : |meanFn ν g η1 - meanFn ν g η2| ≤ ∫ r, Rmax * c * g r η1 ∂ν := by
    rw [hdiffI, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hglm.integrable η1).const_mul (Rmax * c)) ?_
    filter_upwards [hae] with r hr
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    have h1 := hpt r hr
    have h2 : |r| ≤ Rmax := abs_le.mpr hr
    have h3 : 0 ≤ g r η1 * c := mul_nonneg (hglm.pos r hr η1).le (by positivity)
    calc |r| * |g r η1 - g r η2| ≤ Rmax * (g r η1 * c) :=
          mul_le_mul h2 h1 (abs_nonneg _) hRmax.le
      _ = Rmax * c * g r η1 := by ring
  rw [integral_const_mul, hglm.normalized, mul_one] at hbound
  refine hbound.trans ?_
  -- Rmax σ2 δ e^{σ2 δ} ≤ Rmax e^{σ2 xmax L} σ2 xmax L
  have hσδ : σ2 * δ ≤ σ2 * (xmax * L) := mul_le_mul_of_nonneg_left hδ hσ2.le
  have he : Real.exp (σ2 * δ) ≤ Real.exp (σ2 * xmax * L) := by
    rw [mul_assoc]; exact Real.exp_le_exp.mpr hσδ
  calc Rmax * c = Rmax * (σ2 * δ) * Real.exp (σ2 * δ) := by rw [hc]; ring
    _ ≤ Rmax * (σ2 * (xmax * L)) * Real.exp (σ2 * xmax * L) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hσδ hRmax.le) he (Real.exp_pos _).le
        positivity
    _ = _ := by ring
