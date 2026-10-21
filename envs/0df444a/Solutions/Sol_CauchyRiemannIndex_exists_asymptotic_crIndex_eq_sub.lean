-- Prove2me | solution 1 for CauchyRiemannIndex.exists_asymptotic_crIndex_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-20T13:35:50.891662+00:00
-- url     : https://prove2.me/submissions/cfe71df2-f467-4cda-903d-4c778da60e38

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_CauchyRiemannIndex_exists_antilinear_profile
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_perturbation_index
import Theorems.Thm_CauchyRiemannIndex_model_asymptotic_operator



/-!
# Reference operators on the cylinder with index `a - b`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma crm_entry (b : ℂ) (i j : Fin 1 ⊕ Fin 1) :
    antilinearMat b i j = match i, j with
      | .inl _, .inl _ => b.re
      | .inl _, .inr _ => b.im
      | .inr _, .inl _ => b.im
      | .inr _, .inr _ => -b.re := by
  rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat, Matrix.fromBlocks]

lemma crm_isSymm (b : ℂ) : (antilinearMat b).IsSymm := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [antilinearMat, Matrix.transpose_apply, Matrix.fromBlocks]

lemma crm_continuous_antilinearMat : Continuous antilinearMat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [crm_entry] <;> fun_prop

lemma crm_entry_sub_le (b c : ℂ) (i j : Fin 1 ⊕ Fin 1) :
    |antilinearMat b i j - antilinearMat c i j| ≤ ‖b - c‖ := by
  have h1 := Complex.abs_re_le_norm (b - c)
  have h2 := Complex.abs_im_le_norm (b - c)
  rcases i with i | i <;> rcases j with j | j <;> simp only [crm_entry] <;>
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  · exact h1
  · exact h2
  · exact h2
  · rw [show -b.re - -c.re = -(b.re - c.re) by ring, abs_neg]; exact h1

/-- The model loop `π k + σ B(e^{2πikt})`. -/
def crmLoop (k : ℤ) (σ : ℝ) : ℝ → Mat 1 := fun t =>
  (Real.pi * k) • (1 : Mat 1) + σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I))

lemma crm_exp_periodic (k : ℤ) (t : ℝ) :
    Complex.exp (2 * Real.pi * k * ((t + 1 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * k * (t : ℂ) * Complex.I) := by
  have : (2 * Real.pi * k * ((t + 1 : ℝ) : ℂ) * Complex.I) =
      2 * Real.pi * k * (t : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma crm_loop_isSymLoop (k : ℤ) (σ : ℝ) : IsSymLoop (crmLoop k σ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold crmLoop
    have he : Continuous fun t : ℝ => Complex.exp (2 * Real.pi * k * (t : ℂ) * Complex.I) :=
      Complex.continuous_exp.comp (by fun_prop)
    exact continuous_const.add ((crm_continuous_antilinearMat.comp he).const_smul σ)
  · intro t
    simp only [crmLoop]
    rw [crm_exp_periodic]
  · intro t
    unfold crmLoop
    exact (Matrix.IsSymm.smul (Matrix.isSymm_one) _).add ((crm_isSymm _).smul _)

/-- Continuous cutoffs vanishing on `|s| ≤ 1`, equal to `1` for `s ≥ 2` resp. `s ≤ -2`. -/
def crmPhiP (s : ℝ) : ℝ := max 0 (min 1 (s - 1))
def crmPhiM (s : ℝ) : ℝ := max 0 (min 1 (-s - 1))

lemma crm_phiP_cont : Continuous crmPhiP := by unfold crmPhiP; fun_prop
lemma crm_phiM_cont : Continuous crmPhiM := by unfold crmPhiM; fun_prop

/-- The base coefficient built from `β`. -/
def crmS (a b : ℤ) (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : Mat 1 :=
  crmPhiP x.1 • ((Real.pi * a) • (1 : Mat 1) + antilinearMat (β x)) +
    crmPhiM x.1 • ((Real.pi * b) • (1 : Mat 1) + antilinearMat (β x))

lemma crm_isAsymptoticTo (a b : ℤ) (β : ℝ × ℝ → ℂ) (hβ : Continuous β)
    (hper : ∀ s t, β (s, t + 1) = β (s, t))
    (hlim : ∀ ε > 0, ∃ R : ℝ, ∀ s t,
        (R ≤ s → ‖β (s, t) - Complex.exp (2 * Real.pi * a * t * Complex.I)‖ ≤ ε) ∧
        (s ≤ -R → ‖β (s, t) - Complex.exp (2 * Real.pi * b * t * Complex.I)‖ ≤ ε))
    (σ : ℝ) (hσ : 0 ≤ σ) :
    IsAsymptoticTo (fun x => crmS a b β x + σ • antilinearMat (β x))
      (crmLoop a (1 + σ)) (crmLoop b (1 + σ)) := by
  have hB : Continuous fun x => antilinearMat (β x) := crm_continuous_antilinearMat.comp hβ
  refine ⟨?_, ?_, ?_⟩
  · unfold crmS
    exact (((crm_phiP_cont.comp continuous_fst).smul (continuous_const.add hB)).add
      ((crm_phiM_cont.comp continuous_fst).smul (continuous_const.add hB))).add
      (hB.const_smul σ)
  · intro s t
    simp only [crmS, hper]
  · intro ε hε
    obtain ⟨R, hR⟩ := hlim (ε / (1 + σ)) (by positivity)
    refine ⟨max R 2, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · have h1 : crmPhiP s = 1 := by
        unfold crmPhiP
        rw [min_eq_left (by linarith [le_max_right R 2])]; norm_num
      have h2 : crmPhiM s = 0 := by
        unfold crmPhiM
        exact max_eq_left (by
          have := le_max_right R 2
          exact (min_le_right _ _).trans (by linarith))
      have hb := (hR s t).1 (le_trans (le_max_left R 2) hs)
      simp only [crmS, crmLoop, h1, h2, one_smul, zero_smul, add_zero, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      have := crm_entry_sub_le (β (s, t)) (Complex.exp (2 * Real.pi * a * t * Complex.I)) i j
      have e : (Real.pi * a * (1 : Mat 1) i j + antilinearMat (β (s, t)) i j +
          σ * antilinearMat (β (s, t)) i j) -
          (Real.pi * a * (1 : Mat 1) i j +
            (1 + σ) * antilinearMat (Complex.exp (2 * Real.pi * a * t * Complex.I)) i j) =
          (1 + σ) * (antilinearMat (β (s, t)) i j -
            antilinearMat (Complex.exp (2 * Real.pi * a * t * Complex.I)) i j) := by ring
      rw [e, abs_mul, abs_of_pos (by linarith)]
      calc (1 + σ) * _ ≤ (1 + σ) * (ε / (1 + σ)) :=
            mul_le_mul_of_nonneg_left (this.trans hb) (by linarith)
        _ = ε := by field_simp
    · have h1 : crmPhiM s = 1 := by
        unfold crmPhiM
        rw [min_eq_left (by linarith [le_max_right R 2])]; norm_num
      have h2 : crmPhiP s = 0 := by
        unfold crmPhiP
        exact max_eq_left (by
          have := le_max_right R 2
          exact (min_le_right _ _).trans (by linarith))
      have hb := (hR s t).2 (by linarith [le_max_left R 2, hs])
      simp only [crmS, crmLoop, h1, h2, one_smul, zero_smul, zero_add, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul]
      have := crm_entry_sub_le (β (s, t)) (Complex.exp (2 * Real.pi * b * t * Complex.I)) i j
      have e : (Real.pi * b * (1 : Mat 1) i j + antilinearMat (β (s, t)) i j +
          σ * antilinearMat (β (s, t)) i j) -
          (Real.pi * b * (1 : Mat 1) i j +
            (1 + σ) * antilinearMat (Complex.exp (2 * Real.pi * b * t * Complex.I)) i j) =
          (1 + σ) * (antilinearMat (β (s, t)) i j -
            antilinearMat (Complex.exp (2 * Real.pi * b * t * Complex.I)) i j) := by ring
      rw [e, abs_mul, abs_of_pos (by linarith)]
      calc (1 + σ) * _ ≤ (1 + σ) * (ε / (1 + σ)) :=
            mul_le_mul_of_nonneg_left (this.trans hb) (by linarith)
        _ = ε := by field_simp

theorem exists_asymptotic_crIndex_eq_sub_aux (a b : ℤ) :
    ∃ (S : ℝ × ℝ → Mat 1) (Splus Sminus : ℝ → Mat 1),
      IsSymLoop Splus ∧ IsSymLoop Sminus ∧ IsNondegenerate Splus ∧ IsNondegenerate Sminus ∧
        asymptoticCZIndex Splus = a ∧ asymptoticCZIndex Sminus = b ∧
          IsAsymptoticTo S Splus Sminus ∧ crIndex 2 S = a - b := by
  obtain ⟨β, Zplus, Zminus, r, hβ, hper, hC1, hends, hlim, hZ, hdisj, hzero, hr, hband,
    hplusZ, hminusZ, hba, hab⟩ := exists_antilinear_profile a b
  have hβc : Continuous β := hβ.continuous
  have hS0 : IsAsymptoticTo (crmS a b β) (crmLoop a 1) (crmLoop b 1) := by
    simpa using crm_isAsymptoticTo a b β hβc hper hlim 0 le_rfl
  have hnd : ∀ (k : ℤ) (σ : ℝ), 0 < σ → IsNondegenerate (crmLoop k σ) ∧
      asymptoticCZIndex (crmLoop k σ) = k := fun k σ hσ => model_asymptotic_operator k σ hσ
  -- `S = 0` on the discs around the zeros
  have hSzero : ∀ ζ ∈ Zplus ∪ Zminus, ∀ z : ℂ, ‖z‖ < r →
      crmS a b β (ζ.1 + z.re, ζ.2 + z.im) = 0 := by
    intro ζ hζ z hz
    have h1 := hband ζ hζ
    have h2 : |ζ.1 + z.re| < 1 := by
      calc |ζ.1 + z.re| ≤ |ζ.1| + |z.re| := abs_add_le _ _
        _ ≤ |ζ.1| + ‖z‖ := by gcongr; exact Complex.abs_re_le_norm z
        _ < 1 := by linarith
    have hp : crmPhiP (ζ.1 + z.re) = 0 := by
      unfold crmPhiP
      exact max_eq_left ((min_le_right _ _).trans (by linarith [(abs_lt.1 h2).2]))
    have hm : crmPhiM (ζ.1 + z.re) = 0 := by
      unfold crmPhiM
      exact max_eq_left ((min_le_right _ _).trans (by linarith [(abs_lt.1 h2).1]))
    simp [crmS, hp, hm]
  have h527 := large_antilinear_perturbation_index (crmLoop a 1) (crmLoop b 1)
    (crm_loop_isSymLoop a 1) (crm_loop_isSymLoop b 1) (hnd a 1 one_pos).1 (hnd b 1 one_pos).1
    (crmS a b β) hS0 β hβ (fun s t => hper s t) hC1 hends Zplus Zminus hZ hdisj hzero r hr
    (fun ζ hζ z hz => ⟨hplusZ ζ hζ z hz, hSzero ζ (Finset.mem_union_left _ hζ) z hz⟩)
    (fun ζ hζ z hz => ⟨hminusZ ζ hζ z hz, hSzero ζ (Finset.mem_union_right _ hζ) z hz⟩)
  -- the reference operator at a given `σ`
  have hfinal : ∀ σ : ℝ, 0 ≤ σ → crIndex 2 (fun x => crmS a b β x + σ • antilinearMat (β x)) =
      a - b → ∃ (S : ℝ × ℝ → Mat 1) (Splus Sminus : ℝ → Mat 1),
      IsSymLoop Splus ∧ IsSymLoop Sminus ∧ IsNondegenerate Splus ∧ IsNondegenerate Sminus ∧
        asymptoticCZIndex Splus = a ∧ asymptoticCZIndex Sminus = b ∧
          IsAsymptoticTo S Splus Sminus ∧ crIndex 2 S = a - b := by
    intro σ hσ hidx
    have h1σ : (0 : ℝ) < 1 + σ := by linarith
    exact ⟨_, crmLoop a (1 + σ), crmLoop b (1 + σ), crm_loop_isSymLoop a _,
      crm_loop_isSymLoop b _, (hnd a _ h1σ).1, (hnd b _ h1σ).1, (hnd a _ h1σ).2,
      (hnd b _ h1σ).2, crm_isAsymptoticTo a b β hβc hper hlim σ hσ, hidx⟩
  rcases le_total b a with hle | hle
  · obtain ⟨hZm, hcard⟩ := hba hle
    obtain ⟨σ₀, hσ₀⟩ := h527.1 hZm
    obtain ⟨hrange, -, hker⟩ := hσ₀ (max σ₀ 0) (le_max_left _ _)
    refine hfinal (max σ₀ 0) (le_max_right _ _) ?_
    unfold crIndex
    rw [hker, hrange, hcard]
    rw [Module.finrank_zero_of_subsingleton]
    simp
  · obtain ⟨hZp, hcard⟩ := hab hle
    obtain ⟨σ₀, hσ₀⟩ := h527.2 hZp
    obtain ⟨hker, -, hcoker⟩ := hσ₀ (max σ₀ 0) (le_max_left _ _)
    refine hfinal (max σ₀ 0) (le_max_right _ _) ?_
    unfold crIndex
    rw [hker, hcoker, hcard, finrank_bot]
    ring

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (a b : ℤ) :
    ∃ (S : ℝ × ℝ → Mat 1) (Splus Sminus : ℝ → Mat 1),
      IsSymLoop Splus ∧ IsSymLoop Sminus ∧ IsNondegenerate Splus ∧ IsNondegenerate Sminus ∧
        asymptoticCZIndex Splus = a ∧ asymptoticCZIndex Sminus = b ∧
          IsAsymptoticTo S Splus Sminus ∧ crIndex 2 S = a - b :=
  CauchyRiemannIndex.exists_asymptotic_crIndex_eq_sub_aux a b
