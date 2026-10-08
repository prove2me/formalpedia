-- Prove2me | solution 1 for ConnesRZ.finite_mellin_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T20:55:48.752278+00:00
-- url     : https://prove2.me/submissions/94eb4413-ed81-4260-a502-6e7dd87380e6

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

noncomputable section
namespace ConnesRZInterpolation

open ConnesRZ

def testSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | IsTest g}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  add_mem' := fun hg hh => ⟨hg.1.add hh.1, hg.2.add hh.2⟩
  smul_mem' := fun c g hg => ⟨hg.1.const_smul c, by
    change HasCompactSupport (fun t => c * g t)
    exact hg.2.mul_left⟩

lemma weighted_integrable (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    Integrable (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
  have hc : Continuous (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
    exact hg.1.continuous.mul (Complex.continuous_exp.comp (by fun_prop))
  exact hc.integrable_of_hasCompactSupport hg.2.mul_right

lemma mellin_add (g h : ℝ → ℂ) (hg : IsTest g) (hh : IsTest h) (z : ℂ) :
    mellinHat (g + h) z = mellinHat g z + mellinHat h z := by
  unfold mellinHat
  simp only [Pi.add_apply, add_mul]
  exact integral_add (weighted_integrable g hg z) (weighted_integrable h hh z)

lemma mellin_smul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) :
    mellinHat (c • g) z = c * mellinHat g z := by
  simp only [mellinHat, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

def mellinEval (z : ℂ) : testSpace →ₗ[ℂ] ℂ where
  toFun g := mellinHat g.1 z
  map_add' g h := mellin_add g.1 h.1 g.2 h.2 z
  map_smul' c g := by simpa [smul_eq_mul] using mellin_smul c g.1 z

lemma isTest_deriv (g : ℝ → ℂ) (hg : IsTest g) : IsTest (deriv g) :=
  ⟨(contDiff_infty_iff_deriv.mp hg.1).2, hg.2.deriv⟩

lemma mellin_deriv (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    mellinHat (deriv g) z = -(z - 1 / 2) * mellinHat g z := by
  let k := z - 1 / 2
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (k * u))
      (k * Complex.exp (k * t)) t := by
    intro t
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) (𝔸 := ℂ) k (t : ℂ)
    simpa [← Complex.exp_eq_exp_ℂ, smul_eq_mul, mul_comm] using h.comp_ofReal
  have hgd : ∀ t : ℝ, HasDerivAt g (deriv g t) t := fun t =>
    (hg.1.differentiable (by simp)).differentiableAt.hasDerivAt
  have hi : Integrable (fun t : ℝ =>
      deriv g t * Complex.exp (k * t) + k * (g t * Complex.exp (k * t))) :=
    (weighted_integrable (deriv g) (isTest_deriv g hg) z).add
      ((weighted_integrable g hg z).const_mul k)
  have hz : (∫ t : ℝ, deriv g t * Complex.exp (k * t) +
      k * (g t * Complex.exp (k * t))) = 0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable ?_ hi (weighted_integrable g hg z)
    intro t
    convert (hgd t).mul (hd t) using 1 <;> first | rfl | ring
  rw [integral_add (weighted_integrable (deriv g) (isTest_deriv g hg) z)
    ((weighted_integrable g hg z).const_mul k), integral_const_mul] at hz
  change mellinHat (deriv g) z + k * mellinHat g z = 0 at hz
  change mellinHat (deriv g) z = -k * mellinHat g z
  linear_combination hz

def derivative : testSpace →ₗ[ℂ] testSpace where
  toFun g := ⟨deriv g.1, isTest_deriv g.1 g.2⟩
  map_add' g h := by
    apply Subtype.ext
    funext t
    exact deriv_add ((g.2.1.differentiable (by simp)).differentiableAt)
      ((h.2.1.differentiable (by simp)).differentiableAt)
  map_smul' c g := by
    apply Subtype.ext
    funext t
    change deriv (fun y => c * g.1 y) t = c * deriv g.1 t
    exact deriv_const_mul c ((g.2.1.differentiable (by simp)).differentiableAt)

lemma mellinEval_ne_zero (z : ℂ) : mellinEval z ≠ 0 := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let g : ℝ → ℂ := fun t => (bump.normed volume t : ℂ) * Complex.exp (-((z - 1 / 2) * t))
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun t => (bump.normed volume t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff_normed
  have hg : IsTest g := by
    refine ⟨?_, ?_⟩
    · have hof : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
      exact hb.mul (((contDiff_const (c := z - 1 / 2)).mul hof).neg.cexp)
    · have hbs : HasCompactSupport (fun t => (bump.normed volume t : ℂ)) :=
        bump.hasCompactSupport_normed.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
      exact hbs.mul_right
  have heval : mellinHat g z = 1 := by
    unfold mellinHat
    have hint : (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) =
        fun t => (bump.normed volume t : ℂ) := by
      funext t
      dsimp [g]
      rw [mul_assoc, ← Complex.exp_add]
      simp
    rw [hint, integral_complex_ofReal, bump.integral_normed]
    rfl
  intro hz
  have h := LinearMap.congr_fun hz (⟨g, hg⟩ : testSpace)
  change mellinHat g z = 0 at h
  rw [heval] at h
  exact one_ne_zero h

lemma mellinEval_independent {ι : Type*} (z : ι → ℂ) (hz : Function.Injective z) :
    LinearIndependent ℂ (fun i => mellinEval (z i)) := by
  apply Module.End.eigenvectors_linearIndependent' derivative.dualMap
    (fun i => -(z i - 1 / 2)) (fun i j h => hz (by simpa only [neg_inj, sub_left_inj] using h))
  intro i
  refine ⟨?_, mellinEval_ne_zero _⟩
  rw [Module.End.mem_eigenspace_iff]
  apply LinearMap.ext
  intro g
  exact mellin_deriv g.1 g.2 (z i)

end ConnesRZInterpolation

open ConnesRZ ConnesRZInterpolation

/-- Finite Mellin interpolation on smooth compactly supported test functions. -/
theorem solution {ι : Type*} [Finite ι] (z : ι → ℂ) (hz : Function.Injective z)
    (a : ι → ℂ) : ∃ g : ℝ → ℂ, IsTest g ∧ ∀ i, mellinHat g (z i) = a i := by
  classical
  let E : testSpace →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun i => mellinEval (z i))
  have hli : LinearIndependent ℂ (fun i => (mellinEval (z i) : testSpace → ℂ)) := by
    apply linearIndependent_iff.mpr
    intro l hl
    apply (linearIndependent_iff.mp (mellinEval_independent z hz)) l
    apply LinearMap.ext
    intro g
    have h := congrFun hl g
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul] using h
  have hspan : Submodule.span ℂ (Set.range (fun g : testSpace => E g)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hle : Submodule.span ℂ (Set.range (fun g : testSpace => E g)) ≤ E.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hrange : E.range = ⊤ := top_unique (hspan ▸ hle)
  obtain ⟨g, hg⟩ := LinearMap.range_eq_top.mp hrange a
  exact ⟨g.1, g.2, fun i => congrFun hg i⟩
