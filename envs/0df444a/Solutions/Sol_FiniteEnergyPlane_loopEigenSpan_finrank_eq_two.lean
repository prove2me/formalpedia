-- Prove2me | solution 1 for FiniteEnergyPlane.loopEigenSpan_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:27:39.036687+00:00
-- url     : https://prove2.me/submissions/1782edff-ce1b-4594-be62-c6845518f228

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
import Theorems.Thm_FiniteEnergyPlane_loopEigen_apply_ne_smul_of_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_exists_isLoopEigen_hasLoopEigenWind_linearIndependent
import Theorems.Thm_FiniteEnergyPlane_false_of_three_hasLoopEigenWind
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul



namespace FiniteEnergyPlane

open scoped ContDiff

/-- Solutions of the eigen-equation for `μ`, zero allowed. -/
def WLSol (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (μ : ℝ) (f : ℝ → CauchyRiemannIndex.Vec 1) :
    Prop :=
  ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ ∀ t : ℝ,
    -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv f t)) -
      Matrix.toEuclideanLin (Sinf t) (f t) = μ • f t

theorem wl_sol_of_eigen {Sinf : ℝ → CauchyRiemannIndex.Mat 1} {μ : ℝ}
    {e : ℝ → CauchyRiemannIndex.Vec 1} (he : IsLoopEigen Sinf μ e) : WLSol Sinf μ e :=
  ⟨he.1, he.2.1, he.2.2.2⟩

theorem wl_sol_lin {Sinf : ℝ → CauchyRiemannIndex.Mat 1} {μ : ℝ}
    {f g : ℝ → CauchyRiemannIndex.Vec 1} (hf : WLSol Sinf μ f) (hg : WLSol Sinf μ g)
    (a b : ℝ) : WLSol Sinf μ (fun t => a • f t + b • g t) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨(hf1.const_smul a).add (hg1.const_smul b), fun t => by simp [hf2 t, hg2 t], ?_⟩
  intro t
  have df : HasDerivAt f (deriv f t) t :=
    ((hf1.differentiable (by simp)) t).hasDerivAt
  have dg : HasDerivAt g (deriv g t) t :=
    ((hg1.differentiable (by simp)) t).hasDerivAt
  have hd : HasDerivAt (fun t => a • f t + b • g t) (a • deriv f t + b • deriv g t) t :=
    (df.const_smul a).add (dg.const_smul b)
  rw [hd.deriv]
  simp only [map_add, map_smul]
  have h1 := hf3 t
  have h2 := hg3 t
  linear_combination (norm := module) a • h1 + b • h2

theorem wl_sol_eq_zero {Sinf : ℝ → CauchyRiemannIndex.Mat 1} (hSinf : Continuous Sinf)
    {μ : ℝ} {f : ℝ → CauchyRiemannIndex.Vec 1} (hf : WLSol Sinf μ f) (h0 : f 0 = 0) :
    f = 0 := by
  by_contra hne
  have hex : ∃ t, f t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  exact isLoopEigen_apply_ne_zero Sinf hSinf μ f ⟨hf.1, hf.2.1, hex, hf.2.2⟩ 0 h0

theorem wl_eigen_of_sol {Sinf : ℝ → CauchyRiemannIndex.Mat 1} {μ : ℝ}
    {f : ℝ → CauchyRiemannIndex.Vec 1} (hf : WLSol Sinf μ f) (h0 : f 0 ≠ 0) :
    IsLoopEigen Sinf μ f :=
  ⟨hf.1, hf.2.1, ⟨0, h0⟩, hf.2.2⟩

theorem wl_exists_coeffs {u v w : CauchyRiemannIndex.Vec 1}
    (hli : LinearIndependent ℝ ![u, v]) : ∃ a b : ℝ, w = a • u + b • v := by
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hw : w ∈ Submodule.span ℝ (Set.range ![u, v]) := by rw [htop]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at hw
  obtain ⟨a, b, h⟩ := Submodule.mem_span_pair.1 hw
  exact ⟨a, b, h.symm⟩

/-- Case of one eigenvalue carrying two independent eigenfunctions. -/
theorem wl_mem_of_eq (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ ν : ℝ} {k : ℤ}
    {e₁ e₂ e : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ e₁)
    (he₂ : IsLoopEigen Sinf μ e₂) (hw : HasLoopEigenWind Sinf μ k)
    (hli : LinearIndependent ℝ ![e₁ 0, e₂ 0]) (he : IsLoopEigen Sinf ν e)
    (hwe : HasLoopEigenWind Sinf ν k) :
    e ∈ Submodule.span ℝ ({e₁, e₂} : Set (ℝ → CauchyRiemannIndex.Vec 1)) := by
  obtain ⟨a, b, hab⟩ := wl_exists_coeffs (w := e 0) hli
  have hf := wl_sol_lin (wl_sol_of_eigen he₁) (wl_sol_of_eigen he₂) a b
  have he0 := isLoopEigen_apply_ne_zero Sinf hSinf.1 ν e he 0
  by_cases hν : ν = μ
  · subst hν
    have hd := wl_sol_lin (wl_sol_of_eigen he) hf 1 (-1)
    have h0 := wl_sol_eq_zero hSinf.1 hd (by simp [← hab])
    refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
    funext t
    have := congrFun h0 t
    simp only [Pi.zero_apply, one_smul, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at this
    simp [this]
  · exfalso
    have hfe : IsLoopEigen Sinf μ (fun t => a • e₁ t + b • e₂ t) :=
      wl_eigen_of_sol hf (by rw [← hab]; exact he0)
    exact loopEigen_apply_ne_smul_of_hasLoopEigenWind Sinf hSinf hSinf' (Ne.symm hν) hw hwe
      hfe he 0 1 (by rw [one_smul, hab])

/-- Case of an eigenvalue `μ₁ ≠ μ₂`: eigenfunctions of `μ₁` lie in the span. -/
theorem wl_mem_of_ne (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) {μ₁ μ₂ : ℝ} {k : ℤ} (hμ : μ₁ ≠ μ₂)
    {e₁ e₂ e : ℝ → CauchyRiemannIndex.Vec 1} (he₁ : IsLoopEigen Sinf μ₁ e₁)
    (he₂ : IsLoopEigen Sinf μ₂ e₂) (hw₁ : HasLoopEigenWind Sinf μ₁ k)
    (hw₂ : HasLoopEigenWind Sinf μ₂ k)
    (hli : LinearIndependent ℝ ![e₁ 0, e₂ 0]) (he : IsLoopEigen Sinf μ₁ e) :
    e ∈ Submodule.span ℝ ({e₁, e₂} : Set (ℝ → CauchyRiemannIndex.Vec 1)) := by
  obtain ⟨a, b, hab⟩ := wl_exists_coeffs (w := e 0) hli
  have hg := wl_sol_lin (wl_sol_of_eigen he) (wl_sol_of_eigen he₁) 1 (-a)
  have hg0 : (1 : ℝ) • e 0 + (-a) • e₁ 0 = b • e₂ 0 := by
    simp only [one_smul, neg_smul, hab]; abel
  by_cases hb : b = 0
  · have h0 := wl_sol_eq_zero hSinf.1 hg (by rw [hg0, hb, zero_smul])
    refine Submodule.mem_span_pair.2 ⟨a, 0, ?_⟩
    funext t
    have := congrFun h0 t
    simp only [Pi.zero_apply, one_smul, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at this
    simp [this]
  · exfalso
    have he₂0 := isLoopEigen_apply_ne_zero Sinf hSinf.1 μ₂ e₂ he₂ 0
    have hge : IsLoopEigen Sinf μ₁ (fun t => (1 : ℝ) • e t + (-a) • e₁ t) :=
      wl_eigen_of_sol hg (by rw [hg0]; exact smul_ne_zero hb he₂0)
    exact loopEigen_apply_ne_smul_of_hasLoopEigenWind Sinf hSinf hSinf' hμ hw₁ hw₂ hge he₂ 0
      b⁻¹ (by rw [hg0, smul_smul, inv_mul_cancel₀ hb, one_smul])

theorem loopEigenSpan_finrank_eq_two_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    FiniteDimensional ℝ (loopEigenSpan Sinf k) ∧ Module.finrank ℝ (loopEigenSpan Sinf k) = 2 := by
  obtain ⟨μ₁, μ₂, e₁, e₂, he₁, he₂, hw₁, hw₂, hli⟩ :=
    exists_isLoopEigen_hasLoopEigenWind_linearIndependent Sinf hSinf hSinf' k
  have hli' : LinearIndependent ℝ ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t hst
    exact hli s t (by simpa using congrFun hst 0)
  have hspan : loopEigenSpan Sinf k =
      Submodule.span ℝ ({e₁, e₂} : Set (ℝ → CauchyRiemannIndex.Vec 1)) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro e ⟨ν, he, hwe⟩
      by_cases h12 : μ₁ = μ₂
      · subst h12
        exact wl_mem_of_eq Sinf hSinf hSinf' he₁ he₂ hw₁ hli he hwe
      · by_cases h1 : ν = μ₁
        · subst h1
          exact wl_mem_of_ne Sinf hSinf hSinf' h12 he₁ he₂ hw₁ hw₂ hli he
        by_cases h2 : ν = μ₂
        · subst h2
          have hli2 : LinearIndependent ℝ ![e₂ 0, e₁ 0] := by
            rw [LinearIndependent.pair_iff] at hli ⊢
            intro s t hst
            have := hli t s (by rw [add_comm]; exact hst)
            exact ⟨this.2, this.1⟩
          rw [Set.pair_comm]
          exact wl_mem_of_ne Sinf hSinf hSinf' (Ne.symm h12) he₂ he₁ hw₂ hw₁ hli2 he
        exfalso
        have T := fun {a b c : ℝ} (hab : a < b) (hbc : b < c) (ha : HasLoopEigenWind Sinf a k)
          (hb : HasLoopEigenWind Sinf b k) (hc : HasLoopEigenWind Sinf c k) =>
          false_of_three_hasLoopEigenWind Sinf hSinf hSinf' hab hbc ha hb hc
        rcases lt_or_gt_of_ne h12 with h | h <;>
          rcases lt_or_gt_of_ne h1 with g1 | g1 <;>
          rcases lt_or_gt_of_ne h2 with g2 | g2
        all_goals first
          | exact T g1 h hwe hw₁ hw₂
          | exact T h g2 hw₁ hw₂ hwe
          | exact T g1 g2 hw₁ hwe hw₂
          | exact T g2 h hwe hw₂ hw₁
          | exact T h g1 hw₂ hw₁ hwe
          | exact T g2 g1 hw₂ hwe hw₁
          | linarith
    · apply Submodule.span_le.2
      rintro e (rfl | rfl)
      · exact Submodule.subset_span ⟨μ₁, he₁, hw₁⟩
      · exact Submodule.subset_span ⟨μ₂, he₂, hw₂⟩
  have hfin : FiniteDimensional ℝ (loopEigenSpan Sinf k) := by
    rw [hspan]
    exact FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  refine ⟨hfin, ?_⟩
  have hr : ({e₁, e₂} : Set (ℝ → CauchyRiemannIndex.Vec 1)) = Set.range ![e₁, e₂] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [hspan, hr, finrank_span_eq_card hli']
  simp

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    FiniteDimensional ℝ (loopEigenSpan Sinf k) ∧ Module.finrank ℝ (loopEigenSpan Sinf k) = 2 :=
  loopEigenSpan_finrank_eq_two_aux Sinf hSinf hSinf' k
