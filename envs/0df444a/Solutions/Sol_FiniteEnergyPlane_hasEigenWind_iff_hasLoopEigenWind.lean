-- Prove2me | solution 1 for FiniteEnergyPlane.hasEigenWind_iff_hasLoopEigenWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:29:48.037195+00:00
-- url     : https://prove2.me/submissions/a855ce07-1d39-4a98-85a0-a32f6182ddb3

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_ne_zero_hasLoopEigenWind
import Mathlib.Analysis.CStarAlgebra.Matrix



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- Matrices acting on `ℝ²` as continuous linear maps. -/
noncomputable abbrev h310_mE (A : Mat 1) : Vec 1 →L[ℝ] Vec 1 :=
  Matrix.toEuclideanCLM (n := Fin 1 ⊕ Fin 1) (𝕜 := ℝ) A

lemma h310_mE_JJ (v : Vec 1) : h310_mE (J₀ 1) (h310_mE (J₀ 1) v) = -v := by
  have : h310_mE (J₀ 1 * J₀ 1) v = h310_mE (J₀ 1) (h310_mE (J₀ 1) v) := by
    simp [h310_mE, map_mul]
  rw [← this, show J₀ 1 * J₀ 1 = -1 from Matrix.J_squared _ _]
  simp [h310_mE, map_neg, map_one]

/-- The basis vector `eᵢ`. -/
noncomputable abbrev h310_eb (i : Fin 1 ⊕ Fin 1) : Vec 1 := EuclideanSpace.single i (1 : ℝ)

lemma h310_sum_inner_single (b : Vec 1) : ∑ i, (inner ℝ (h310_eb i) b) • h310_eb i = b := by
  have := (EuclideanSpace.basisFun (Fin 1 ⊕ Fin 1) ℝ).sum_repr' b
  simpa [h310_eb] using this

/-- `j0` as a continuous linear map. -/
noncomputable def h310_j0L : V 1 →L[ℝ] V 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := j0
      map_add' := fun u v => by funext k; simp only [j0, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun a v => by
        funext k; simp only [j0, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def h310_omegaL : V 1 →L[ℝ] V 1 →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp h310_j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ) k)

lemma h310_omegaL_apply (u v : V 1) : h310_omegaL u v = omega0 u v := by
  simp [h310_omegaL, omega0, dot, ContinuousLinearMap.sum_apply, h310_j0L]

/-- Coordinates of `w` in the frame map `Zt`: `Σᵢ ω₀(Zt(-J₀ eᵢ), w) eᵢ`. -/
noncomputable def h310_pull (Zt : Vec 1 →L[ℝ] V 1) (w : V 1) : Vec 1 :=
  ∑ i, omega0 (Zt (-(h310_mE (J₀ 1) (h310_eb i)))) w • h310_eb i

lemma h310_pull_left (Zt : Vec 1 →L[ℝ] V 1)
    (hω : ∀ a b, omega0 (Zt a) (Zt b) = inner ℝ (Matrix.toEuclideanLin (J₀ 1) a) b)
    (b : Vec 1) : h310_pull Zt (Zt b) = b := by
  simp only [h310_pull, hω]
  conv_rhs => rw [← h310_sum_inner_single b]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show Matrix.toEuclideanLin (J₀ 1) (-(h310_mE (J₀ 1) (h310_eb i))) =
    h310_mE (J₀ 1) (-(h310_mE (J₀ 1) (h310_eb i))) from rfl, map_neg, h310_mE_JJ, neg_neg]

lemma h310_inj (Zt : Vec 1 →L[ℝ] V 1)
    (hω : ∀ a b, omega0 (Zt a) (Zt b) = inner ℝ (Matrix.toEuclideanLin (J₀ 1) a) b)
    {a b : Vec 1} (h : Zt a = Zt b) : a = b := by
  rw [← h310_pull_left Zt hω a, h, h310_pull_left Zt hω b]

section
variable {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
  {Z : ℝ → Vec 1 →L[ℝ] V 1}

lemma h310_pull_contDiff (hZ : IsUnitaryXiFrame J P Z) {v : ℝ → V 1}
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun t => h310_pull (Z t) (v t)) := by
  unfold h310_pull
  refine ContDiff.sum (fun i _ => ?_)
  have h1 : ContDiff ℝ ∞ (fun t => omega0 (Z t (-(h310_mE (J₀ 1) (h310_eb i)))) (v t)) := by
    simp_rw [← h310_omegaL_apply]
    exact (h310_omegaL.contDiff.comp (hZ.1.clm_apply contDiff_const)).clm_apply hv
  exact h1.smul contDiff_const

lemma h310_pull_right (hZ : IsUnitaryXiFrame J P Z) {v : ℝ → V 1} (hv : IsXiLoop P v)
    (t : ℝ) : Z t (h310_pull (Z t) (v t)) = v t := by
  obtain ⟨a, ha⟩ := (hZ.2.2 t).2.1 (v t) (hv.2.2 t)
  rw [← ha, h310_pull_left _ (hZ.2.2 t).2.2.2]

lemma h310_pull_isLoop (hZ : IsUnitaryXiFrame J P Z) {v : ℝ → V 1} (hv : IsXiLoop P v) :
    ContDiff ℝ ∞ (fun t => h310_pull (Z t) (v t)) ∧
      Function.Periodic (fun t => h310_pull (Z t) (v t)) 1 := by
  refine ⟨h310_pull_contDiff hZ hv.1, fun t => ?_⟩
  show h310_pull (Z (t + 1)) (v (t + 1)) = h310_pull (Z t) (v t)
  rw [hZ.2.1 t, hv.2.1 t]

variable {Sinf : ℝ → Mat 1}
  (hA : ∀ η : ℝ → Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (J₀ 1) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
include hA

lemma h310_push (hZ : IsUnitaryXiFrame J P Z) {μ : ℝ} {e : ℝ → Vec 1}
    (he : IsLoopEigen Sinf μ e) : IsAsymptoticEigen J P μ (fun t => Z t (e t)) := by
  obtain ⟨hes, hep, ⟨t₀, ht₀⟩, heq⟩ := he
  refine ⟨⟨hZ.1.clm_apply hes, fun t => ?_, fun t => (hZ.2.2 t).1 _⟩, ⟨t₀, fun h => ht₀ ?_⟩,
    fun t => ?_⟩
  · show Z (t + 1) (e (t + 1)) = Z t (e t)
    rw [hZ.2.1 t, hep t]
  · exact h310_inj (Z t₀) (hZ.2.2 t₀).2.2.2 (h.trans (map_zero _).symm)
  · rw [hA e hes hep t, heq t, map_smul]

lemma h310_pullEigen (hZ : IsUnitaryXiFrame J P Z) {μ : ℝ} {v : ℝ → V 1}
    (hv : IsAsymptoticEigen J P μ v) :
    IsLoopEigen Sinf μ (fun t => h310_pull (Z t) (v t)) := by
  obtain ⟨hvl, ⟨t₀, ht₀⟩, heq⟩ := hv
  obtain ⟨hs, hp⟩ := h310_pull_isLoop hZ hvl
  have hfun : (fun t => Z t (h310_pull (Z t) (v t))) = v :=
    funext fun t => h310_pull_right hZ hvl t
  refine ⟨hs, hp, ⟨t₀, fun h => ht₀ ?_⟩, fun t => ?_⟩
  · rw [← h310_pull_right hZ hvl t₀]; simp only at h; rw [h, map_zero]
  · refine h310_inj (Z t) (hZ.2.2 t).2.2.2 ?_
    rw [← hA _ hs hp t, hfun, heq t, map_smul, h310_pull_right hZ hvl t]

theorem hasEigenWind_iff_hasLoopEigenWind_aux (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → Vec 1, Continuous ζ → Function.Periodic ζ 1 →
      (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
        (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (μ : ℝ) (k : ℤ) :
    HasEigenWind J P μ k ↔ HasLoopEigenWind Sinf μ k := by
  have hw : ∀ e, IsLoopEigen Sinf μ e →
      (HasXiLoopWind P (fun t => Z t (e t)) k ↔ HasLoopWind (fun t => vecToC (e t)) k) :=
    fun e he => hwind e he.1.continuous he.2.1
      (isLoopEigen_ne_zero_hasLoopEigenWind Sinf hSinf hSinf' μ e he).1 k
  constructor
  · rintro ⟨⟨v, hv⟩, hall⟩
    exact ⟨⟨_, h310_pullEigen hA hZ hv⟩, fun e he => (hw e he).1 (hall _ (h310_push hA hZ he))⟩
  · rintro ⟨⟨e, he⟩, hall⟩
    refine ⟨⟨_, h310_push hA hZ he⟩, fun v hv => ?_⟩
    have he' := h310_pullEigen hA hZ hv
    have := (hw _ he').2 (hall _ he')
    have hfun : (fun t => Z t (h310_pull (Z t) (v t))) = v :=
      funext fun t => h310_pull_right hZ hv.1 t
    rwa [hfun] at this

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1)
    (P : ReebOrbit H) (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
      (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
        (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (μ : ℝ) (k : ℤ) :
    HasEigenWind J P μ k ↔ HasLoopEigenWind Sinf μ k :=
  hasEigenWind_iff_hasLoopEigenWind_aux hA hZ hwind hSinf hSinf' μ k
