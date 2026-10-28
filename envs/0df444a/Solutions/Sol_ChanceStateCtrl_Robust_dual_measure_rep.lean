-- Prove2me | solution 1 for ChanceStateCtrl.Robust.dual_measure_rep
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:42:12.697327+00:00
-- url     : https://prove2.me/submissions/60e5af2e-8ce8-41a6-a017-e727a5996fcd

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory Filter Topology
open scoped CompactlySupported InnerProductSpace
open ChanceStateCtrl.Robust

/-- Riesz–Markov–Kakutani on a compact space, for a positive linear functional. -/
private lemma rmk_compact_lin {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ z : C(X, ℝ), (∀ q, 0 ≤ z q) → 0 ≤ Λ z) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ z : C(X, ℝ), ∫ q, z q ∂μ = Λ z := by
  let Lc : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => Λ (f : C(X, ℝ))
      map_add' := fun f g => by
        rw [← map_add]; rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← smul_eq_mul, ← map_smul]; rfl }
  let Λc : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Lc (fun f hf => hpos _ (fun q => hf q))
  refine ⟨RealRMK.rieszMeasure Λc, inferInstance, fun z => ?_⟩
  have := RealRMK.integral_rieszMeasure Λc (CompactlySupportedContinuousMap.continuousMapEquiv z)
  exact this.trans (congrArg Λ (ContinuousMap.ext fun _ => rfl))

/-- Every continuous linear functional on `C(X)` (`X` compact) is dominated on the positive
cone by a positive linear functional (Hahn–Banach / Mazur–Orlicz). -/
private lemma pos_dominant {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (Λ : StrongDual ℝ C(X, ℝ)) :
    ∃ L : C(X, ℝ) →ₗ[ℝ] ℝ, (∀ g : C(X, ℝ), (∀ q, 0 ≤ g q) → 0 ≤ L g) ∧
      (∀ g : C(X, ℝ), (∀ q, 0 ≤ g q) → Λ g ≤ L g) := by
  set c := ‖Λ‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg Λ
  have hbdd : ∀ g : C(X, ℝ), BddAbove (Set.range fun q => max (g q) 0) := fun g =>
    ⟨‖g‖, by
      rintro _ ⟨q, rfl⟩
      exact max_le ((le_abs_self _).trans (g.norm_coe_le_norm q)) (norm_nonneg g)⟩
  let S : C(X, ℝ) → ℝ := fun g => ⨆ q, max (g q) 0
  have hS0 : ∀ g, 0 ≤ S g := fun g =>
    (le_max_right (g (Classical.arbitrary X)) 0).trans (le_ciSup (hbdd g) _)
  have hSle : ∀ g q, max (g q) 0 ≤ S g := fun g q => le_ciSup (hbdd g) q
  have hShom : ∀ t : ℝ, 0 ≤ t → ∀ g, S (t • g) = t * S g := by
    intro t ht g
    simp only [S, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Real.mul_iSup_of_nonneg ht]
    congr 1; ext q
    rw [mul_max_of_nonneg _ _ ht, mul_zero]
  have hSadd : ∀ a b, S (a + b) ≤ S a + S b := by
    intro a b
    refine ciSup_le fun q => ?_
    have h1 := hSle a q
    have h2 := hSle b q
    simp only [ContinuousMap.add_apply]
    refine max_le ?_ (add_nonneg (hS0 a) (hS0 b))
    have := le_max_left (a q) 0
    have := le_max_left (b q) 0
    linarith
  let N : C(X, ℝ) → ℝ := fun g => c * S g
  let P := {g : C(X, ℝ) // ∀ q, 0 ≤ g q}
  haveI : Nonempty P := ⟨⟨0, fun q => le_rfl⟩⟩
  have hlow : ∀ x (g : P), -(c * ‖x‖) ≤ N (x + g.1) - Λ g.1 := by
    intro x g
    have hg : ‖g.1‖ ≤ S (x + g.1) + ‖x‖ := by
      refine (ContinuousMap.norm_le _ (add_nonneg (hS0 _) (norm_nonneg _))).2 fun q => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (g.2 q)]
      have h1 := hSle (x + g.1) q
      have h2 := le_max_left ((x + g.1) q) 0
      have h34 := abs_le.1 (show |x q| ≤ ‖x‖ from x.norm_coe_le_norm q)
      simp only [ContinuousMap.add_apply] at h1 h2
      linarith [h34.1, h34.2]
    have hΛ : Λ g.1 ≤ c * ‖g.1‖ := (le_abs_self _).trans (Λ.le_opNorm g.1)
    have := mul_le_mul_of_nonneg_left hg hc0
    simp only [N]
    nlinarith
  let N' : C(X, ℝ) → ℝ := fun x => ⨅ g : P, (N (x + g.1) - Λ g.1)
  have hbddN' : ∀ x, BddBelow (Set.range fun g : P => N (x + g.1) - Λ g.1) := fun x =>
    ⟨-(c * ‖x‖), by rintro _ ⟨g, rfl⟩; exact hlow x g⟩
  have hN'le : ∀ x (g : P), N' x ≤ N (x + g.1) - Λ g.1 := fun x g => ciInf_le (hbddN' x) g
  have hNhom : ∀ t : ℝ, 0 ≤ t → ∀ g, N (t • g) = t * N g := by
    intro t ht g; simp only [N]; rw [hShom t ht]; ring
  have hN'hom : ∀ t : ℝ, 0 < t → ∀ x, N' (t • x) = t * N' x := by
    intro t ht x
    apply le_antisymm
    · -- `N' (t x) ≤ t (N(x+g) - Λ g)` for every `g`
      have : N' (t • x) / t ≤ N' x := by
        refine le_ciInf fun g => ?_
        rw [div_le_iff₀ ht]
        have hg' : ∀ q, 0 ≤ (t • g.1) q := fun q => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul]; exact mul_nonneg ht.le (g.2 q)
        have := hN'le (t • x) ⟨t • g.1, hg'⟩
        simp only at this
        rw [← smul_add, hNhom t ht.le, map_smul, smul_eq_mul] at this
        linarith
      rw [div_le_iff₀ ht] at this; linarith
    · refine le_ciInf fun g => ?_
      have hg' : ∀ q, 0 ≤ (t⁻¹ • g.1) q := fun q => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 ht.le) (g.2 q)
      have := hN'le x ⟨t⁻¹ • g.1, hg'⟩
      simp only at this
      have e : t • x + g.1 = t • (x + t⁻¹ • g.1) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      rw [e, hNhom t ht.le]
      have e2 : Λ g.1 = t * Λ (t⁻¹ • g.1) := by
        rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
      rw [e2]
      nlinarith
  have hN'add : ∀ x y, N' (x + y) ≤ N' x + N' y := by
    intro x y
    have : N' (x + y) - N' y ≤ N' x := by
      refine le_ciInf fun g1 => ?_
      have : N' (x + y) - (N (x + g1.1) - Λ g1.1) ≤ N' y := by
        refine le_ciInf fun g2 => ?_
        have hg : ∀ q, 0 ≤ (g1.1 + g2.1) q := fun q => by
          simp only [ContinuousMap.add_apply]; exact add_nonneg (g1.2 q) (g2.2 q)
        have h1 := hN'le (x + y) ⟨g1.1 + g2.1, hg⟩
        simp only at h1
        have h2 : x + y + (g1.1 + g2.1) = (x + g1.1) + (y + g2.1) := by abel
        rw [h2, map_add] at h1
        have h3 : N ((x + g1.1) + (y + g2.1)) ≤ N (x + g1.1) + N (y + g2.1) := by
          simp only [N]; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (hSadd _ _) hc0
        linarith
      linarith
    linarith
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    (⟨⊥, 0⟩ : C(X, ℝ) →ₗ.[ℝ] ℝ) N' hN'hom hN'add
    (fun x => by
      have hx : (x : C(X, ℝ)) = 0 := (Submodule.mem_bot ℝ).1 x.2
      show (0 : (⊥ : Submodule ℝ C(X, ℝ)) →ₗ[ℝ] ℝ) x ≤ N' x
      rw [LinearMap.zero_apply, hx]
      refine le_ciInf fun g => ?_
      have := hlow 0 g
      simpa using this)
  refine ⟨L, fun g hg => ?_, fun g hg => ?_⟩
  · have h1 := (hL (-g)).trans (hN'le (-g) ⟨0, fun q => le_rfl⟩)
    simp only [add_zero, map_zero, sub_zero, map_neg] at h1
    have h2 : S (-g) = 0 := le_antisymm (ciSup_le fun q => max_le (by simp; exact hg q) le_rfl)
      (hS0 _)
    simp only [N, h2, mul_zero] at h1
    linarith
  · have h1 := (hL (-g)).trans (hN'le (-g) ⟨g, hg⟩)
    simp only [neg_add_cancel, map_neg] at h1
    have h2 : N 0 = 0 := by
      have := hNhom 0 le_rfl 0; simpa using this
    rw [h2] at h1
    linarith

private lemma signed_rmk {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Λ : StrongDual ℝ C(X, ℝ)) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ ⟂ₘ ν ∧
      ∀ r : C(X, ℝ), Λ r = ∫ q, r q ∂μ - ∫ q, r q ∂ν := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨0, 0, inferInstance, inferInstance, Measure.MutuallySingular.zero_left, fun r => ?_⟩
    have : r = 0 := ContinuousMap.ext fun x => isEmptyElim x
    simp [this]
  obtain ⟨L, hL0, hLΛ⟩ := pos_dominant Λ
  obtain ⟨μ1, h1, hμ1⟩ := rmk_compact_lin L hL0
  obtain ⟨μ2, h2, hμ2⟩ := rmk_compact_lin (L - Λ.toLinearMap) (fun g hg => by
    have := hLΛ g hg
    simp only [LinearMap.sub_apply, ContinuousLinearMap.coe_coe]; linarith)
  have hrep : ∀ r : C(X, ℝ), Λ r = ∫ q, r q ∂μ1 - ∫ q, r q ∂μ2 := by
    intro r; rw [hμ1, hμ2]; simp
  set s := μ1.toSignedMeasure - μ2.toSignedMeasure with hs
  set j := s.toJordanDecomposition with hj
  have hsum : j.posPart + μ2 = j.negPart + μ1 := by
    ext A hA
    have e := congrArg (fun t : MeasureTheory.SignedMeasure X => t A)
      (MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s)
    simp only [MeasureTheory.JordanDecomposition.toSignedMeasure] at e
    rw [VectorMeasure.sub_apply, VectorMeasure.sub_apply,
      Measure.toSignedMeasure_apply_measurable hA, Measure.toSignedMeasure_apply_measurable hA,
      Measure.toSignedMeasure_apply_measurable hA, Measure.toSignedMeasure_apply_measurable hA] at e
    rw [Measure.add_apply, Measure.add_apply,
      ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [measureReal_def] at e
    linarith
  refine ⟨j.posPart, j.negPart, inferInstance, inferInstance, j.mutuallySingular, fun r => ?_⟩
  have hi : ∀ (ν : Measure X) [IsFiniteMeasure ν], Integrable (fun q => r q) ν := fun ν _ =>
    r.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : ∫ q, r q ∂(j.posPart + μ2) = ∫ q, r q ∂(j.negPart + μ1) := by rw [hsum]
  rw [integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _)] at e
  rw [hrep]; linarith

theorem solution {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    [CompactSpace (closure D)] [CompactSpace Ξ]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (lamStar : StrongDual ℝ C(closure D × Ξ, ℝ)) :
    ∃ μ ν : Measure (closure D × Ξ), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ ⟂ₘ ν ∧
      (∀ r : C(closure D × Ξ, ℝ), lamStar r = ∫ q, r q ∂μ - ∫ q, r q ∂ν) ∧
      ∀ h : ChanceStateCtrl.PDE.L2 D, lamStar (AhatBhat Ainv h) = ∫ q, Ainv h q.1 ∂μ - ∫ q, Ainv h q.1 ∂ν := by
  obtain ⟨μ, ν, hμ, hν, hs, hrep⟩ := signed_rmk lamStar
  exact ⟨μ, ν, hμ, hν, hs, hrep, fun h => hrep (AhatBhat Ainv h)⟩
