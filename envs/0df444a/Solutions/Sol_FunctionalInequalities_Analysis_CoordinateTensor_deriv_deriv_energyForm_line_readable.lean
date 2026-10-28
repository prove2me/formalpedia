-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:28.098094+00:00
-- url     : https://prove2.me/submissions/015f7a09-7812-4fc1-9fef-7eee4e4e324f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_actOn_mul_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actOn_left_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actSum_actSum_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_sum_two_readable
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_two_slot_sum_readable

section
noncomputable section
open Matrix
section S3Bf3ASlotActionAlgebra
section
variable {n r : ℕ}
/-- `⟨T, (M²)^{(s)} T⟩ = |M^{(s)} T|²` for symmetric `M`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_mul_self (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T : (Fin r → Fin n) → ℝ) : inner T (actOn (M * M) s T) = inner (actOn M s T) (actOn M s T) := by
  rw [actOn_mul_readable]
  exact (inner_actOn_left_readable M hM s T (actOn M s T)).symm
end
end S3Bf3ASlotActionAlgebra
end
end

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.delta_product (J K : Fin r → Fin n) :
    (∏ s, if J s = K s then (1 : ℝ) else 0) =
      if J = K then 1 else 0 := by
  classical
  by_cases h : J = K
  · subst K
    simp
  · rw [if_neg h]
    have hex : ∃ s, J s ≠ K s := by
      by_contra hnone
      apply h
      funext s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)
end
section S3Bf2EnergyFormFirstOrder
section
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_line {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R] (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 : R) + t • H) H 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : R))
  have hi :
      HasFDerivAt Ring.inverse
        (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R))
        ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero, inv_one, Units.val_one] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Rˣ))
  have hc := hi.comp_hasDerivAt 0 hl
  have heq :
      (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R)) H = -H := by
    change -((1 : R) * H * 1) = -H
    rw [one_mul, mul_one]
  simpa only [Function.comp_def] using hc.congr_deriv heq
/-- The entries of `(1 + εH)⁻¹` have derivative `−⟪e_i, H e_k⟫` at `ε = 0`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (i k : Fin n) :
    HasDerivAt (fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫) 0 := by
  have hi :
      HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
    convert inverse_line H using 1
  have hv := hi.clm_apply
    (hasDerivAt_const (0 : ℝ) (EuclideanSpace.basisFun (Fin n) ℝ k))
  have h := (hasDerivAt_const (0 : ℝ)
    (EuclideanSpace.basisFun (Fin n) ℝ i)).inner ℝ hv
  simpa using h
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul {f g : ℝ → ℝ} {df dg x : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t => f t * g t) (df * g x + f x * dg) x := by
  convert hf.mul hg using 1 <;> rfl
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, df i) x := by
  have h := HasDerivAt.sum hf
  have he : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  convert h using 1
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t)
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * df i) x := by
  have h := HasDerivAt.finsetProd hf
  have he : (∏ i ∈ s, f i) = (fun t => ∏ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  simp only [smul_eq_mul] at h
  convert h using 1
end
end S3Bf2EnergyFormFirstOrder
section S3Bf3B1SecondOrderHelpers
section
variable {n r : ℕ}
section StructuredSpace
variable {R : Type*}
variable [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_line_at_unit
    (H : R) (t : ℝ) (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => Ring.inverse (1 + x • H))
      (-(Ring.inverse (1 + t • H) * H * Ring.inverse (1 + t • H))) t := by
  have hl : HasDerivAt (fun x : ℝ => (1 : R) + x • H) H t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const H).const_add (1 : R)
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) ht.unit
  rw [ht.unit_spec] at hi
  have hc := hi.comp_hasDerivAt t hl
  simpa only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit, ht.unit_spec] using hc
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_line_at_zero (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hu : IsUnit ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero] using (isUnit_one : IsUnit (1 : R))
  simpa only [zero_smul, add_zero, Ring.inverse_one, one_mul, mul_one] using
    inverse_line_at_unit H 0 hu
end StructuredSpace
section NormedSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_entry_at_unit
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) (t : ℝ)
    (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => L (Ring.inverse (1 + x • H) v))
      (-L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) t := by
  have h := inverse_line_at_unit H t ht
  simpa only [Function.comp_def, _root_.neg_apply, mul_apply_eq_comp,
    map_zero, add_zero, map_neg] using
    L.hasFDerivAt.comp_hasDerivAt t (h.clm_apply (hasDerivAt_const t v))
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inverse_entry_second
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) :
    HasDerivAt (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v))
      (2 * L (H (H v))) 0 := by
  have hR := inverse_line_at_zero H
  have hv := hR.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hHv := (hasDerivAt_const (0 : ℝ) H).clm_apply hv
  have hboth := hR.clm_apply hHv
  have hh := (-L).hasFDerivAt.comp_hasDerivAt 0 hboth
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v))))
        (2 * L (H (H v))) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero, Ring.inverse_one,
      one_apply_eq_self, _root_.neg_apply, _root_.zero_apply, map_zero,
      zero_add, map_neg, map_add, neg_add, neg_neg, two_mul] using hh
  have hopen : {t : ℝ | IsUnit (1 + t • H)} ∈ nhds (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => (1 : E →L[ℝ] E) + t • H) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply (Units.isOpen.preimage hc).mem_nhds
    change IsUnit ((1 : E →L[ℝ] E) + (0 : ℝ) • H)
    simpa only [zero_smul, add_zero] using
      (isUnit_one : IsUnit (1 : E →L[ℝ] E))
  have heq :
      (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v)) =ᶠ[nhds 0]
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) := by
    filter_upwards [hopen] with t ht
    exact (inverse_entry_at_unit H L v t ht).deriv
  exact hd.congr_of_eventuallyEq heq
end NormedSpace
/-- The entries of `(1 + εH)⁻¹` are differentiable near `ε = 0` with derivative
`−⟪e_i, (1+εH)⁻¹ H (1+εH)⁻¹ e_k⟫`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add_of_isUnit
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) {ε : ℝ}
    (hε : IsUnit (1 + ε • H)) :
    HasDerivAt (fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (H (Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)))⟫) ε := by
  exact inverse_entry_at_unit H
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (EuclideanSpace.basisFun (Fin n) ℝ k) ε hε
/-- The second derivative of the entries of `(1 + εH)⁻¹` at `ε = 0` is `2⟪e_i, H² e_k⟫`. -/
theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_deriv_inner_ringInverse_one_add
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) :
    HasDerivAt (deriv fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (2 * ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (H (EuclideanSpace.basisFun (Fin n) ℝ k))⟫) 0 := by
  exact inverse_entry_second H
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (EuclideanSpace.basisFun (Fin n) ℝ k)
end
end S3Bf3B1SecondOrderHelpers
section S3Bf3B2SecondOrderCore
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_add {f g : ℝ → ℝ} {df dg x : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t => f t + g t) (df + dg) x :=
  hf.add hg
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_const_mul {f : ℝ → ℝ} {df x : ℝ} (c : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => c * f t) (c * df) x :=
  hf.const_mul c
private lemma FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul_const {f : ℝ → ℝ} {df x : ℝ} (c : ℝ)
    (hf : HasDerivAt f df x) :
    HasDerivAt (fun t => f t * c) (df * c) x :=
  hf.mul_const c
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inner_comm' (T S : (Fin r → Fin n) → ℝ) : inner T S = inner S T := by
  unfold inner
  apply Finset.sum_congr rfl
  intro J _
  exact mul_comm _ _
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_eq_sum (N : Matrix (Fin n) (Fin n) ℝ) (T S : (Fin r → Fin n) → ℝ) :
    inner T (actSum N S) = ∑ s, inner T (actOn N s S) := by
  unfold inner actSum
  simp only [Finset.mul_sum]
  exact Finset.sum_comm
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_left (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (T S : (Fin r → Fin n) → ℝ) : inner (actSum M T) S = inner T (actSum M S) := by
  rw [inner_comm', inner_actSum_eq_sum, inner_actSum_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [inner_comm']
  exact inner_actOn_left_readable M hM s T S
private lemma FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix_isSymm (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H) : (stdMatrix H).IsSymm := by
  have hsym : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪H x, y⟫ = ⟪x, H y⟫ :=
    fun x y => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH) x y
  apply Matrix.IsSymm.ext
  intro i k
  change ⟪EuclideanSpace.basisFun (Fin n) ℝ k, H (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ =
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  rw [← hsym, real_inner_comm]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.inner_H_H (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H) (i k : Fin n) :
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (H (EuclideanSpace.basisFun (Fin n) ℝ k))⟫ =
      (stdMatrix H * stdMatrix H) i k := by
  have hsym : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪H x, y⟫ = ⟪x, H y⟫ :=
    fun x y => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH) x y
  rw [Matrix.mul_apply, ← hsym (EuclideanSpace.basisFun (Fin n) ℝ i) (H (EuclideanSpace.basisFun (Fin n) ℝ k)),
    ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner
      (H (EuclideanSpace.basisFun (Fin n) ℝ i)) (H (EuclideanSpace.basisFun (Fin n) ℝ k))]
  apply Finset.sum_congr rfl
  intro j _
  change ⟪H (EuclideanSpace.basisFun (Fin n) ℝ i), EuclideanSpace.basisFun (Fin n) ℝ j⟫ *
      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫ =
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ *
      ⟪EuclideanSpace.basisFun (Fin n) ℝ j, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  rw [hsym]
set_option maxHeartbeats 1600000 in
/-- **BKL (88), second order, along the line**: for symmetric `H`,
`d²/dε² F(1 + εH, T + εX)|₀ = 2 (|X|² − 2⟨X, Σ_H T⟩ + ½|Σ_H T|² + ½ Σ_s |H^{(s)} T|²)`. -/
theorem solution (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    deriv (deriv fun ε : ℝ => FunctionalInequalities.Analysis.CoordinateTensor.energyForm (1 + ε • H) (T + ε • X)) 0 =
      2 * (FunctionalInequalities.Analysis.CoordinateTensor.inner X X - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner X (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T)
        + (1 / 2 : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T)
        + (1 / 2 : ℝ) * ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T)) := by
  have hM : (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H).IsSymm := FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix_isSymm H hH
  let a (i k : Fin n) (t : ℝ) : ℝ :=
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Ring.inverse (1 + t • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  have hz :
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) +
        (0 : ℝ) • H = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    change v + (0 : ℝ) • H v = v
    simp
  have a0 (i k : Fin n) : a i k 0 = if i = k then 1 else 0 := by
    unfold a
    rw [hz, Ring.inverse_one]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i k
  have ha0 (i k : Fin n) : HasDerivAt (a i k) (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H i k) 0 :=
    FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add H i k
  have da0 (i k : Fin n) : deriv (a i k) 0 = -FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H i k := (ha0 i k).deriv
  have hda (i k : Fin n) :
      HasDerivAt (deriv (a i k)) (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) i k) 0 := by
    rw [← FunctionalInequalities.Analysis.CoordinateTensor.inner_H_H H hH i k]
    exact FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_deriv_inner_ringInverse_one_add H i k
  have hopen : {t : ℝ | IsUnit (1 + t • H)} ∈ nhds (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ =>
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + t • H) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply (Units.isOpen.preimage hc).mem_nhds
    change IsUnit ((1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + (0 : ℝ) • H)
    rw [hz]
    exact isUnit_one
  have hT (J : Fin r → Fin n) (t : ℝ) :
      HasDerivAt (fun x : ℝ => T J + x * X J) (X J) t := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (X J)).const_add (T J))
  -- the two pieces of the first derivative
  let A (J K : Fin r → Fin n) (t : ℝ) : ℝ :=
    (X J * (T K + t * X K) + (T J + t * X J) * X K) * ∏ s, a (J s) (K s) t
  let B (J K : Fin r → Fin n) (t : ℝ) : ℝ :=
    (T J + t * X J) * (T K + t * X K) *
      ∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) t) * deriv (a (J s) (K s)) t
  -- first derivative at every unit point
  have hD1 (t : ℝ) (ht : IsUnit (1 + t • H)) :
      HasDerivAt (fun ε : ℝ => FunctionalInequalities.Analysis.CoordinateTensor.energyForm (1 + ε • H) (T + ε • X))
        (∑ J, ∑ K, (A J K t + B J K t)) t := by
    have ha (i k : Fin n) : HasDerivAt (a i k) (deriv (a i k) t) t :=
      (FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_inner_ringInverse_one_add_of_isUnit H i k ht).differentiableAt.hasDerivAt
    have hp (J K : Fin r → Fin n) :
        HasDerivAt (fun x => ∏ s, a (J s) (K s) x)
          (∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) t) * deriv (a (J s) (K s)) t) t :=
      FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_prod Finset.univ (fun s x => a (J s) (K s) x)
        (fun s => deriv (a (J s) (K s)) t) t (fun s _ => ha (J s) (K s))
    have hraw :
        HasDerivAt
          (fun x : ℝ => ∑ J, ∑ K,
            (T J + x * X J) * (T K + x * X K) * ∏ s, a (J s) (K s) x)
          (∑ J, ∑ K, (A J K t + B J K t)) t := by
      apply FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum
      intro J _
      apply FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum
      intro K _
      exact FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul (hT J t) (hT K t)) (hp J K)
    convert hraw using 1
    rfl
  have heq :
      (deriv fun ε : ℝ => FunctionalInequalities.Analysis.CoordinateTensor.energyForm (1 + ε • H) (T + ε • X)) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ => ∑ J, ∑ K, (A J K t + B J K t)) := by
    filter_upwards [hopen] with t ht
    exact (hD1 t ht).deriv
  -- second derivative at `0`
  let P (J K : Fin r → Fin n) : ℝ :=
    ∏ s, if J s = K s then (1 : ℝ) else 0
  let Q (J K : Fin r → Fin n) : ℝ :=
    ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
      (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s))
  let R (J K : Fin r → Fin n) : ℝ :=
    ∑ s, ((∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u))) * (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s)) +
      (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
        (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)))
  let dA (J K : Fin r → Fin n) : ℝ :=
    (X J * X K + X J * X K) * P J K + (X J * T K + T J * X K) * Q J K
  let dB (J K : Fin r → Fin n) : ℝ :=
    (X J * T K + T J * X K) * Q J K + T J * T K * R J K
  have hp0 (J K : Fin r → Fin n) :
      HasDerivAt (fun x => ∏ s, a (J s) (K s) x) (Q J K) 0 := by
    have h := FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_prod Finset.univ (fun s x => a (J s) (K s) x)
      (fun s => -FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s)) 0 (fun s _ => ha0 (J s) (K s))
    apply h.congr_deriv
    simp only [a0, Q]
  have hq0 (J K : Fin r → Fin n) :
      HasDerivAt
        (fun x => ∑ s, (∏ u ∈ Finset.univ.erase s, a (J u) (K u) x) * deriv (a (J s) (K s)) x)
        (R J K) 0 := by
    have h := FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum Finset.univ
      (fun s x => (∏ u ∈ Finset.univ.erase s, a (J u) (K u) x) * deriv (a (J s) (K s)) x)
      (fun s => (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, a (J v) (K v) 0) *
            (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u))) * deriv (a (J s) (K s)) 0 +
        (∏ u ∈ Finset.univ.erase s, a (J u) (K u) 0) *
          (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s))) 0
      (fun s _ => FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul
        (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_prod (Finset.univ.erase s) (fun u x => a (J u) (K u) x)
          (fun u => -FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u)) 0 (fun u _ => ha0 (J u) (K u)))
        (hda (J s) (K s)))
    apply h.congr_deriv
    simp only [a0, da0, R]
  have hA (J K : Fin r → Fin n) : HasDerivAt (fun t => A J K t) (dA J K) 0 := by
    have h := FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul
      (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_add (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_const_mul (X J) (hT K 0)) (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul_const (X K) (hT J 0)))
      (hp0 J K)
    apply h.congr_deriv
    simp only [a0, dA, P, zero_mul, add_zero]
  have hB (J K : Fin r → Fin n) : HasDerivAt (fun t => B J K t) (dB J K) 0 := by
    have h := FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul (FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_mul (hT J 0) (hT K 0)) (hq0 J K)
    apply h.congr_deriv
    simp only [a0, da0, dB, Q, zero_mul, add_zero]
  have hD2 :
      HasDerivAt (fun t : ℝ => ∑ J, ∑ K, (A J K t + B J K t))
        (∑ J, ∑ K, (dA J K + dB J K)) 0 := by
    apply FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum
    intro J _
    apply FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_sum
    intro K _
    exact FunctionalInequalities.Analysis.CoordinateTensor.real_deriv_add (hA J K) (hB J K)
  rw [heq.deriv_eq, hD2.deriv]
  -- the algebra
  have h1 : (∑ J, ∑ K, (X J * X K + X J * X K) * P J K) = 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner X X := by
    calc
      (∑ J, ∑ K, (X J * X K + X J * X K) * P J K) =
          ∑ J, (X J * X J + X J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        simp [P, FunctionalInequalities.Analysis.CoordinateTensor.delta_product, mul_ite]
      _ = 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner X X := by
        unfold FunctionalInequalities.Analysis.CoordinateTensor.inner
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J _
        ring
  have h2 : (∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) =
      -(2 * FunctionalInequalities.Analysis.CoordinateTensor.inner X (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T)) := by
    have e1 : (∑ J, ∑ K, X J * T K * Q J K) = -FunctionalInequalities.Analysis.CoordinateTensor.inner X (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) :=
      FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_readable X T (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H)
    have e2 : (∑ J, ∑ K, T J * X K * Q J K) = -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) X) :=
      FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_readable T X (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H)
    have e3 : FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) X) = FunctionalInequalities.Analysis.CoordinateTensor.inner X (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) := by
      rw [← FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_left _ hM T X, FunctionalInequalities.Analysis.CoordinateTensor.inner_comm']
    calc
      (∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) =
          ∑ J, ∑ K, (X J * T K * Q J K + T J * X K * Q J K) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = (∑ J, ∑ K, X J * T K * Q J K) + ∑ J, ∑ K, T J * X K * Q J K := by
        simp only [Finset.sum_add_distrib]
      _ = -(2 * FunctionalInequalities.Analysis.CoordinateTensor.inner X (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T)) := by
        rw [e1, e2, e3]
        ring
  have h3a :
      (∑ J, ∑ K, T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
          (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
            (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u))) * (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s)))) =
        ∑ s, ∑ u ∈ Finset.univ.erase s,
          FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) u T)) :=
    FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_readable T (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H)
  have h3b :
      (∑ J, ∑ K, T J * T K * (∑ s,
          (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)))) =
        2 * ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) := by
    have e := FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_readable T T (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H)
    have hpt (J K : Fin r → Fin n) :
        (∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s))) =
          -2 * ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (-(FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    calc
      (∑ J, ∑ K, T J * T K * (∑ s,
          (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
            (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)))) =
          ∑ J, ∑ K, -2 * (T J * T K * (∑ s,
            (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
              (-(FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)))) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        rw [hpt]
        ring
      _ = -2 * ∑ J, ∑ K, T J * T K * (∑ s,
            (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
              (-(FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = -2 * -FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actSum (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) T) := by
        rw [e]
      _ = 2 * ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) := by
        rw [FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_eq_sum,
          Finset.sum_congr rfl (fun s _ => FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_mul_self (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) hM s T)]
        ring
  have h3 : (∑ J, ∑ K, T J * T K * R J K) =
      (∑ s, ∑ u ∈ Finset.univ.erase s,
        FunctionalInequalities.Analysis.CoordinateTensor.inner T (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) u T))) +
      2 * ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) s T) := by
    calc
      (∑ J, ∑ K, T J * T K * R J K) =
          ∑ J, ∑ K, (T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u))) * (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s))) +
            T J * T K * (∑ s,
              (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
                (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s)))) := by
        apply Finset.sum_congr rfl
        intro J _
        apply Finset.sum_congr rfl
        intro K _
        simp only [R, Finset.sum_add_distrib, mul_add]
      _ = (∑ J, ∑ K, T J * T K * (∑ s, (∑ u ∈ Finset.univ.erase s,
              (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
                (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J u) (K u))) * (-FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H (J s) (K s)))) +
          ∑ J, ∑ K, T J * T K * (∑ s,
              (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
                (2 * (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H * FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) (J s) (K s))) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        rw [h3a, h3b]
  have hsplit : (∑ J, ∑ K, (dA J K + dB J K)) =
      ((∑ J, ∑ K, (X J * X K + X J * X K) * P J K) +
        ∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) +
      ((∑ J, ∑ K, (X J * T K + T J * X K) * Q J K) +
        ∑ J, ∑ K, T J * T K * R J K) := by
    simp only [dA, dB, Finset.sum_add_distrib]
  rw [hsplit, h1, h2, h3, FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_readable (FunctionalInequalities.Analysis.CoordinateTensor.stdMatrix H) hM T]
  ring
