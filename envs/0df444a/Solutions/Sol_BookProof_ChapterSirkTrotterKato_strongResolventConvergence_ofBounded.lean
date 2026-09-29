-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:38:39.072213+00:00
-- url     : https://prove2.me/submissions/504e2ecb-7d7e-4c80-9f26-ca8833634180

import Definitions.Def_ChapterSirkTrotterKatoGalerkin
-- Adapted from Leonardo Pedro, timepiece 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology Asymptotics
open scoped InnerProductSpace
namespace SirkBoundedResolventAux
open BookProof.HermiteGalerkin BookProof.ChapterSirkTrotterKato BookProof.ChapterStoneResolvent
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
private theorem norm_sub_smul_ge (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (z : ℂ) (u : F) :
    |z.im| * ‖u‖ ≤ ‖(algebraMap ℂ (F →L[ℂ] F) z - T) u‖ := by
  have h : (inner ℂ (T u) u : ℂ) = inner ℂ u (T u) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) u u
  have hsym : (inner ℂ u (T u) : ℂ).im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [inner_conj_symm]
    exact h
  have happ : (algebraMap ℂ (F →L[ℂ] F) z - T) u = z • u - T u := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hinner : (inner ℂ u ((algebraMap ℂ (F →L[ℂ] F) z - T) u) : ℂ).im = z.im * ‖u‖ ^ 2 := by
    rw [happ, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.sub_im,
      hsym, sub_zero, Complex.mul_im]
    simp [← Complex.ofReal_pow]
  have hcs : |(inner ℂ u ((algebraMap ℂ (F →L[ℂ] F) z - T) u) : ℂ).im|
      ≤ ‖u‖ * ‖(algebraMap ℂ (F →L[ℂ] F) z - T) u‖ :=
    le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm _ _)
  rw [hinner] at hcs
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
  · simp [← h0]
  · rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖ ^ 2)] at hcs
    nlinarith [hcs, hpos]

private theorem isUnit_algebraMap_sub (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (algebraMap ℂ (F →L[ℂ] F) z - T) := by
  have hspec : z ∉ spectrum ℂ T := by
    intro hmem
    exact hz (by rw [← hT.spectrumRestricts.rightInvOn hmem]; simp)
  simpa [spectrum.mem_iff] using hspec

private theorem sub_resolvent_apply (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (w : F) : (algebraMap ℂ (F →L[ℂ] F) z - T) (resolvent T z w) = w := by
  have hmul : (algebraMap ℂ (F →L[ℂ] F) z - T) * resolvent T z = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_algebraMap_sub T hT hz)
  calc (algebraMap ℂ (F →L[ℂ] F) z - T) (resolvent T z w)
      = ((algebraMap ℂ (F →L[ℂ] F) z - T) * resolvent T z) w := rfl
    _ = w := by rw [hmul]; rfl

private theorem norm_resolvent_apply_le (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (w : F) : |z.im| * ‖resolvent T z w‖ ≤ ‖w‖ := by
  have h := norm_sub_smul_ge T hT z (resolvent T z w)
  rwa [sub_resolvent_apply T hT hz w] at h

private theorem resolvent_tendsto_of_strong_tendsto (T : ℕ → F →L[ℂ] F) (A : F →L[ℂ] F)
    (hT : ∀ n, IsSelfAdjoint (T n)) (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (hconv : ∀ u : F, Tendsto (fun n : ℕ => T n u) atTop (nhds (A u))) (u : F) :
    Tendsto (fun n : ℕ => resolvent (T n) z u) atTop (nhds (resolvent A z u)) := by
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖resolvent (T n) z u - resolvent A z u‖
      ≤ ‖T n (resolvent A z u) - A (resolvent A z u)‖ / |z.im| := by
    intro n
    have hSn : resolvent (T n) z * (algebraMap ℂ (F →L[ℂ] F) z - T n) = 1 :=
      Ring.inverse_mul_cancel _ (isUnit_algebraMap_sub (T n) (hT n) hz)
    have hS : (algebraMap ℂ (F →L[ℂ] F) z - A) * resolvent A z = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_algebraMap_sub A hA hz)
    have hsub : (T n - A)
        = (algebraMap ℂ (F →L[ℂ] F) z - A) - (algebraMap ℂ (F →L[ℂ] F) z - T n) := by abel
    have hid : resolvent (T n) z - resolvent A z
        = resolvent (T n) z * (T n - A) * resolvent A z := by
      rw [hsub, mul_sub, sub_mul, mul_assoc, hS, hSn]
      simp
    have happ : resolvent (T n) z u - resolvent A z u
        = resolvent (T n) z (T n (resolvent A z u) - A (resolvent A z u)) := by
      have := congrArg (fun S : F →L[ℂ] F => S u) hid
      simpa using this
    rw [happ, le_div_iff₀ hzpos, mul_comm]
    exact norm_resolvent_apply_le (T n) (hT n) hz _
  have hconv0 : Tendsto
      (fun n : ℕ => ‖T n (resolvent A z u) - A (resolvent A z u)‖ / |z.im|) atTop (nhds 0) := by
    have h := hconv (resolvent A z u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    simpa using h.div_const |z.im|
  exact squeeze_zero (fun n => norm_nonneg _) hbound hconv0

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
@[simp] private theorem ofBounded_op (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H)
    (hx : x ∈ (ofBounded A hA).domain) : (ofBounded A hA).op ⟨x, hx⟩ = A x := rfl

private theorem resCLM_ofBounded (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (y : H) :
    (ofBounded A hA).resCLM 1 y = -(resolvent A Complex.I y) := by
  have hz : (Complex.I).im ≠ 0 := by simp
  have h := sub_resolvent_apply A hA hz y
  rw [Algebra.algebraMap_eq_smul_one] at h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply] at h
  set r : H := resolvent A Complex.I y with hr
  set x : H := -r with hx
  have hxmem : x ∈ (ofBounded A hA).domain := by simp [ofBounded]
  have hop : (ofBounded A hA).op ⟨x, hxmem⟩ = A x := rfl
  have hshift : (ofBounded A hA).shift 1 ⟨x, hxmem⟩ = y := by
    rw [UnboundedSelfAdjoint.shift_apply, hop]
    calc A x - ((1 : ℂ) * Complex.I) • x = Complex.I • r - A r := by
          rw [hx, map_neg]; module
      _ = y := h
  have hres := (ofBounded A hA).res_shift (l := 1) one_ne_zero ⟨x, hxmem⟩
  rw [hshift] at hres
  simpa using congrArg (fun (u : (ofBounded A hA).domain) => (u : H)) hres

private theorem strongResolventConvergence_ofBounded {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) :
    StrongResolventConvergence (ofBounded Alim hlim) (fun n => ofBounded (A n) (hA n)) := by
  intro y
  have hz : (Complex.I).im ≠ 0 := by simp
  have h := resolvent_tendsto_of_strong_tendsto A Alim hA hlim hz hconv y
  have h' := h.neg
  simp only [resCLM_ofBounded]
  exact h'

end SirkBoundedResolventAux

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — theorem BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
open BookProof.ChapterSirkTrotterKato








noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SirkBoundedResolventAux
theorem solution {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) :
    StrongResolventConvergence (ofBounded Alim hlim) (fun n => ofBounded (A n) (hA n)) := by
  intro y
  have hz : (Complex.I).im ≠ 0 := by simp
  have h := SirkBoundedResolventAux.resolvent_tendsto_of_strong_tendsto A Alim hA hlim hz hconv y
  have h' := h.neg
  simp only [resCLM_ofBounded]
  exact h'
#print axioms solution
