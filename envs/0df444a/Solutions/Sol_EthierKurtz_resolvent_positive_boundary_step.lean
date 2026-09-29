-- Prove2me | solution 1 for EthierKurtz.resolvent_positive_boundary_step
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:38:21.786912+00:00
-- url     : https://prove2.me/submissions/40ae491c-c69b-4da5-aee6-4a40414f1a26

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

abbrev aux_rpb_E := EuclideanSpace ℝ (Fin (0 + 1))

def aux_rpb_Ω : Set aux_rpb_E := {x | x 0 < 0}

theorem aux_rpb_proj_apply (x : aux_rpb_E) : EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) x = x 0 := rfl

theorem aux_rpb_ext (x : aux_rpb_E) (h : x 0 = 0) : x = 0 := by
  ext i
  fin_cases i
  simpa using h

theorem aux_rpb_frontier_sub : frontier aux_rpb_Ω ⊆ {0} := by
  intro x hx
  have := frontier_lt_subset_eq (f := fun x : aux_rpb_E => x 0) (g := fun _ => (0:ℝ))
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1))).continuous continuous_const hx
  exact aux_rpb_ext x this

theorem aux_rpb_zero_mem : (0 : aux_rpb_E) ∈ frontier aux_rpb_Ω := by
  rw [frontier, Set.mem_sdiff]
  refine ⟨?_, fun h => ?_⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨EuclideanSpace.single 0 (-ε/2), ?_, ?_⟩
    · show (EuclideanSpace.single (0 : Fin (0+1)) (-ε/2) : aux_rpb_E) 0 < 0
      simp; linarith
    · rw [dist_zero_left, PiLp.norm_single, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
  · have := interior_subset h
    simp [aux_rpb_Ω] at this

theorem aux_rpb_frontier : frontier aux_rpb_Ω = {0} :=
  Set.Subset.antisymm aux_rpb_frontier_sub (Set.singleton_subset_iff.2 aux_rpb_zero_mem)

theorem aux_rpb_boundary : BoundaryCTwiceHolder aux_rpb_Ω 1 := by
  refine ⟨1, one_pos, ?_⟩
  intro x₀ hx₀
  rw [aux_rpb_frontier] at hx₀
  rw [Set.mem_singleton_iff] at hx₀
  subst hx₀
  have hfb : frontier aux_rpb_Ω ∩ Metric.ball (0 : aux_rpb_E) 1 = {0} := by
    rw [aux_rpb_frontier]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Metric.mem_ball]
    constructor
    · exact fun h => h.1
    · rintro rfl; simp
  refine ⟨LinearIsometryEquiv.refl ℝ _, Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _,
    ⟨contDiffOn_const, fun i => i.elim0⟩, rfl, by simp, ?_, ?_⟩
  · rw [hfb]; exact isConnected_singleton
  · rw [hfb]
    ext y
    simp only [Set.image_singleton, Set.mem_singleton_iff, Set.image_univ, Set.mem_range,
      sub_zero, LinearIsometryEquiv.coe_refl, id]
    constructor
    · rintro rfl
      refine ⟨0, ?_⟩
      ext i
      fin_cases i
      rfl
    · rintro ⟨z, rfl⟩
      ext i
      fin_cases i
      rfl


theorem aux_rpb_sum (f : Fin (0+1) → ℝ) : ∑ i, f i = f 0 := Fin.sum_univ_one f

def aux_rpb_u : aux_rpb_E → ℝ := fun x => -1 + x 0 ^ 2

theorem aux_rpb_hasFDeriv (y : aux_rpb_E) :
    HasFDerivAt aux_rpb_u ((2 * y 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1))) y := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1))).hasFDerivAt (x := y)).pow 2
  have h2 := h.const_add (-1)
  have e : (2 • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1))) y ^ (2 - 1)) •
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) =
      (2 * y 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) := by
    ext v
    simp
  rw [e] at h2
  exact h2

theorem aux_rpb_fderiv (y v : aux_rpb_E) : fderiv ℝ aux_rpb_u y v = 2 * y 0 * v 0 := by
  rw [(aux_rpb_hasFDeriv y).fderiv]
  rfl

theorem aux_rpb_contDiff : ContDiff ℝ 2 aux_rpb_u :=
  contDiff_const.add ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) : aux_rpb_E →L[ℝ] ℝ).contDiff.pow 2)

theorem aux_rpb_second (x : aux_rpb_E) :
    fderiv ℝ (fun y => fderiv ℝ aux_rpb_u y (EuclideanSpace.single 0 1)) x
      (EuclideanSpace.single 0 1) = 2 := by
  have hf : (fun y => fderiv ℝ aux_rpb_u y (EuclideanSpace.single 0 1)) =
      fun y : aux_rpb_E => (2 : ℝ) * EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) y := by
    funext y
    rw [aux_rpb_fderiv]
    simp
  rw [hf]
  have := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) : aux_rpb_E →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul (2:ℝ))
  rw [this.fderiv]
  simp

end EthierKurtz

open EthierKurtz

theorem solution : ¬ (∀ {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {μ : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {u g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {J0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ} {lam : ℝ}
    (hx : x₀ ∈ frontier Ω)
    (hboundary : BoundaryCTwiceHolder Ω μ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hcontG : ContinuousOn g (closure Ω))
    (hD : HasFDerivAt u J0 x₀)
    (hJ0b : J0 (c x₀) = 0)
    (hnor : IsOutwardUnitNormal Ω x₀ (normal x₀))
    (hob : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ∑ i, c x₀ i * normal x₀ i)
    (hIdΩ : ∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      a x i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ u x (b x))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hminglob : ∀ y ∈ closure Ω, u x₀ ≤ u y)
    (hu0 : u x₀ < 0)
    (hlam : 0 < lam)
    (hop : 0 ≤ lam * u x₀ - g x₀),
    False) := by
  intro h
  have hv : ‖(EuclideanSpace.single (0 : Fin (0+1)) (1:ℝ) : aux_rpb_E)‖ = 1 := by
    rw [PiLp.norm_single]; simp
  refine @h 0 aux_rpb_Ω 1 (fun _ => 1)
    (fun x => (-3 / (2 * x 0)) • EuclideanSpace.single 0 1)
    (fun _ => EuclideanSpace.single 0 1) (fun _ => EuclideanSpace.single 0 1)
    aux_rpb_u (fun _ => -2) 0 0 1
    aux_rpb_zero_mem aux_rpb_boundary ⟨one_pos, le_rfl⟩
    aux_rpb_contDiff.contDiffOn aux_rpb_contDiff.continuous.continuousOn continuousOn_const
    ?_ (by simp) ?_ ⟨1, one_pos, by simp⟩ ?_ (fun _ _ => Matrix.PosSemidef.one) ?_ ?_
    (by simp [aux_rpb_u]) one_pos (by norm_num [aux_rpb_u])
  · convert aux_rpb_hasFDeriv 0 using 1
    simp
  · refine ⟨aux_rpb_zero_mem, hv, Set.univ, isOpen_univ, Set.mem_univ _, fun x => x 0, 1, one_pos,
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) : aux_rpb_E →L[ℝ] ℝ).contDiff.contDiffOn, rfl,
      fun y _ => Iff.rfl, ?_⟩
    intro v
    rw [show (fun x : aux_rpb_E => x 0) = EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (0+1)) from rfl,
      ContinuousLinearMap.fderiv]
    simp
  · intro x hx
    have hx0 : x 0 ≠ 0 := ne_of_lt hx
    simp only [aux_rpb_sum, Matrix.one_apply_eq, one_mul]
    rw [aux_rpb_second, aux_rpb_fderiv]
    simp
    field_simp
    norm_num
  · refine ⟨1, one_pos, fun x _ θ hθ => ?_⟩
    simp only [aux_rpb_sum, Matrix.one_apply_eq, mul_one]
    have := EuclideanSpace.norm_eq θ
    rw [hθ, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs] at this
    have h2 := congrArg (· ^ 2) this
    simp only [one_pow] at h2
    rw [Real.sq_sqrt (sq_nonneg _)] at h2
    nlinarith
  · intro y _
    simp only [aux_rpb_u]
    simp
    positivity
