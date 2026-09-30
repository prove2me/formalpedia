-- Prove2me | solution 1 for FriedmannEquations.density_scaling_of_fluidEq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:40:38.605214+00:00
-- url     : https://prove2.me/submissions/fd640302-2ba5-4e9e-8800-ef7c52c95c21

import Definitions.Def_FriedmannEquations_Defs
set_option autoImplicit false
open FriedmannEquations Filter Topology

theorem solution (w : ℝ) (R ρ : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (hR_pos : ∀ t ∈ I, 0 < R t) (hR : DifferentiableOn ℝ R I) (hρ : DifferentiableOn ℝ ρ I)
    (hfluid : ∀ t ∈ I, FluidEq R ρ (fun s => w * ρ s) t) :
    ∃ C : ℝ, ∀ t ∈ I, ρ t = C * R t ^ (-3 * (1 + w)) := by
  let q : ℝ := 3 * (1+w)
  let f : ℝ → ℝ := fun t => ρ t * R t ^ q
  have hzero (t : ℝ) (ht : t ∈ I) : HasDerivAt f 0 t := by
    have hdR := ((hR t ht).differentiableAt (hI_open.mem_nhds ht)).hasDerivAt
    have hdρ := ((hρ t ht).differentiableAt (hI_open.mem_nhds ht)).hasDerivAt
    have hd := hdρ.mul (hdR.rpow_const (p := q) (Or.inl (hR_pos t ht).ne'))
    have hf := hfluid t ht
    unfold FluidEq hubble at hf
    convert! hd using 1
    rw [hf, Real.rpow_sub_one (hR_pos t ht).ne']
    dsimp [q]
    field_simp [(hR_pos t ht).ne']
    <;> ring
  obtain ⟨C, hC⟩ := hI_open.exists_is_const_of_deriv_eq_zero hI_conn
    (fun t ht => (hzero t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hzero t ht).deriv)
  refine ⟨C, ?_⟩
  intro t ht
  have hn : R t ^ q ≠ 0 := (Real.rpow_pos_of_pos (hR_pos t ht) q).ne'
  have hprod : ρ t * R t ^ q = C := hC t ht
  rw [show -3 * (1+w) = -q by dsimp [q]; ring, Real.rpow_neg (hR_pos t ht).le]
  exact (eq_div_iff hn).mpr hprod
