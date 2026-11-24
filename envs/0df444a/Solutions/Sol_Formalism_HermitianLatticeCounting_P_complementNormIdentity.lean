-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.complementNormIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:42.606654+00:00
-- url     : https://prove2.me/submissions/d1d16e6e-5c77-4105-a834-9f1dc52d5a1d

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : OmegaNorm := by
  intro K V _ _ _ _ h hh r f f' T T' x w ζ hG hG' hT hxmem hw hom
  set Z := crossGram h f f' with hZ
  set z := f (Fin.last r) with hz
  have hx : ∀ y, (∀ a : Fin r, h (f a.castSucc) y = 0) → h x y = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun v _ => h v y = 0) ?_ ?_ ?_ ?_ hxmem
    · rintro v ⟨a, rfl⟩; exact hy a
    · simp
    · intro u v _ _ hu hv; simp [hu, hv]
    · intro c u _ hu; simp [hu]
  have hne : ∀ a : Fin r, a.castSucc ≠ Fin.last r := fun a => (Fin.castSucc_lt_last a).ne
  have hez : ∀ a : Fin r, ∀ b, h (f a.castSucc) (f b) = 0 := fun a b => by
    rw [hG]; simp [hne a]
  have hxf : ∀ b, h x (f b) = 0 := fun b => hx _ fun a => hez a b
  have hxw : h x w = 0 := hx _ fun a => by rw [hh w, hw, star_zero]
  have hwx : h w x = 0 := by rw [hh x, hxw, star_zero]
  have hxx : h x x = 0 := hx _ fun a => by rw [hh x, hxf, star_zero]
  have hzx : h z x = 0 := by rw [hh x, hxf, star_zero]
  have hzw : h z w = 0 := by rw [hh w, hw, star_zero]
  have hzz : h z z = -T := by rw [hz, hG]; simp
  have hxz : h x z = 0 := hxf _
  have hwz : h w z = 0 := hw _
  have hTs : star T = T := by
    have := hh z z
    rw [hzz] at this
    have h2 : star (-T) = -star T := star_neg T
    rw [h2] at this
    exact (neg_injective this).symm
  set om := ∑ b, Z.adjugate b (Fin.last r) • f' b with hom'

  have h1 : h om z = Z.det := by
    rw [hom']
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have : (Z * Z.adjugate) (Fin.last r) (Fin.last r) = Z.det := by
      rw [Matrix.mul_adjugate]; simp
    rw [← this, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  have h2 : h om z = -(ζ * T) := by
    rw [hom]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hxz, hwz,
      hzz, ← hz]
    ring
  have hdet : Z.det = -(ζ * T) := h1.symm.trans h2

  have h3 : h om om = -(T' * (Z.adjugate (Fin.last r) (Fin.last r) *
      star (Z.adjugate (Fin.last r) (Fin.last r)))) := by
    rw [hom']
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.map_smulₛₗ, starRingEnd_apply, hG']
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp; ring
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb
      simp [hb]
    · simp
  have h4 : h om om = h w w - ζ * star ζ * T := by
    rw [hom]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.map_smulₛₗ, starRingEnd_apply, hxx, hxw, hwx, hxz, hwz, hzx, hzw, hzz, ← hz]
    ring
  have hadj : Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    simp [← two_mul]
  rw [← hadj, hdet, star_neg, star_mul, hTs]
  have h5 : h w w = ζ * star ζ * T - T' * (Z.adjugate (Fin.last r) (Fin.last r) *
      star (Z.adjugate (Fin.last r) (Fin.last r))) := by
    have := h3.symm.trans h4
    linear_combination -this
  rw [h5]; ring
end Formalism.HermitianLatticeCounting.P
