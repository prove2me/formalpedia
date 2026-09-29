-- Prove2me | solution 1 for FixedPart.isReduced_of_linearIndependent_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/81504fee-6934-5027-a2f5-b81f12ae1af7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FixedPart_isReduced_of_linearIndependent_of_trace

set_option autoImplicit false

open Submodule

namespace FixedPart

section RedAux

variable {R : Type} [CommRing R]
variable {K : Type} [Field K]
variable {T : Type} [CommRing T] [Algebra K T]
variable {ι : Type} [Fintype ι]

private theorem red_map_mem_span (b : Module.Basis ι ℤ R) (f : R →+* T) (r : R) :
    f r ∈ span K (Set.range fun i => f (b i)) := by
  rw [← b.sum_repr r, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact zsmul_mem (subset_span (Set.mem_range_self i)) _

private theorem red_span_eq_top (b : Module.Basis ι ℤ R) (f : R →+* T)
    (hspan : Algebra.adjoin K (Set.range f) = ⊤) :
    span K (Set.range fun i => f (b i)) = ⊤ := by
  rw [eq_top_iff, ← Algebra.top_toSubmodule, ← hspan, Algebra.adjoin_eq_span, span_le]
  intro x hx
  have hle : Submonoid.closure (Set.range (f : R → T)) ≤ MonoidHom.mrange (f : R →* T) :=
    Submonoid.closure_le.mpr (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  obtain ⟨r, hr⟩ := hle hx
  rw [← hr]
  exact red_map_mem_span b f r

private theorem red_repr (b : Module.Basis ι ℤ R) (bT : Module.Basis ι K T) (f : R →+* T)
    (hbT : ∀ i, bT i = f (b i)) (r : R) (i : ι) :
    bT.repr (f r) i = (b.repr r i : K) := by
  have hsum : f r = ∑ j, ((b.repr r j : ℤ) : K) • bT j := by
    conv_lhs => rw [← b.sum_repr r]
    simp only [map_sum, map_zsmul, hbT, Int.cast_smul_eq_zsmul]
  have : bT.equivFun (f r) = fun j => ((b.repr r j : ℤ) : K) := by
    rw [hsum, ← bT.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rw [← bT.equivFun_apply, this]

private theorem red_leftMulMatrix [DecidableEq ι] (b : Module.Basis ι ℤ R) (bT : Module.Basis ι K T)
    (f : R →+* T) (hbT : ∀ i, bT i = f (b i)) (r : R) :
    Algebra.leftMulMatrix bT (f r) = (Algebra.leftMulMatrix b r).map (Int.castRingHom K) := by
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hbT, ← map_mul, red_repr b bT f hbT, eq_intCast]

private theorem red_trace [DecidableEq ι] (b : Module.Basis ι ℤ R) (bT : Module.Basis ι K T)
    (f : R →+* T) (hbT : ∀ i, bT i = f (b i)) (r : R) :
    Algebra.trace K T (f r) = (Algebra.trace ℤ R r : K) := by
  rw [Algebra.trace_eq_matrix_trace bT, Algebra.trace_eq_matrix_trace b,
    red_leftMulMatrix b bT f hbT]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, eq_intCast, Int.cast_sum]

private theorem red_det_traceMatrix_ne_zero [DecidableEq ι] (b : Module.Basis ι ℤ R)
    (hsep : ∀ r : R, r ≠ 0 → ∃ s : R, Algebra.trace ℤ R (r * s) ≠ 0) :
    (Algebra.traceMatrix ℤ b).det ≠ 0 := by
  rw [Algebra.traceMatrix_of_basis, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · by_contra h
    obtain ⟨s, hs⟩ := hsep r h
    exact hs (by simpa only [Algebra.traceForm_apply] using hr s)
  · by_contra h
    obtain ⟨s, hs⟩ := hsep r h
    exact hs (by simpa only [Algebra.traceForm_apply, mul_comm] using hr s)

end RedAux

end FixedPart

theorem solution
    (R : Type) [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (hsep : ∀ r : R, r ≠ 0 → ∃ s : R, Algebra.trace ℤ R (r * s) ≠ 0)
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [Algebra ℚ_[q] T] (f : R →+* T)
    (hspan : Algebra.adjoin ℚ_[q] (Set.range f) = ⊤)
    (hli : LinearIndependent ℚ_[q] fun i => f (Module.Free.chooseBasis ℤ R i)) :
    IsReduced T ∧ IsArtinianRing T := by
  classical
  set b := Module.Free.chooseBasis ℤ R with hb
  have htop : ⊤ ≤ span ℚ_[q] (Set.range fun i => f (b i)) :=
    (FixedPart.red_span_eq_top b f hspan).ge
  let bT : Module.Basis (Module.Free.ChooseBasisIndex ℤ R) ℚ_[q] T := Module.Basis.mk hli htop
  have hbT : ∀ i, bT i = f (b i) := fun i => Module.Basis.mk_apply hli htop i
  haveI : Module.Finite ℚ_[q] T := Module.Finite.of_basis bT
  refine ⟨⟨fun x hx => ?_⟩, IsArtinianRing.of_finite ℚ_[q] T⟩

  have hmat : Algebra.traceMatrix ℚ_[q] bT =
      (Algebra.traceMatrix ℤ b).map (Int.castRingHom ℚ_[q]) := by
    ext i j
    rw [Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply, hbT, hbT, ← map_mul,
      FixedPart.red_trace b bT f hbT, eq_intCast]
  have hdet : (Algebra.traceMatrix ℚ_[q] bT).det ≠ 0 := by
    rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Int.cast_ne_zero.mpr (FixedPart.red_det_traceMatrix_ne_zero b hsep)
  have hnd : (Algebra.traceForm ℚ_[q] T).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bT, ← Algebra.traceMatrix_of_basis]
    exact hdet

  refine hnd.1 x fun y => ?_
  rw [Algebra.traceForm_apply]
  have hxy : IsNilpotent (x * y) := (Commute.all x y).isNilpotent_mul_right hx
  have htr : IsNilpotent (Algebra.trace ℚ_[q] T (x * y)) := by
    rw [Algebra.trace_apply]
    exact LinearMap.isNilpotent_trace_of_isNilpotent (hxy.map (Algebra.lmul ℚ_[q] T))
  exact htr.eq_zero

end S_FixedPart_isReduced_of_linearIndependent_of_trace
end P2MW
export P2MW.S_FixedPart_isReduced_of_linearIndependent_of_trace (solution)
