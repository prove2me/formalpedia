-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.summable_periodisation_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:01:12.889572+00:00
-- url     : https://prove2.me/submissions/3d85c67e-bca3-4dc0-906c-e661cf8e193a

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (x : V) :
    Summable (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V))) := by
  classical
  -- The character has modulus one: reduce to summability of the norms.
  apply Summable.of_norm
  -- 𝓕 f is again Schwartz.
  set g : SchwartzMap V ℂ := SchwartzMap.fourierTransformCLM ℂ f with hg
  have hgc : (g : V → ℂ) = 𝓕 (f : V → ℂ) := by
    rw [hg]; rfl
  set Lstar := dualLattice L
  set d : ℕ := Module.finrank ℤ Lstar with hd
  set s : ℝ := -(d : ℝ) - 1 with hs
  have hsd : s < -(Module.finrank ℤ Lstar : ℝ) := by rw [hs, ← hd]; linarith
  have hgO : (g : V → ℂ) =O[Filter.cocompact V] fun y => ‖y‖ ^ s :=
    g.isBigO_cocompact_rpow s
  have hLclosed : IsClosed (X := V) (Lstar : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ Lstar.toAddSubgroup
      (inferInstanceAs (DiscreteTopology Lstar))
  have hcoe : Filter.Tendsto ((↑) : Lstar → V) Filter.cofinite
      (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hbo : (fun w : Lstar => (g : V → ℂ) (w : V)) =O[Filter.cofinite]
      fun w : Lstar => ‖(w : V)‖ ^ s := hgO.comp_tendsto hcoe
  have hsum : Summable fun w : Lstar => ‖(w : V)‖ ^ s := by
    have := ZLattice.summable_norm_sub_rpow Lstar s hsd 0
    refine this.congr fun w => ?_; rw [sub_zero]
  have hg_sum : Summable fun w : Lstar => (g : V → ℂ) (w : V) :=
    summable_of_isBigO hsum hbo
  -- Multiply by the constant `(vol L)⁻¹` and rewrite via `Circle.norm_smul`.
  have hconst : Summable fun w : Lstar =>
      ‖(ZLattice.covolume L : ℂ)⁻¹‖ * ‖𝓕 (f : V → ℂ) (w : V)‖ := by
    refine (hg_sum.norm.mul_left ‖(ZLattice.covolume L : ℂ)⁻¹‖).congr fun w => ?_
    rw [hgc]
  refine hconst.congr fun w => ?_
  rw [Circle.norm_smul, norm_mul]
end DedekindZeta.PoissonSummation
