-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.summable_periodisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:20.100343+00:00
-- url     : https://prove2.me/submissions/5ef49ff3-220d-44c3-8f3c-0f1a67d74a50

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
    Summable fun v : L => (f : V → ℂ) (x + v) := by
  classical
  set d : ℕ := Module.finrank ℤ L with hd
  -- The exponent `s = -(d+1) < -d` controlling both the Schwartz decay and the
  -- lattice sum.
  set s : ℝ := -(d : ℝ) - 1 with hs
  have hsd : s < -(Module.finrank ℤ L : ℝ) := by rw [hs, ← hd]; linarith
  -- Schwartz rapid decay: `f =O[cocompact V] (‖·‖ ^ s)` (`ProperSpace V` from
  -- finite dimensionality). See `SchwartzMap.isBigO_cocompact_rpow`.
  have hfO : (f : V → ℂ) =O[Filter.cocompact V] fun y => ‖y‖ ^ s :=
    f.isBigO_cocompact_rpow s
  -- The translated lattice inclusion `v ↦ x + v` tends to `cocompact V` along
  -- `cofinite`: the lattice is a closed discrete set, so its inclusion does
  -- (`tendsto_cofinite_cocompact_of_discrete`), and translation by `x` is a
  -- homeomorphism, hence proper.
  have hLclosed : IsClosed (X := V) (L : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hcoe : Filter.Tendsto ((↑) : L → V) Filter.cofinite (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have htrans : Filter.Tendsto (fun y : V => x + y)
      (Filter.cocompact V) (Filter.cocompact V) :=
    (Homeomorph.addLeft x).isClosedEmbedding.tendsto_cocompact
  have he : Filter.Tendsto (fun v : L => x + (v : V))
      Filter.cofinite (Filter.cocompact V) := htrans.comp hcoe
  -- Compose the decay estimate with the translated inclusion.
  have hbo : (fun v : L => (f : V → ℂ) (x + v)) =O[Filter.cofinite]
      fun v : L => ‖x + (v : V)‖ ^ s := hfO.comp_tendsto he
  -- The polynomial lattice sum converges (`ZLattice.summable_norm_sub_rpow`).
  have hsum : Summable fun v : L => ‖x + (v : V)‖ ^ s := by
    have := ZLattice.summable_norm_sub_rpow L s hsd (-x)
    refine this.congr fun v => ?_
    rw [sub_neg_eq_add, add_comm]
  exact summable_of_isBigO hsum hbo
end DedekindZeta.PoissonSummation
