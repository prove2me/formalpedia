-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_prod_torus_eq_integral_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:35.490131+00:00
-- url     : https://prove2.me/submissions/3263f3a7-8363-4803-8924-644ca6c253cb

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_908
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution
    {g : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hg : Integrable g) :
    (∫ θ, g θ)
      = ∫ y in Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1),
          g (fun i => ((y i : ℝ) : AddCircle (1 : ℝ))) := by
  -- `UnitAddTorus.integral_preimage` (Mathlib) is exactly the product-torus = box
  -- identity for the mass-1 Haar product measure, with the fundamental box
  -- `(Ioc (a i) (a i + 1))^d`. Specialise to `a = 0`, giving the half-open unit
  -- box, and rewrite the set into `Set.univ.pi` form.
  have h := UnitAddTorus.integral_preimage (d := Fin d) g (0 : Fin d → ℝ)
  simp only [Pi.zero_apply, zero_add] at h
  have hset : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      = Set.univ.pi (fun _ : Fin d => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [h, hset]
end DedekindZeta.PoissonSummation
