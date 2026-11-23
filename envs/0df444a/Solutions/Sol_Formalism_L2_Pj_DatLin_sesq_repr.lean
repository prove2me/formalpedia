-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.sesq_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:38.550684+00:00
-- url     : https://prove2.me/submissions/1b31c5c5-2b18-4a28-b27c-234ca428fc3a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SumEmbeddingsEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution [StarRing E] {V : Type} [AddCommGroup V] [Module E V] {ι : Type} [Fintype ι]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis ι E V) (x y : V) :
    h x y = ∑ i, ∑ j, star (b.repr x i) * h (b i) (b j) * b.repr y j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.L2.Pj.DatLin
