-- Prove2me | solution 1 for DedekindZeta.Theta.discreteTopology_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:14:40.693011+00:00
-- url     : https://prove2.me/submissions/1629cbb7-0222-4340-a466-aad78e9ae466

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_idealLattice_eq_comap

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    DiscreteTopology (idealLattice K I) := by
  rw [idealLattice_eq_comap K I hI]
  infer_instance
end DedekindZeta.Theta
