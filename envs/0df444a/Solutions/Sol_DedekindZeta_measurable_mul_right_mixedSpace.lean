-- Prove2me | solution 1 for DedekindZeta.measurable_mul_right_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:07.576166+00:00
-- url     : https://prove2.me/submissions/7b92fe01-12ba-4d1b-8b48-bdafb272373e

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements

set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
open MeasureTheory NumberField.mixedEmbedding
namespace DedekindZeta
theorem _root_.solution (c : mixedEmbedding.mixedSpace K) :
    Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
  (continuous_id.mul continuous_const).measurable
end DedekindZeta
