-- Prove2me | solution 1 for DedekindZeta.coneSMul_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:08.147795+00:00
-- url     : https://prove2.me/submissions/f9cb00ee-927d-46ef-907d-cb8499609f6f

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
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction
variable {K}
namespace DedekindZeta
theorem _root_.solution (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
    (x : mixedEmbedding.mixedSpace K) :
    g • x = (coneUnitHom (K := K) g) • x := rfl
end DedekindZeta
