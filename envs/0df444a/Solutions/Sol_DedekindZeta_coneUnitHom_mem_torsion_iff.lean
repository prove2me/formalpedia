-- Prove2me | solution 1 for DedekindZeta.coneUnitHom_mem_torsion_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:39:56.249164+00:00
-- url     : https://prove2.me/submissions/00830472-a03d-455d-b3b4-28feac3bd667

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



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
attribute [local instance] DedekindZeta.coneMeasurableConstSMul
attribute [local instance] DedekindZeta.coneCountable
attribute [local instance] DedekindZeta.coneSMulInvariantMeasure
variable {K}
namespace DedekindZeta
theorem _root_.solution (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :
    (coneUnitHom (K := K) g : (𝓞 K)ˣ) ∈ torsion K ↔ g = 1 := by
  constructor
  · intro hmem
    have hA : (coneUnitHom (K := K) g : (𝓞 K)ˣ)
        = ((1 : torsion K) : (𝓞 K)ˣ)
          * ∏ i, fundSystem K i ^ ((Multiplicative.toAdd g) i) := by
      simp [coneUnitHom]
    have hB : (coneUnitHom (K := K) g : (𝓞 K)ˣ)
        = ((⟨coneUnitHom (K := K) g, hmem⟩ : torsion K) : (𝓞 K)ˣ)
          * ∏ i, fundSystem K i ^ ((0 : Fin (rank K) → ℤ) i) := by
      simp
    have hpair :=
      (exist_unique_eq_mul_prod K (coneUnitHom (K := K) g)).unique
        (y₁ := ((1 : torsion K), (Multiplicative.toAdd g : Fin (rank K) → ℤ)))
        (y₂ := ((⟨coneUnitHom (K := K) g, hmem⟩ : torsion K), (0 : Fin (rank K) → ℤ))) hA hB
    have h2 : Multiplicative.toAdd g = 0 := congrArg Prod.snd hpair
    exact Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
  · rintro rfl; simpa using (one_mem (torsion K))
end DedekindZeta
