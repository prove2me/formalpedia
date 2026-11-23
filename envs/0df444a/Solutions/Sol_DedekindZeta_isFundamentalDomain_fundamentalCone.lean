-- Prove2me | solution 1 for DedekindZeta.isFundamentalDomain_fundamentalCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:44:03.343638+00:00
-- url     : https://prove2.me/submissions/6b02232e-4f6c-47e2-9060-d4530ad8374e

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_coneSMul_def
import Theorems.Thm_DedekindZeta_coneUnitHom_mem_torsion_iff
import Theorems.Thm_DedekindZeta_ae_norm_ne_zero
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
theorem _root_.solution :
    IsFundamentalDomain (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by
  refine IsFundamentalDomain.mk'' (measurableSet_fundamentalCone K).nullMeasurableSet ?_ ?_ ?_
  · -- a.e.-cover
    filter_upwards [ae_norm_ne_zero (K := K)] with x hx
    obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hx
    obtain ⟨⟨ζ, e⟩, he, -⟩ := exist_unique_eq_mul_prod K u
    refine ⟨Multiplicative.ofAdd e, ?_⟩
    rw [coneSMul_def]
    have hcone : (coneUnitHom (K := K) (Multiplicative.ofAdd e) : (𝓞 K)ˣ)
        = ∏ i, fundSystem K i ^ (e i) := by
      simp [coneUnitHom]
    have hsplit : u • x
        = (ζ : (𝓞 K)ˣ) • ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • x) := by
      rw [← mul_smul, hcone, ← he]
    have hz : (↑ζ⁻¹ * ↑ζ : (𝓞 K)ˣ) = 1 := by
      rw [← Subgroup.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    have hinv : (↑ζ⁻¹ : (𝓞 K)ˣ) • (u • x)
        = (coneUnitHom (K := K) (Multiplicative.ofAdd e)) • x := by
      rw [hsplit, ← mul_smul, hz, one_smul]
    rw [← hinv]
    exact fundamentalCone.torsion_smul_mem_of_mem hu ((torsion K).inv_mem ζ.2)
  · -- a.e.-disjointness (genuine disjointness for `g ≠ 1`)
    intro g hg
    refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
    intro x hx hx'
    rw [Set.mem_smul_set_iff_inv_smul_mem, coneSMul_def, map_inv] at hx
    have htor := (fundamentalCone.unit_smul_mem_iff_mem_torsion hx'
      (coneUnitHom (K := K) g)⁻¹).mp hx
    have hmem : (coneUnitHom (K := K) g : (𝓞 K)ˣ) ∈ torsion K := by
      simpa using (torsion K).inv_mem htor
    exact hg ((coneUnitHom_mem_torsion_iff g).mp hmem)
  · -- quasi-measure-preserving
    intro g
    exact (measurePreserving_unitSMul (coneUnitHom (K := K) g)).quasiMeasurePreserving
end DedekindZeta
