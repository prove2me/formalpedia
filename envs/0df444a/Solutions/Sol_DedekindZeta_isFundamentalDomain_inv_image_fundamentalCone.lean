-- Prove2me | solution 1 for DedekindZeta.isFundamentalDomain_inv_image_fundamentalCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:13.079069+00:00
-- url     : https://prove2.me/submissions/697e6ee0-7148-43b5-a7af-cfcf02fe9afa

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_mixedMulHaar_map_inv
import Theorems.Thm_DedekindZeta_measurable_mixedSpace_inv
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_unitSMul_inv
import Theorems.Thm_DedekindZeta_coneSMul_def
import Theorems.Thm_DedekindZeta_isFundamentalDomain_fundamentalCone
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
namespace DedekindZeta
theorem _root_.solution :
    IsFundamentalDomain (Multiplicative (Fin (rank K) → ℤ))
      ((fun y : mixedEmbedding.mixedSpace K => y⁻¹) ''
        mixedEmbedding.fundamentalCone K) (mixedMulHaar K) := by
  have hmp : MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => x⁻¹)
      (mixedMulHaar K) (mixedMulHaar K) :=
    ⟨measurable_mixedSpace_inv, mixedMulHaar_map_inv⟩
  have himg := (isFundamentalDomain_fundamentalCone (K := K)).image_of_equiv
    (Equiv.inv (mixedEmbedding.mixedSpace K))
    (by simpa using hmp.quasiMeasurePreserving)
    (Equiv.inv (Multiplicative (Fin (rank K) → ℤ)))
    (fun g x => by
      -- Semiconj: `(g⁻¹ • x)⁻¹ = g • x⁻¹`.
      simp only [Equiv.inv_apply]
      rw [coneSMul_def, coneSMul_def, map_inv, Theta.unitSMul_inv, inv_inv])
  simpa using himg
end DedekindZeta
