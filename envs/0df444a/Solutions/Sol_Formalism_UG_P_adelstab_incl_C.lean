-- Prove2me | solution 1 for Formalism.UG.P.adelstab_incl_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:33.290997+00:00
-- url     : https://prove2.me/submissions/010571fd-6cf4-49b8-8d85-de82e2dd3af8

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (d : 𝓞 F) : ι (algebraMap (𝓞 F) E d) = levelafC E d := by
  simp only [levelafC, inclE]
  first
  | (rw [Algebra.TensorProduct.includeLeftRingHom_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E,
      IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F),
      Algebra.algebraMap_eq_smul_one (A := E),
      Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F), TensorProduct.smul_tmul])
  | simp [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
end Formalism.UG.P
