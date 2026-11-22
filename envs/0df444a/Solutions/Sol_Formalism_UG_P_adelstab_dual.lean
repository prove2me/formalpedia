-- Prove2me | solution 1 for Formalism.UG.P.adelstab_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:20.99202+00:00
-- url     : https://prove2.me/submissions/38307e21-09b6-40da-a34d-d9ad38d8403e

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
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (d : E)
    (hd : ∀ i, IsIntegral ℤ (d * β i)) (e : E)
    (he : ∀ b : 𝓞 E, Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) :
    d * e ∈ Submodule.span (𝓞 F)
      (Set.range ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β)) := by
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  rw [← β'.sum_repr (d * e)]
  refine sum_mem fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  obtain ⟨t, ht⟩ := he ⟨d * β i, hd i⟩
  have : Algebra.trace F E (d * e * β i) = algebraMap (𝓞 F) F t := by
    rw [ht]; congr 1; show _ = e * (d * β i); ring
  rw [this, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.UG.P
