-- Prove2me | solution 1 for Formalism.L2.G.Triv.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:11.193182+00:00
-- url     : https://prove2.me/submissions/5f877e5f-020d-4a78-bc68-ad9551b7b600

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.G.Triv
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (z : 𝒜) :
    z = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    have he := ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at he
    conv_lhs => rw [← he]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul, mul_comm e (β i)]
    simp [adelstabT]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, map_add, TensorProduct.tmul_add]
end Formalism.L2.G.Triv
