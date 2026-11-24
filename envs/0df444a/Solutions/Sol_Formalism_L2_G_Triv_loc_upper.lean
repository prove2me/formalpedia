-- Prove2me | solution 1 for Formalism.L2.G.Triv.loc_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:39.735927+00:00
-- url     : https://prove2.me/submissions/78ddfc8c-142d-484b-8cfe-c67adcb423f2

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Theorems.Thm_Formalism_L2_G_Triv_incl_int

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G.Triv
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k))
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ) (i : n) :
    inclE (F := F) (v.adicCompletion F) (m : E) * y i ∈ SV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨x, hx, rfl⟩ := hy'
    rw [← map_mul]
    exact incl_int v _ (hm x hx i)
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, mul_add]
    exact add_mem ha hb
  | smul s a _ ha =>
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    rw [mul_left_comm]
    exact mul_mem s.2 ha
end Formalism.L2.G.Triv
