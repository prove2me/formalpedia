-- Prove2me | solution 1 for Formalism.L2.G.Triv.loc_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:43.082469+00:00
-- url     : https://prove2.me/submissions/a1c38ffa-a587-44b6-a3fe-07a48ea98144

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
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.G.Triv
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ) (hm : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ)
    (v : HeightOneSpectrum (𝓞 F)) (y : n → E ⊗[F] v.adicCompletion F) (hy : ∀ i, y i ∈ SV E v) :
    (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ := by
  have key : (fun i => inclE (F := F) (v.adicCompletion F) (m : E) * y i) =
      ∑ k, (⟨y k, hy k⟩ : SV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = y i * inclE (F := F) (v.adicCompletion F) ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, mul_comm]
    · intro k _ hk
      show y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hk), map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm k, rfl⟩)
end Formalism.L2.G.Triv
