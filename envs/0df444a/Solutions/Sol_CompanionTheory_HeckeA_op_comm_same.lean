-- Prove2me | solution 1 for CompanionTheory.HeckeA.op_comm_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:30.908691+00:00
-- url     : https://prove2.me/submissions/cb6f3e2d-a0c0-4549-9c05-14113856e498

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_Formalism_UG_P_hecke_act_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
variable {K}
namespace CompanionTheory.HeckeA
theorem _root_.solution (hK : IsCommensurated K) {φ ψ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) (hψ : ψ ∈ Hecke ℂ K)
    (hc : conv K φ ψ = conv K ψ φ) {f : G → W} (hf : Inv ι K f) : op ι K φ (op ι K ψ f) = op ι K ψ (op ι K φ f) := by
  funext g
  have hm : (fun h => f (g * ι h)) ∈ AMF ℂ (⊥ : Subgroup H) K (1 : Representation ℂ (⊥ : Subgroup H) W) := by
    rintro ⟨γ, hγ⟩ h κ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    show f (g * ι (1 * h * κ)) = f (g * ι h)
    rw [one_mul, map_mul, ← mul_assoc, hf _ _ κ.2]
  have key : ∀ a b : H → ℂ, op ι K a (op ι K b f) g = hAct K a (hAct K b fun h => f (g * ι h)) 1 := fun a b => by
    simp only [op, hAct, one_mul, map_mul, mul_assoc]
  rw [key, key, ← hecke_act_mul H ⊥ K ℂ W 1 hK φ hφ ψ hψ _ hm, ← hecke_act_mul H ⊥ K ℂ W 1 hK ψ hψ φ hφ _ hm, hc]
end CompanionTheory.HeckeA
