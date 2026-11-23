-- Prove2me | solution 1 for CompanionTheory.HeckeA.op_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:07.728609+00:00
-- url     : https://prove2.me/submissions/e9bb6ec8-3809-4f22-9d73-21e0e43ae6ed

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_Formalism_UG_P_finite_supp
import Theorems.Thm_Formalism_UG_P_finsum_out_mul


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
theorem _root_.solution {φ : H → ℂ} (hφ : IsBiInv K φ) {f : G → W} (hf : Inv ι K f) {κ : G} {u : H} (hu : u ∈ K) {c : ℂ}
    (hκ : ∀ h, κ * ι h * κ⁻¹ = ι (u * h * u⁻¹)) (hc : ∀ g, f (g * κ) = c • f g) (hfin : IsCommensurated K)
    (hφ' : φ ∈ Hecke ℂ K) (g : G) : op ι K φ f (g * κ) = c • op ι K φ f g := by
  have h1 : op ι K φ f g = ∑ᶠ z : H ⧸ K, φ z.out • f (g * ι (u * z.out)) := by
    rw [op, ← finsum_out_mul K u (fun h => φ h • f (g * ι h)) fun h k => by
      rw [map_mul, ← mul_assoc, hf _ _ k.2, show φ (h * k) = φ h by simpa using hφ 1 k h]]
    exact finsum_congr fun z => by rw [show φ (u * z.out) = φ z.out by simpa using hφ ⟨u, hu⟩ 1 z.out]
  rw [h1, smul_finsum' c ((finite_supp K hfin φ hφ').subset fun z hz h => hz (by simp only [h, zero_smul])), op]
  refine finsum_congr fun z => ?_
  rw [smul_comm, show g * κ * ι z.out = g * (κ * ι z.out * κ⁻¹) * κ by group, hc, hκ, map_mul ι _ u⁻¹, ← mul_assoc,
    hf _ _ (K.inv_mem hu)]
end CompanionTheory.HeckeA
