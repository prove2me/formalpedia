-- Prove2me | solution 1 for CohCarrier.diamondL_top_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/98c500ca-cbc4-5609-a300-ee2352b3b1d6

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_diamondL_top_apply

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

theorem solution (M : ℕ) [NeZero M] (𝒪 : Type) [CommRing 𝒪]
    (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M ⊤ 𝒪) :
    CohCarrier.diamondL M ⊤ 𝒪 d φ = φ := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M d
  rw [CohCarrier.diamondL_eq_diamondRaw M ⊤ 𝒪 d σ hσ]

  have hσmem : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊤ :=
    CohCarrier.mem_GammaH_iff.mpr ⟨σ.2, Subgroup.mem_top _⟩
  set s : ↥(CohCarrier.GammaH M ⊤) := ⟨(σ : SL(2, ℤ)), hσmem⟩ with hs
  ext a

  change φ (Additive.ofMul (CohCarrier.conjHom M ⊤ σ (Additive.toMul a))) = φ a
  have hconj : CohCarrier.conjHom M ⊤ σ (Additive.toMul a) = s * Additive.toMul a * s⁻¹ :=
    Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

end S_CohCarrier_diamondL_top_apply
end P2MW
export P2MW.S_CohCarrier_diamondL_top_apply (solution)
