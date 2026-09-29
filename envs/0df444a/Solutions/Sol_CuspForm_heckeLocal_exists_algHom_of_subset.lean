-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algHom_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/742497e5-7573-59d6-a3bc-ec3ce14f261a

import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_CuspForm_heckeLocal_exists_factor_algHom
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algHom_of_subset

set_option autoImplicit false

open CuspForm in
theorem solution
    (N : ℕ) [NeZero N] (S S₀ : Set ℕ) (hS : S₀ ⊆ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 S₀ →+* IsLocalRing.ResidueField 𝒪)
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hθ : ∀ t : CuspForm.heckeAlgebra N 2 S,
      θ t = θ₀ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS) t)) :
    ∃ Ψ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N S₀ 𝒪 θ₀,
      IsLocalHom (Ψ : CuspForm.heckeLocal N S 𝒪 θ →+* CuspForm.heckeLocal N S₀ 𝒪 θ₀) ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        Ψ (CuspForm.heckeLocal.π N S 𝒪 θ t) =
          CuspForm.heckeLocal.π N S₀ 𝒪 θ₀ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS) t) := by
  classical

  set incl : heckeAlgebra N 2 S →+* heckeAlgebra N 2 S₀ :=
    (Subalgebra.inclusion (heckeAlgebra_mono hS)).toRingHom with hincl
  set π' : heckeAlgebra N 2 S →+* heckeLocal N S₀ 𝒪 θ₀ :=
    (heckeLocal.π N S₀ 𝒪 θ₀).comp incl with hπ'def
  have hπ' : ∀ t, IsLocalRing.residue (heckeLocal N S₀ 𝒪 θ₀) (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (heckeLocal N S₀ 𝒪 θ₀)) (θ t) := by
    intro t
    rw [hπ'def, RingHom.comp_apply, CuspForm.heckeLocal.residue_pi N S₀ 𝒪 θ₀ (incl t), hθ t]
    rfl
  obtain ⟨Ψ, hΨloc, hΨπ⟩ :=
    CuspForm.heckeLocal.exists_factor_algHom N S 𝒪 θ Fact.out (heckeLocal N S₀ 𝒪 θ₀) π' hπ'
  refine ⟨Ψ, hΨloc, fun t => ?_⟩
  rw [hΨπ t, hπ'def, RingHom.comp_apply]
  rfl

end S_CuspForm_heckeLocal_exists_algHom_of_subset
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algHom_of_subset (solution)
