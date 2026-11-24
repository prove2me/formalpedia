-- Prove2me | solution 1 for Formalism.L2.G.Cmp.extK_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:07.210973+00:00
-- url     : https://prove2.me/submissions/1d94eb1c-bc26-4fdf-8a7a-6db9e51ed57b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
import Theorems.Thm_Formalism_L2_G_Cmp_mem_spanK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
namespace Formalism.L2.G.Cmp
theorem _root_.solution (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (i : ι) :
    extK c0 c1 b hli KL (c0 (b i)) = c1 (KL (b i)) := by
  have hm : c0 (b i) ∈ spanK c0 := mem_spanK c0 (b i)
  have hp := Submodule.projectionOnto_apply_left (isCompl_complK c0) ⟨c0 (b i), hm⟩
  dsimp only at hp
  simp only [extK, LinearMap.comp_apply]
  rw [hp]
  have e2 : (LinearEquiv.ofEq _ _ (span_basis_eq c0 b).symm) (⟨c0 (b i), hm⟩ : spanK c0) =
      ⟨c0 (b i), Submodule.subset_span ⟨i, rfl⟩⟩ := Subtype.ext rfl
  rw [LinearEquiv.coe_toLinearMap, e2]
  simp only [extSpan, LinearMap.comp_apply]
  rw [hli.repr_eq_single i _ rfl]
  simp
end Formalism.L2.G.Cmp
