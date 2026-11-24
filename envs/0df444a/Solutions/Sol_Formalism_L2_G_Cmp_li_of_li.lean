-- Prove2me | solution 1 for Formalism.L2.G.Cmp.li_of_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:16.269623+00:00
-- url     : https://prove2.me/submissions/411c5263-847f-4996-af35-6b5bbf2e0072

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
import Theorems.Thm_Formalism_L2_G_Cmp_extK_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
section Indep
open TensorProduct
variable {ι' : Type*}
private theorem li_core_lemma_2 {κ : Type*} (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (v : κ → V0) (hv : LinearIndependent LL v) :
    LinearIndependent Kf fun k => c0 (v k) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs k hk
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply k) ∘ₗ hv.repr)
  let c1 : LL →ₛₗ[e] Kf := { toFun := e, map_add' := e.map_add, map_smul' := fun a x => e.map_mul a x }
  have hφv : ∀ i, φ (v i) = if i = k then 1 else 0 := by
    intro i
    have h1 := LinearMap.congr_fun hφ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h1
    rw [h1, hv.repr_eq_single i _ rfl, Finsupp.single_apply]
  have h2 := congrArg (extK c0 c1 b hli φ) hs
  rw [map_sum, map_zero] at h2
  simp only [map_smul, extK_apply] at h2
  rw [Finset.sum_eq_single k (fun i _ hik => by rw [hφv, if_neg hik]; simp [c1])
    (fun h => absurd hk h), hφv, if_pos rfl] at h2
  simpa [c1] using h2
end Indep
section Rat
variable {Cc : Type*} [Field Cc] {s : LL →+* Cc} {M0 M1 : Type*} [AddCommGroup M0] [Module Cc M0]
  [AddCommGroup M1] [Module Cc M1]
end Rat
end Formalism.L2.G.Cmp
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
open TensorProduct
variable {ι' : Type*}
namespace Formalism.L2.G.Cmp
theorem _root_.solution {κ : Type*} (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (v : κ → V0) (hv : LinearIndependent LL v) :
    LinearIndependent Kf fun k => c0 (v k) := by
  exact li_core_lemma_2 c0 b hli v hv
end Formalism.L2.G.Cmp
