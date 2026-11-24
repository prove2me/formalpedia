-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:32.720442+00:00
-- url     : https://prove2.me/submissions/0daafb14-89d0-4783-a889-d47f3bcdca62

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfStmt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RCoc
namespace Formalism.L2.SG.Pf.RCoc
theorem _root_.solution : KerBaseChange := by
  intro K L _ _ f m p _ _ _ A
  classical
  set T : (p → K) →ₗ[K] (m → K) := Matrix.toLin' A with hT
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker T)
  have hinj : LinearMap.ker (T ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hk : (c : p → K) ∈ LinearMap.ker T := hc
    have hm : (c : p → K) ∈ LinearMap.ker T ⊓ C := ⟨hk, c.2⟩
    rw [hC.inf_eq_bot, Submodule.mem_bot] at hm
    exact Subtype.ext hm
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (T ∘ₗ C.subtype) hinj
  have hTQT : ∀ v : p → K, T (C.subtype (g (T v))) = T v := by
    intro v
    have hv : v ∈ LinearMap.ker T ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    have hk0 : T k = 0 := hk
    have e : g (T (k + c)) = ⟨c, hc⟩ := by
      rw [map_add, hk0, zero_add]
      exact LinearMap.congr_fun hg ⟨c, hc⟩
    rw [e, map_add, hk0, zero_add]
    rfl
  set Q : Matrix p m K := LinearMap.toMatrix' (C.subtype ∘ₗ g) with hQ
  have hAQA : A * Q * A = A := by
    have hcomp : T ∘ₗ (C.subtype ∘ₗ g) ∘ₗ T = T := LinearMap.ext hTQT
    have h := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hT, LinearMap.toMatrix'_toLin', ← hQ,
      ← Matrix.mul_assoc] at h
  refine ⟨1 - Q * A, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hAQA, sub_self]
  · intro z hz
    have e : (1 - Q * A).map f = 1 - Q.map f * A.map f := by
      have h := (f.mapMatrix (m := p)).map_sub 1 (Q * A)
      rw [map_one] at h
      simp only [RingHom.mapMatrix_apply] at h
      rw [h, Matrix.map_mul]
    rw [e, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]
end Formalism.L2.SG.Pf.RCoc
