-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDB.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:01.757409+00:00
-- url     : https://prove2.me/submissions/41c107c3-73b4-428d-a788-5e1f92ecfce2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Theorems.Thm_P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution (G : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span (Localization.AtPrime p) (G : Set V)) :
    ∃ s ∈ p.primeCompl, s • x ∈ G := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, p.primeCompl.one_mem, by rw [smul_zero]; exact G.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • y = s • (t • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact add_mem (G.smul_mem t hsx) (G.smul_mem s hty)
  | smul o x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, s'⟩, hos⟩ := IsLocalization.mk'_surjective p.primeCompl o
    refine ⟨s' * s, p.primeCompl.mul_mem s'.2 hs, ?_⟩
    have h1 : (s' : A) • o = algebraMap A (Localization.AtPrime p) a := by
      rw [← hos, Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    rw [mul_smul, smul_comm' p s o x, ← smul_assoc, h1, algebraMap_smul]
    exact G.smul_mem a hsx
end Formalism.L2.Pj.QAt.TieLDB
