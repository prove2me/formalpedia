-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.approx_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:07:36.498855+00:00
-- url     : https://prove2.me/submissions/4e4f658f-7efe-4a07-8bdf-0b1017edd73d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_approx_lo
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, b < a → g p a b = 0) :
    ∃ U : Matrix (Fin n) (Fin n) E, (∀ a, U a a = 1) ∧ (∀ a b, b < a → U a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (U a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (U a b) ∈ (A p).O := by
  obtain ⟨L, hL1, hL0, hLS, hLn⟩ := approx_lo A S c hc (fun p => (g p).transpose)
    (fun p hp a => by simpa using hg1 p hp a)
    (fun p hp a b hab => by simpa [Matrix.transpose_apply] using hg0 p hp b a hab)
  refine ⟨L.transpose, fun a => by simpa using hL1 a, fun a b hab => by simpa using hL0 b a hab,
    fun p hp a b => ?_, fun p hp a b => by simpa using hLn p hp b a⟩
  simpa [Matrix.transpose_apply] using hLS p hp b a
end Formalism.L2.SG.Pf.PCountEx
