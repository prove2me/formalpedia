-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.approx_lo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:23.820901+00:00
-- url     : https://prove2.me/submissions/8c8e0a57-0ebb-4e73-a2d7-27e24e0c5893

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_approxE
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
    (hg0 : ∀ p ∈ S, ∀ a b, a < b → g p a b = 0) :
    ∃ L : Matrix (Fin n) (Fin n) E, (∀ a, L a a = 1) ∧ (∀ a b, a < b → L a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (L a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (L a b) ∈ (A p).O := by
  have h := fun ab : Fin n × Fin n => approxE A S c hc (fun p => g p ab.1 ab.2)
  choose x hxS hxO using h
  refine ⟨fun a b => if b < a then x (a, b) else if a = b then 1 else 0, fun a => by simp, fun a b hab => ?_,
    fun p hp a b => ?_, fun p hp a b => ?_⟩
  · simp [not_lt.2 hab.le, hab.ne]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxS (a, b) p hp
    · refine ⟨0, zero_mem _, ?_⟩
      rcases eq_or_ne a b with rfl | hab
      · simp [hg1 p hp a]
      · have hlt : a < b := lt_of_le_of_ne (not_lt.1 hba) hab
        simp [hba, hab, hg0 p hp a b hlt]
  · by_cases hba : b < a
    · simp only [hba, if_true]; exact hxO (a, b) p hp
    · simp only [hba, if_false]
      split_ifs
      · rw [map_one]; exact one_mem _
      · rw [map_zero]; exact zero_mem _
end Formalism.L2.SG.Pf.PCountEx
