-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.CC.Surj.wal_sig_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:21:52.7088+00:00
-- url     : https://prove2.me/submissions/76b907d0-55b7-4cd2-8886-53920fcc854d

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_incl_int
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
local notation "Av" => E ⊗[F] v.adicCompletion F
local notation "Sv" => Formalism.UG.P.lvS F E v
local notation "ιv" => inclE (F := F) (E := E) (v.adicCompletion F)
namespace Formalism.MainNotions.Gaps.CC.Surj
theorem _root_.solution (σ : E →ₐ[F] E) {s : Av} (hs : s ∈ Sv) :
    sigR σ (v.adicCompletion F) s ∈ Sv := by
  refine Subring.closure_induction (p := fun s _ => sigR σ (v.adicCompletion F) s ∈ Sv)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · have h1 : sigR σ (v.adicCompletion F) (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ιv ((σ : E →+* E) (algebraMap (𝓞 E) E b)) := by
        simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
      show sigR σ _ (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Sv
      rw [h1]
      exact wal_incl_int v _ ((RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom))
    · have h1 : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ Sv
      rw [h1]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy
end Formalism.MainNotions.Gaps.CC.Surj
