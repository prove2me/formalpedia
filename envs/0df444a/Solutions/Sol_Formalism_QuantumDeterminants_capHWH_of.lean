-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capHWH_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:48.475432+00:00
-- url     : https://prove2.me/submissions/a0b7a45f-6ec4-4cc1-ad6a-70a5965f5d73

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_EabH_fun
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUJ
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_inUH
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_smooth
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_repr
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_gl
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_QP
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_unique
import Theorems.Thm_Formalism_REAL_qDetHW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution (hAd : GlRelAd) : CapHWH := by
  intro n ε E _ _ H P Q f ν hQP hPQ hH hf hhw g hg u
  have hsm := ioh_smooth ε H P Q f hPQ hH hf
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have hR := ioh_repr (ε := ε) (E := E) P Q
  have hEW : ∀ a b y, EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) y =
      EabH H a b f (Q * y * P) := fun a b y =>
    (congrFun (ioh_EabH_fun ε H P Q f a b hQP hPQ hH) y).symm
  have hHW : IsHW (iohE ε E P Q) ν x := by
    refine ⟨fun a => io_rep_unique (hR a a _ x hx) (fun g' hg' => ?_),
      fun a b hab => io_rep_unique (hR a b _ x hx) (fun g' hg' => ?_)⟩
    · show EcV ε (P * Matrix.single a a 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).1 a, Submodule.coe_smul,
        Pi.smul_apply, ← hx g' hg']
    · show EcV ε (P * Matrix.single a b 1 * Q) (fun y => f (Q * y * P)) g' = _
      rw [hEW, (hhw _ (ioh_inUH ε H P Q g' hPQ hH hg')).2 a b hab]; rfl
  have h1 := ioh_qminor_rep hR id id u hx _ hg'
  have h2 := qDetHW (ioS ε E) n (iohE ε E P Q) ν x (ioh_gl hAd P Q hQP) hHW u
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1]
  unfold qdet at h2
  rw [h2]
  show (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x.1 ⟨_, hg'⟩ = _
  rw [← hx _ hg']
  show _ • f (Q * (P * g * Q) * P) = _
  rw [ioh_QP P Q g hQP]
end Formalism.QuantumDeterminants
