-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.AAx_omit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:01:33.292022+00:00
-- url     : https://prove2.me/submissions/04af6d9f-7067-47ff-97e8-c7c186db9666

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_mono_omit
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_omit_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (k r m : ℕ) (hm : m + 1 ≤ r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → m + 1 ≤ p.val → xi a p = 0) :
    AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Matrix.of fun a l : Fin m => xi (Fin.castLE (by omega) a) (xR k r (m + 1) hm (l0.succAbove l))).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) hm ∘ l0.succAbove) u := by
  classical
  unfold AAx
  set g := fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove
  have hg : Function.Injective g := omit_inj hm
  have hsub : Finset.image g Finset.univ ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image (fun a _ b _ h => hg h)]
    apply Finset.sum_congr rfl
    intro l0 _
    rw [if_pos]
    · rfl
    · intro a b hab; simp only [g, Function.comp_apply, xR, eI]; exact Fin.strictMono_succAbove l0 hab
  · intro c _ hc
    split_ifs with hP
    · by_cases hS : ∀ l, (c l).val < m + 1
      · obtain ⟨l0, hl0⟩ := mono_omit hm c hP hS
        exact absurd (Finset.mem_image.2 ⟨l0, Finset.mem_univ _, hl0.symm⟩) hc
      · push Not at hS
        obtain ⟨l, hl⟩ := hS
        rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by
          simp only [Matrix.of_apply]; exact hz _ _ (by simp) hl), zero_smul]
    · rfl
end Formalism.FourierDecayAlt.P.PBG
