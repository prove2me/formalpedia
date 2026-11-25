-- Prove2me | solution 1 for Formalism.GM.FockB.chain_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:14.117356+00:00
-- url     : https://prove2.me/submissions/eae22cd0-a503-42f4-af07-6e1f2331765d

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_tiePhi_mem
import Theorems.Thm_Formalism_GM_FockB_good_of_ops
import Theorems.Thm_Formalism_GM_FockB_biHom_of_good
import Theorems.Thm_Formalism_GM_FockB_zsfree_of_good
import Theorems.Thm_Formalism_GM_FockB_step_same
import Theorems.Thm_Formalism_GM_FockB_step_orth
import Theorems.Thm_Formalism_GM_FockB_disj_VL
import Theorems.Thm_Formalism_GM_FockB_chain_rw
import Theorems.Thm_Formalism_GM_FockB_good_chain
import Theorems.Thm_Formalism_GM_FockB_phi_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
variable {w e zv sv z}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] (hr : 1 ≤ r) (o n j o' n' j' : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (hon : ∀ a ∈ L, j a = j' a → o a = o' a ∧ n a = n' a) (hne : ∃ a ∈ L, j a ≠ j' a)
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o' a) (n' a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j' L * chainP w e zv sv z o' n' L Y') = 0 := by
  induction L with
  | nil =>
    obtain ⟨a, ha, _⟩ := hne
    simp at ha
  | cons a L ih =>
    intro Y' hY'
    obtain ⟨hda, hdL⟩ := List.pairwise_cons.mp hd
    have hvA := hv a (List.mem_cons_self ..)
    have hdisj := disj_VL hda
    rw [chain_rw o n j a L hdisj, chain_rw o' n' j' a L hdisj]
    have gY := good_chain (z := z) o n j a L hdisj Y (hY a (List.mem_cons_self ..))
    have gY' := good_chain (z := z) o' n' j' a L hdisj Y' (hY' a (List.mem_cons_self ..))
    by_cases hja : j a = j' a
    · obtain ⟨ho, hn⟩ := hon a (List.mem_cons_self ..) hja
      rw [← ho, ← hn] at gY'
      rw [← hja, ← ho, ← hn]
      rw [step_same hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY'),
        phi_chain o' n' j' a L hdisj]
      have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
      have hneL : ∃ b ∈ L, j b ≠ j' b := by
        obtain ⟨b, hb, hjb⟩ := hne
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd hja hjb
        · exact ⟨b, hb, hjb⟩
      rw [ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) hdL
        (fun b hb => hon b (List.mem_cons_of_mem _ hb)) hneL
        (fun b hb => hY b (List.mem_cons_of_mem _ hb)) _
        (fun b hb => good_of_ops (hda b hb).symm hPhi (hY' b (List.mem_cons_of_mem _ hb))), mul_zero]
    · exact step_orth hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY') hja
end Formalism.GM.FockB
