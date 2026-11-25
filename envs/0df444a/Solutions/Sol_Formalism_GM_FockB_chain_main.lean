-- Prove2me | solution 1 for Formalism.GM.FockB.chain_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:45:13.014471+00:00
-- url     : https://prove2.me/submissions/a9588339-d666-4161-8ef3-ee99de8cf185

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_ops_apply_comm
import Theorems.Thm_Formalism_GM_FockB_tiePhi_mem
import Theorems.Thm_Formalism_GM_FockB_good_of_ops
import Theorems.Thm_Formalism_GM_FockB_biHom_of_good
import Theorems.Thm_Formalism_GM_FockB_zsfree_of_good
import Theorems.Thm_Formalism_GM_FockB_step_same
import Theorems.Thm_Formalism_GM_FockB_disj_VL
import Theorems.Thm_Formalism_GM_FockB_chainPhi_mem
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
theorem _root_.solution [CharZero k] (hr : 1 ≤ r) (o n j : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j L * chainP w e zv sv z o n L Y') =
        cst (r := r) z o n j L * M.fockK Y (chainPhi w e z o n L Y') := by
  induction L with
  | nil =>
    intro Y' _
    simp [chainE, chainP, chainPhi, cst]
  | cons a L ih =>
    intro Y' hY'
    obtain ⟨hda, hdL⟩ := List.pairwise_cons.mp hd
    have hvA := hv a (List.mem_cons_self ..)
    have hdisj := disj_VL hda
    rw [chain_rw o n j a L hdisj, chain_rw o n j a L hdisj]
    have gY := good_chain (z := z) o n j a L hdisj Y (hY a (List.mem_cons_self ..))
    have gY' := good_chain (z := z) o n j a L hdisj Y' (hY' a (List.mem_cons_self ..))
    rw [step_same hvA hr (biHom_of_good gY) (biHom_of_good gY') (zsfree_of_good gY) (zsfree_of_good gY'),
      phi_chain o n j a L hdisj]
    have hPhi := tiePhi_mem (k := k) (w := w a) (e := e a) (zv := zv a) (sv := sv a) (o a) (n a) (z a)
    rw [ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) hdL (fun b hb => hY b (List.mem_cons_of_mem _ hb)) _
      (fun b hb => good_of_ops (hda b hb).symm hPhi (hY' b (List.mem_cons_of_mem _ hb)))]
    have e2 : chainPhi w e z o n (a :: L) Y' =
        chainPhi w e z o n L (Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) Y') := by
      show Formalism.GM.tiePhi (w a) (e a) (o a) (n a) (z a) (chainPhi w e z o n L Y') = _
      exact ops_apply_comm hdisj hPhi (chainPhi_mem (zv := zv) (sv := sv) o n L) _
    rw [e2]
    simp only [cst, List.map_cons, List.prod_cons]
    ring
end Formalism.GM.FockB
