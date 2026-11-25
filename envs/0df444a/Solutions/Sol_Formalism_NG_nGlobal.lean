-- Prove2me | solution 1 for Formalism.NG.nGlobal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:58.019886+00:00
-- url     : https://prove2.me/submissions/35a4a13b-477b-44f2-b4fb-cde8b08ab1de

import Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SumIteLe
import Theorems.Thm_Formalism_NG_sum_ite_le
import Theorems.Thm_Formalism_NG_globalConcrete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatNGlobal := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ t bl hbl ρk hsurj
    hblk hcard ℓ what₂ cols Q lenRow e' j vδ h0 s Sha vhE cB deg H0 vζ eO h0b hcb
  classical
  have hG := globalConcrete O X X' T T' Z p q b hT hZ d R' m g P hdet hφ π' ρπ hρπ (Fin (t + 1)) bl
    hbl ρk hsurj hblk hcard
  refine hG.trans ((Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans ?_)
  rw [Fin.sum_univ_succ]
  have hsucc : ∑ c : Fin t, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c.succ) P))) ≤
      ∑ c : Fin t, ((if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
          else Sha ((c : ℕ) + 1 - 1)) +
        (eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
          (cols.card : ℕ∞) * H0 + ∑ z ∈ Q, vζ z)) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have h := hcb c.succ (Fin.succ_ne_zero c)
    rw [Fin.val_succ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hite : ∑ c : Fin t, (if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha ((c : ℕ) + 1 - 1)) ≤
      (vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)) + ∑ e ∈ Ioo 0 t, Sha e :=
    (Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha (i + 1 - 1)) t).le.trans (sum_ite_le t _ Sha)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hsucc
  refine (add_le_add h0b (hsucc.trans (add_le_add hite le_rfl))).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib]
  ring
end Formalism.NG
