-- Prove2me | solution 1 for Formalism.NG.collectAlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:13.30397+00:00
-- url     : https://prove2.me/submissions/e1b0e599-3d55-4c19-a042-0157027ba389

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Theorems.Thm_Formalism_NG_sum_range_ite_le_add_sum_Ioo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) (L : Fin (t + 1) → ℕ∞) (S : Finset (Fin (t + 1))) (v : ℕ∞)
    (what₂ cols qs : Finset ℕ) (lenRow vζ h0 : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (Sha : ℕ → ℕ∞)
    (eO vδ s vhE N H0 : ℕ∞) (cB : ℕ)
    (hG : v ≤ ∑ k ∈ S, L k)
    (hL0 : L 0 ≤ ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) +
      s + 4 * N * ((cols.card : ℕ∞) + 1) * vδ)
    (hL1 : L ⟨1, by omega⟩ ≤ vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      ∑ w ∈ qs, vζ w)
    (hLc : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) → L c ≤ Sha ((c : ℕ) - 1) +
      eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
      (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w) :
    v ≤ ∑ w ∈ what₂, lenRow w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, vζ w := by
  set C1 : ℕ∞ := ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) with hC1
  set A0 : ℕ∞ := ∑ w ∈ what₂, lenRow w +
    ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s with hA0
  set B : ℕ∞ := eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
    4 * ((cols.card : ℕ∞) + 1) * vδ + (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w with hB
  have hsucc : ∀ i : Fin t, L i.succ ≤
      (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hs : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [hi])
      rw [if_pos (by omega), hs]
      refine (hL1.trans ?_)
      rw [hB]
      calc vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w
          ≤ vhE + C1 + eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
            4 * ((cols.card : ℕ∞) + 1) * vδ + ∑ w ∈ qs, vζ w + (cols.card : ℕ∞) * H0 := le_self_add
        _ = _ := by ring
    · rw [if_neg (by omega)]
      have h2 : 2 ≤ ((i.succ : Fin (t + 1)) : ℕ) := by simp [Fin.val_succ]; omega
      refine (hLc i.succ h2).trans_eq ?_
      rw [hB, Fin.val_succ]
      ring
  have hsumite : ∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) ≤
      (vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + C1 else Sha (i + 1 - 1)) t]
    exact sum_range_ite_le_add_sum_Ioo t (vhE + C1) Sha
  have hcol : ∑ w ∈ cols,
      (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) =
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + C1 := by
    rw [hC1, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => by ring
  rw [hcol]
  calc v ≤ ∑ k ∈ S, L k := hG
    _ ≤ ∑ k : Fin (t + 1), L k := sum_le_sum_of_subset (subset_univ _)
    _ = L 0 + ∑ i : Fin t, L i.succ := Fin.sum_univ_succ L
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          ∑ i : Fin t, ((if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) + B) :=
        add_le_add hL0 (sum_le_sum fun i _ => hsucc i)
    _ = (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (∑ i : Fin t, (if (i : ℕ) + 1 = 1 then vhE + C1 else Sha ((i : ℕ) + 1 - 1)) +
            (t : ℕ∞) * B) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (A0 + 4 * N * ((cols.card : ℕ∞) + 1) * vδ) +
          (((vhE + C1) + ∑ e ∈ Ioo 0 t, Sha e) + (t : ℕ∞) * B) := by
        gcongr
    _ = _ := by
        rw [hA0, hB]
        ring
end Formalism.NG
