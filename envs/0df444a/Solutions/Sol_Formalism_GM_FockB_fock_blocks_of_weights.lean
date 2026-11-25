-- Prove2me | solution 1 for Formalism.GM.FockB.fock_blocks_of_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:30.091979+00:00
-- url     : https://prove2.me/submissions/3a637c77-c512-4d38-897c-ce69c23c195c

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_chain_main
import Theorems.Thm_Formalism_GM_FockB_chain_orth
import Theorems.Thm_Formalism_GM_FockB_pall_eq
import Theorems.Thm_Formalism_GM_FockB_phi_eq
import Theorems.Thm_Formalism_GM_FockB_ehat_eq
import Theorems.Thm_Formalism_GM_FockB_deg_fst
import Theorems.Thm_Formalism_GM_FockB_deg_snd
import Theorems.Thm_Formalism_GM_FockB_tvA
import Theorems.Thm_Formalism_GM_FockB_pairwiseA
import Theorems.Thm_Formalism_GM_FockB_goodA
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.GM.FockB
theorem _root_.solution : M.FockBlocks := by
  intro p _ N r _ D hB hr
  constructor
  · intro j j' jp jp' _ _ hne y hy y' hy' g hg g' hg'
    rw [ehat_eq D p j jp, ehat_eq D p j' jp', pall_eq, pall_eq]
    have hon : ∀ a ∈ LA D, jA D j jp a = jA D j' jp' a →
        oA D j jp a = oA D j' jp' a ∧ nA D j jp a = nA D j' jp' a := by
      intro a _ h
      rcases a with _ | i
      · simp only [jA, oA, nA, Option.elim] at h ⊢
        rw [h]; exact ⟨rfl, rfl⟩
      · simp only [jA, oA, nA, Option.elim] at h ⊢
        rw [deg_fst hB, deg_fst hB, deg_snd hB, deg_snd hB, h]; exact ⟨rfl, rfl⟩
    have hne' : ∃ a ∈ LA D, jA D j jp a ≠ jA D j' jp' a := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      apply hne
      have h0 : jp = jp' := hc none (List.mem_cons_self ..)
      have h1 : j = j' := funext fun i =>
        hc (some i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
      rw [h0, h1]
    exact chain_orth hr (oA D j jp) (nA D j jp) (jA D j jp) (oA D j' jp') (nA D j' jp') (jA D j' jp') (LA D)
      (fun a _ => tvA hB a) (pairwiseA hB) hon hne' _ (fun a _ => goodA hB j jp y hy g hg a) _
      (fun a _ => goodA hB j' jp' y' hy' g' hg' a)
  · intro j jp _ y hy y' hy' g hg g' hg'
    rw [ProjS.fockK_smul_left, ProjS.fockK_smul_right, ehat_eq D p j jp, pall_eq, pall_eq,
      chain_main hr (oA D j jp) (nA D j jp) (jA D j jp) (LA D) (fun a _ => tvA hB a) (pairwiseA hB) _
        (fun a _ => goodA hB j jp y hy g hg a) _ (fun a _ => goodA hB j jp y' hy' g' hg' a), phi_eq]
    have hcst : cst (r := r) (zzA D) (oA D j jp) (nA D j jp) (jA D j jp) (LA D) =
        ((jp.factorial : ℚ_[p]) ^ 2 * (∏ i, ((j i).factorial : ℚ_[p])) ^ 2) *
          ((∏ i, ((((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) +
                (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) + r + D.T.z i + 1 + j i - 1).choose (j i) *
              (D.T.z i).factorial : ℕ) : ℚ_[p])) *
            ((((D.LL.deg D.uPos - jp) + (D.B - jp) + r + D.zPlus + 1 + jp - 1).choose jp *
              D.zPlus.factorial : ℕ) : ℚ_[p])) := by
      simp only [cst, LA, List.map_cons, List.prod_cons, List.map_map]
      rw [← Fin.prod_univ_def]
      simp only [Function.comp_def, jA, oA, nA, zzA, Option.elim]
      push_cast
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [hcst]
    have hf1 : (∏ i, ((j i).factorial : ℚ_[p])) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hf2 : (jp.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
end Formalism.GM.FockB
