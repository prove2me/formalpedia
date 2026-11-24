-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.lemmaSOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:39:55.789934+00:00
-- url     : https://prove2.me/submissions/ce4c0e4a-9e5c-4bfb-8d90-ab0c9e8fbcd7

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_admissible_word_of_extension
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_len
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_lenN
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_exists_max_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution : LemmaSOfSteps := by
  intro h1 hU
  obtain ⟨Cu, hCu, hup⟩ := hU
  refine ⟨max (3 / π) Cu, lt_max_of_lt_right hCu, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5
  have hC2 : 0 ≤ max (3 / π) Cu := le_max_of_le_right hCu.le
  have hCL : 0 ≤ max (3 / π) Cu * Λ ^ 2 := by positivity
  intro b s hb hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro hbs h hh w hw hlen t ht
    rw [one_mul] at hlen
    obtain ⟨w', hw', hE⟩ := h1 Wp Wq P p nn F Y Λ K N hK (by linarith) hI2 hI3 (b - 1) (by omega) h hh w hw
      hlen t ht
    rw [show b - 1 + 1 = b + 1 - 1 by omega] at hE
    refine ⟨w', by rwa [one_mul], hE.trans ?_⟩
    have hE0 : 0 ≤ Ew p nn F (b - 1) w' h := hPos _ _ _ (admissible_word_of_extension hw hw') (isExt_lenN hw')
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hE0
  | succ s hs ih =>
    intro hbs h hh w hw hlen t ht
    have hlen' : w.length + K + s * K ≤ N := by rw [Nat.succ_mul] at hlen; omega
    have hself : IsExt P p.l0 Y N ((s + 1) * K) w w := isExt_self hw (by omega)
    obtain ⟨wm, hwm, hmax⟩ := exists_max_ext ((s + 1) * K) w (fun w' => Ew p nn F (b - 1) w' h) hself
    have hE0 : 0 ≤ Ew p nn F (b - 1) wm h := hPos _ _ _ (admissible_word_of_extension hw hwm) (isExt_lenN hwm)
    set Mb := (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h with hMbdef
    have hMb : ∀ w', IsExt P p.l0 Y N K w w' → ∀ t : ℂ, t ≠ 0 →
        Ew p nn F (b + (s + 1) - 2) w' (h ++ [(s + 1 - 1, t)]) ≤ Mb := by
      intro w' hw' t ht
      rw [show b + (s + 1) - 2 = b + s - 1 by omega, show s + 1 - 1 = s by omega]
      have hl' : w'.length + s * K ≤ N := by have := isExt_len hw'; omega
      obtain ⟨w'', hw'', hE⟩ := ih (by omega) h hh w' (admissible_word_of_extension hw hw') hl' t ht
      refine hE.trans (mul_le_mul_of_nonneg_left (hmax w'' ?_) (pow_nonneg hCL _))
      refine isExt_mono (isExt_trans hw' hw'') ?_
      rw [Nat.succ_mul]; omega
    have hup' := hup Wp Wq P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b (s + 1) hb (by omega) hbs h hh w hw
      (by omega) Mb hMb t ht
    refine ⟨wm, hwm, hup'.trans ?_⟩
    rw [hMbdef, pow_succ]
    have hX : 0 ≤ (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h := mul_nonneg (pow_nonneg hCL _) hE0
    have hc : Cu * Λ ^ 2 ≤ max (3 / π) Cu * Λ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    calc Cu * Λ ^ 2 * ((max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h)
        ≤ max (3 / π) Cu * Λ ^ 2 * ((max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h) :=
          mul_le_mul_of_nonneg_right hc hX
      _ = (max (3 / π) Cu * Λ ^ 2) ^ s * (max (3 / π) Cu * Λ ^ 2) * Ew p nn F (b - 1) wm h := by ring
end Formalism.FourierDecayAlt.P.TBBx1
