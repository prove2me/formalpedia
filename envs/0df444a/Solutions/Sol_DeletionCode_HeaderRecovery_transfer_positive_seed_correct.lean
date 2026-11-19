-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.transfer_positive_seed_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:27.08148+00:00
-- url     : https://prove2.me/submissions/5b280eb7-9167-45f2-b5b6-35748bb82323

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_HeaderRecovery_shorten_seed_correct
import Theorems.Thm_DeletionCode_HeaderRecovery_lengthen_seed_correct
import Theorems.Thm_DeletionCode_Windows_insert_delete


set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool)
    (hbit : long (editOffset k) = h.bit)
    (hseed : Agree (positivePath k h long) seed.offset seed.bits 0 k)
    (hextra : ExtensionMatches k h long seed extra) :
    Agree (negativePath k h long) (transferPositiveSeed k h seed extra).offset
      (transferPositiveSeed k h seed extra).bits 0 k := by
  cases ho : h.orientation with
  | deletion =>
    simp only [positivePath, ho] at hseed
    simp only [negativePath, transferPositiveSeed, ho]
    have hresult := lengthen_seed_correct (deleteAt long (editOffset k))
      (editOffset k) k seed h.bit hseed
    have hinv : insertAt (deleteAt long (editOffset k)) (editOffset k) h.bit = long := by
      rw [← hbit]
      exact insert_delete long (editOffset k)
    rw [hinv] at hresult
    exact hresult
  | insertion =>
    simp only [positivePath, ho] at hseed
    simp only [negativePath, transferPositiveSeed, ho]
    apply shorten_seed_correct long (editOffset k) k seed extra hseed
    simpa only [ExtensionMatches, ho, negativePath, true_implies] using hextra
end DeletionCode.HeaderRecovery
